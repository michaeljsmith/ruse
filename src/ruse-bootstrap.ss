#! /usr/bin/env mzscheme

;--------------------------------------------------------------------------------
;
;  Scheme implementation of Ruse, a simple interpreted language based on
;  substitution rules. Evaluating an expression involves checking the
;  expression against a database of rules. Each rule specifies a pattern
;  that must be matched, and an expression specifying the result if the
;  match is made. Pattern matching can involve binding parts of the
;  expression to variable names, which can be referred to in the result
;
;  Tested under:
;  MzScheme v4.1.5 (Ubuntu Linux 9.10)
;
;
;  Copyright (c) 2010 Michael Smith <msmith@msmith.id.au>
;
;  http://github.com/michaeljsmith/ruse
;
;  Permission is hereby granted, free of charge, to any person obtaining a copy
;  of this software and associated documentation files (the "Software"), to
;  deal in the Software without restriction, including without limitation the
;  rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
;  sell copies of the Software, and to permit persons to whom the Software is
;  furnished to do so, subject to the following conditions:
;  
;  The above copyright notice and this permission notice shall be included in
;  all copies or substantial portions of the Software.
;  
;  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
;  IN THE SOFTWARE.
;
;--------------------------------------------------------------------------------

#lang scheme

(require srfi/42)

; Declare some helpers for initializing the environment.
(define (ruse-global-env bdng)
	(set! global-env (cons bdng global-env)))
(define (ruse-global-rule ptn bd)
	(ruse-global-env `(rule (,ptn . ,bd) . ,global-env)))
(define (ruse-global-macro ptn bd)
	(ruse-global-env `(macro (,ptn . ,bd) . ,global-env)))

; Initialize the environment.
(define global-env '())
(ruse-global-rule 'tag '(quote tag))
(ruse-global-rule '(tag @t @v) '(builtin list t v))
(ruse-global-rule 'multiply-int '(quote multiply-int))
(ruse-global-rule 'int '(quote int))
(ruse-global-rule '(int  @x) '(tag int x))
(ruse-global-rule '(multiply-int @x @y) '(int (builtin * x y)))

; Main evaluate function.
(define (ruse-eval expr env on-scs on-fail on-err)

	; Primary evaluation function.
	(define (eval expr env on-scs on-fail)
		(check-quote expr env on-scs on-fail))

	; Check whether expression is quoted, if so return the value.
	(define (check-quote expr env on-scs on-fail)
		(if (and (list? expr) (eqv? (car expr) 'quote))
			(on-scs (cadr expr) env)
			(check-quasiquote expr env on-scs on-fail)))

	; Check whether the expression is quasiquoted.
	(define (check-quasiquote expr env on-scs on-fail)
		(define (on-qq-fail)
			(expand-macros expr env on-scs on-fail))
		(if (and (list? expr) (eqv? (car expr) 'quasiquote))
			(ruse-eval-quasiquote expr env on-scs on-qq-fail on-err)
			(expand-macros expr env on-scs on-fail)))

	; Try to expand any macros before continuing.
	(define (expand-macros expr env on-scs on-fail)
		(define (on-mac-scs val mac-env)
			(eval val env on-scs on-fail))
		(define (on-mac-fail)
			(eval-base expr env on-scs on-fail))
		(apply-env-macros-to-expr expr env on-mac-scs on-mac-fail on-err))

	; Evalute any core functions (eg builtin functions).
	(define (eval-base expr env on-scs on-fail)
		(define (on-base-fail)
			(expand-rules expr env on-scs on-fail))
		(ruse-eval-base expr env on-scs on-base-fail on-err))

	; Apply any rules that match the current expression.
	(define (expand-rules expr env on-scs on-fail)
		(define (on-rule-fail)
			(fail expr env on-scs on-fail))
		(define (on-rule-scs new-expr new-env)
			(define (on-rplc-eval-fail)
				(printf "Unable to evaluate replacement expression ~v~n" new-expr)
				(on-fail))
			(eval new-expr new-env on-scs on-rplc-eval-fail))
		(printf "eval-base ~v~n" expr)
		(cond
			((symbol? expr)
			 (apply-env-to-expr expr env on-rule-scs on-rule-fail on-err))
			((list? expr)
			 (begin
				 (let* ((sub-eval (lambda (sub)
														(let/cc
															return
															(define (on-eval val expr) (return val))
															(eval sub env on-eval on-rule-fail))))
								(fm-exp (map sub-eval expr)))
					 (apply-env-to-expr fm-exp env on-rule-scs on-fail on-err))))
			(else (fail expr env on-scs on-fail))))

	; I'm stumped.
	(define (fail expr env on-scs on-fail)
		(on-err (format "Unknown value type (~v)." expr))
		(printf "Shouldn't get here (1).~n"))

	; Apply the function pipeline we have defined.
	(eval expr env on-scs on-fail))

(define (ruse-eval-base expr env on-scs on-fail on-err)
	; Check whether the expression is a rule definition.
	(cond
		; Handle requests to evaluate form as a scheme form.
		((and (list? expr) (eqv? (car expr) 'builtin))
		 (ruse-eval-builtin expr env on-scs on-fail on-err))
		; Handle requests to evaluate dynamic form.
		((and (list? expr) (eqv? (car expr) 'eval))
		 (ruse-eval-eval expr env on-scs on-fail on-err))
		((and (list? expr) (eqv? (car expr) 'scope))
		 (ruse-eval-scope expr env on-scs on-fail on-err))
		; Handle conditional requests.
		((and (list? expr) (eqv? (car expr) 'cond))
		 (ruse-eval-cond expr env on-scs on-fail on-err))
		; Handle rule definitions.
		((and (list? expr) (eqv? (car expr) '=))
		 (ruse-eval-rule-def expr env on-scs on-fail on-err))
		; Handle macro definitions.
		((and (list? expr) (eqv? (car expr) '=*))
		 (ruse-eval-macro-def expr env on-scs on-fail on-err))
		; Handle integer literals by returning them as is.
		((integer? expr) (on-scs expr env))
		; Handle string literals by returning them as is.
		((string? expr) (on-scs expr env))
		(else (on-fail))))

(define (ruse-eval-quasiquote expr env on-scs on-fail on-err)
	(define (recurse cur-expr)
		(cond
			((and (list? cur-expr) (eqv? 'unquote (car cur-expr)))
			 (ruse-eval (cadr cur-expr) env on-scs on-fail on-err))
			((list? cur-expr) (map recurse cur-expr))
			(else cur-expr)))
	(on-scs (recurse (cadr expr))))

; Evaluate using Scheme.
(define-namespace-anchor ns-anchor)
(define eval-ns (namespace-anchor->namespace ns-anchor))
(define (ruse-eval-builtin expr env on-scs on-fail on-err)
	(let ((fm (cdr expr)))
		(define (eval-arg arg)
			(define (on-arg-fail) (on-err (format "Builtin eval failed to evaluate argument ~v." arg)))
			(let ((rslt #f))
				(define (on-arg-scs val new-env) (set! rslt val))
				(ruse-eval arg env on-arg-scs on-arg-fail on-err)
				(list 'quote rslt)))
		(let* ((val-fm (map eval-arg (cdr fm)))
					 (bi-expr (cons (car fm) val-fm)))
			(let ((bi-rslt (eval bi-expr eval-ns)))
				(on-scs bi-rslt env)))))

; Evaluate dynamic form.
(define (ruse-eval-eval expr env on-scs on-fail on-err)
	(let ((fm (cadr expr)))
		(ruse-eval fm env on-scs on-fail on-err)))

; Evaluate scope declaration.
(define (ruse-eval-scope expr env on-scs on-fail on-err)
	(let ((fm (cadr expr))
				(scope-env (cons (make-scope-bdng (make-scope)) env)))
		(ruse-eval fm scope-env on-scs on-fail on-err)))

; Apply the current environment to the form.
(define (ruse-eval-apply-rules expr env on-scs on-fail on-err)
	(let ((fm (cdr expr)))
		(cond
			((symbol? fm)
			 (apply-env-to-expr fm env on-scs on-fail on-err))
			((list? fm)
			 (apply-env-to-expr fm env on-scs on-fail on-err))
			(else (on-fail)))))

; Evaluate conditional expression.
(define (ruse-eval-cond expr env on-scs on-fail on-err)
	(when (not (list? (cadr expr))) (on-err "cond arguments not list."))
	(let eval-cond ((cnd-pairs (cdr expr)))
		(if (null? cnd-pairs)
			(on-fail)
			(let* ((cnd-pair (car cnd-pairs))
						 (cnd (car cnd-pair))
						 (rslt (cadr cnd-pair)))
				(define (on-cond-scs cnd-val cond-env)
					(if cnd-val
						(ruse-eval rslt env (lambda (nval nenv) (on-scs nval nenv)) on-fail on-err)
						(eval-cond (cdr cnd-pairs))))
				(if (eq? cnd 'else)
					(ruse-eval rslt env on-scs on-fail on-err)
					(ruse-eval cnd env on-cond-scs (lambda () (eval-cond (cdr cnd-pairs))) on-err))))))

; Pattern matching.
(define (ptn-is-var? ptn)
	(eqv? #\@ (string-ref (symbol->string ptn) 0)))
(define (ptn->var-name ptn)
	(string->symbol (substring (symbol->string ptn) 1)))
(define (match-sym ptn val bdngs on-scs on-fail)
	(if (eqv? ptn val)
		(on-scs bdngs)
		(on-fail)))
(define (match-var ptn val bdngs on-scs on-fail)
	(on-scs (cons (cons (ptn->var-name ptn) val) bdngs)))
(define (match-pair ptn val bdngs on-scs on-fail)
	(if (pair? val)
		(let ((sub-on-scs
						(lambda (new-bdngs)
							(match-ptn (cdr ptn) (cdr val) new-bdngs on-scs on-fail))))
			(match-ptn (car ptn) (car val) bdngs sub-on-scs on-fail))
		(on-fail)))
(define (match-ptn ptn val bdngs on-scs on-fail)
	(printf "match-ptn:~n  ptn=~v~n  val=~v~n" ptn val)
	(cond
		((and (symbol? ptn) (ptn-is-var? ptn)) (match-var ptn val bdngs on-scs on-fail))
		((symbol? ptn) (match-sym ptn val bdngs on-scs on-fail))
		((pair? ptn) (match-pair ptn val bdngs on-scs on-fail))
		((and (null? ptn) (null? val)) (on-scs bdngs))
		(else (on-fail))))

; Function taking a form (whose arguments have already been evaluated) and
; attempting to apply a specific rule to it.
(define (apply-rule rule expr env on-scs on-fail on-err)
	; Extract the pattern and the body from the rule.
	(let* ((templ (car rule))
				 (rl-env (cdr rule))
				 (ptn (car templ))
				 (body (cdr templ))
				 (on-match-scs
					 (lambda (bdngs)
						 (let ((new-env rl-env))
							 ; Add all the bindings from the match to the environment.
							 (do-ec (: bdng bdngs)
											(set! new-env (cons `(rule (,(car bdng) . (quote ,(cdr bdng))) ()) new-env)))
							 (on-scs body new-env)))))
		; Using the handlers we have defined, attempt to match the pattern.
		(match-ptn ptn expr '() on-match-scs on-fail)))

; Function taking a form and attempting to apply a specific macro to it.
(define (apply-macro mac fm env on-scs on-fail on-err)
	; Extract the pattern and the body from the rule.
	(let* ((templ (car mac))
				 (mac-env (cdr mac))
				 (ptn (car templ))
				 (body (cdr templ))
				 (on-match-scs
					 (lambda (bdngs)
						 ; Perform a typographical replacement of all variables mentioned
						 ; in the pattern in the body of the macro.
						 (let ((expnsn 
										 (let recurse-pattern ((sub-ptn body))
											 (cond
												 ((null? sub-ptn)
													sub-ptn)
												 ((list? sub-ptn)
													(cons (recurse-pattern (car sub-ptn)) (recurse-pattern (cdr sub-ptn))))
												 ((symbol? sub-ptn)
													(let check-bindings ((cur-bdngs bdngs))
														(if (null? cur-bdngs)
															sub-ptn
															(let* ((bdng (car cur-bdngs))
																		 (bdng-sym (car bdng))
																		 (bdng-rplc (cdr bdng)))
																(if (eq? sub-ptn bdng-sym)
																	bdng-rplc
																	(check-bindings (cdr cur-bdngs)))))))
												 (else sub-ptn)))))
							 (on-scs expnsn mac-env)))))
		; Using the handlers we have defined, attempt to match the pattern.
		(match-ptn ptn fm '() on-match-scs on-fail)))

(define (make-scope) (box null))
(define (make-scope-bdng scope) (cons 'scope scope))

; Accessor functions for bindings.
(define (bdng-is-rule? bdng) (eq? 'rule (car bdng)))
(define (bdng->rule bdng) (cdr bdng))
(define (bdng-is-macro? bdng) (eq? 'macro (car bdng)))
(define (bdng->macro bdng) (cdr bdng))
(define (bdng-is-scope? bdng) (eq? 'scope (car bdng)))
(define (bdng->scope bdng) (cdr bdng))

; Function taking an expression and the current environment and applying
; all the bindings to the expression until one matches.
(define (apply-env-to-expr expr env on-scs on-fail on-err)
	(let recurse ((cur-env env))
		(cond
			; Have we tried every entry in the env?
			((null? cur-env) #f)
			; is the current entry a rule?
			((bdng-is-rule? (car cur-env))
			 ; Attempt to apply the rule to the expression. If it fails,
			 ; try the next one.
			 (apply-rule (bdng->rule (car cur-env)) expr env
									 on-scs
									 (lambda () (recurse (cdr cur-env)))
									 on-err))
			; Check whether the current entry is a sub-scope.
			((bdng-is-scope? (car cur-env))
			 (let ((sub-env (unbox (bdng->scope (car cur-env)))))
				 (recurse sub-env)
				 (printf "Recursing to next scope: ~v~n" (cdr cur-env))
				 (recurse (cdr cur-env))))
			; If the env entry is not a rule, skip it.
			(else (recurse (cdr cur-env)))))

	; We found no matching rules, so we failed.
	(on-fail))

; Function taking an (unevaluated) expression and the current environment and applying
; all the macros in the current environment to the expression until one matches.
(define (apply-env-macros-to-expr expr env on-scs on-fail on-err)
	(let recurse ((cur-env env))
		(cond
			; Have we tried every entry in the env?
			((null? cur-env) #f)
			; Is the current entry a macro?
			((bdng-is-macro? (car cur-env))
			 ; Attempt to apply the macro to the expression. If it fails,
			 ; try the next one.
			 (apply-macro (bdng->rule (car cur-env)) expr env
										on-scs
										(lambda () (recurse (cdr cur-env)))
										on-err))
			; Check whether the current entry is a sub-scope.
			((bdng-is-scope? (car cur-env))
			 (let ((sub-env (unbox (bdng->scope (car cur-env)))))
				 (recurse sub-env)
				 (recurse (cdr cur-env))))
			; If the env entry is not a macro, skip it.
			(else (recurse (cdr cur-env)))))

	; We found no matching macros, so we failed.
	(on-fail))

; Compile a rule definition into an internal format.
(define (compile-rule-def rl)
	; Function for converting the pattern.
	(define (compile-pattern ptn)
		(let recurse ((fm ptn))
			(cond
				; Handle symbols.
				((symbol? fm) fm)
				; Handle forms.
				((list? fm) (list-ec (: x fm) (recurse x)))
				((pair? fm) (cons (recurse (car fm)) (recurse (cdr fm))))
				((integer? fm) fm)
				((string? fm) fm))))
	(define (compile-body bd)
		(let recurse ((fm bd))
			(cond
				; Handle symbols.
				((symbol? fm) fm)
				; Handle forms.
				((list? fm) (list-ec (: x fm) (recurse x)))
				((pair? fm) (cons (recurse (car fm)) (recurse (cdr fm))))
				((integer? fm) fm)
				((string? fm) fm))))
	; Return a pair consisting of the compiled pattern and the compiled body.
	(cons (compile-pattern (car rl)) (compile-body (cadr rl))))

; Compile a macro definition into an internal format.
(define (compile-macro-def mac)
	; Function for converting the pattern.
	(define (compile-pattern ptn)
		(let recurse ((fm ptn))
			(cond
				; Handle symbols.
				((symbol? fm) fm)
				; Handle forms.
				((list? fm) (list-ec (: x fm) (recurse x)))
				((pair? fm) (cons (recurse (car fm)) (recurse (cdr fm))))
				((integer? fm) fm)
				((string? fm) fm))))
	(define (compile-body bd)
		(let recurse ((fm bd))
			(cond
				; Handle symbols.
				((symbol? fm) fm)
				; Handle forms.
				((list? fm) (list-ec (: x fm) (recurse x)))
				((pair? fm) (cons (recurse (car fm)) (recurse (cdr fm))))
				((integer? fm) fm)
				((string? fm) fm))))
	; Return a pair consisting of the compiled pattern and the compiled body.
	(cons (compile-pattern (car mac)) (compile-body (cadr mac))))

; Modify the current scope (the top of the environment stack) to
; include a new definition.
(define (ruse-add-to-current-scope bdng env on-err)
	(let* ((top-env (car env))
				 (top-scope
					 (begin
						 (unless (bdng-is-scope? top-env)
							 (on-err (format
												 (string-append
													 "Declaration (~v) failed: "
													 "top binding is not scope.")
												 (cadr bdng))))
						 (bdng->scope top-env))))
		(printf "    top-env = ~v~n    top-scope = ~v\n" top-env top-scope)
		(set-box! top-scope (cons bdng (unbox top-scope)))))

; Evaluate a rule definition (add it to the environment).
(define (ruse-eval-rule-def expr env on-scs on-fail on-err)
	(printf "ruse-eval-rule-def ~v~n" expr)
	(let ((rl-tpl (compile-rule-def (cdr expr))))
		(printf "  compiled: ~v~n" rl-tpl)
		(if rl-tpl
			(let ((rl (cons rl-tpl env)))
				(ruse-add-to-current-scope (cons 'rule rl) env on-err)
				(on-scs 'rule-def env))
			(on-fail))))

; Evaluate a macro definition (add it to the environment).
(define (ruse-eval-macro-def expr env on-scs on-fail on-err)
	(let ((mac-tpl (compile-macro-def (cdr expr))))
		(if mac-tpl
			(let ((mac (cons mac-tpl env)))
				(ruse-add-to-current-scope (cons 'macro mac) env on-err)
				(on-scs 'mac-def env))
			(on-fail))))

; Execute a given file.
(define (ruse-load-file f env on-scs on-err)
	(let ((rslt (void))
				(errors 0)
				(file-env env))
		(define (load-from-port p)
			(let read-next-data ()
				(let ((fm null))
					(let/cc
						skip-current-data
						(define (on-eval-scs val new-env)
							(set! rslt val)
							(set! file-env new-env)
							(skip-current-data))
						(define (on-eval-fail)
							(set! rslt (void))
							(set! errors (+ 1 errors))
							(printf "Unable to evaluate form: ~v~n" fm)
							(skip-current-data))
						(define (on-eval-err msg)
							(set! rslt (void))
							(set! errors (+ 1 errors))
							(printf "Error while evaluating form: ~v~n  Message: ~a~n" fm msg)
							(skip-current-data))
						(set! fm (read p))
						(unless (eof-object? fm)
							(begin
								(ruse-eval fm file-env on-eval-scs on-eval-fail on-eval-err)
								(printf "Shouldn't get here (2).~n"))))
					(unless (eof-object? fm)
						(read-next-data))))
			(if (> errors 0)
				(on-err (format "File contained errors (~v)." errors))
				(on-scs rslt file-env)))

		; Push a top-level scope onto the environment stack.
		(set! file-env (cons (make-scope-bdng (make-scope)) file-env))
		(printf "ruse-load-file: env = ~v~n" file-env)
		(call-with-input-file f load-from-port)))

; Top level file execution function.
(define (ruse-load-files fs)
	(define (load-files env on-scs on-err)
		(let ((rslt (void)))
			(let read-next-file ((f-tl fs))
				(define (on-file-scs val new-env)
					(set! rslt val)
					(read-next-file (cdr f-tl)))
				(if (null? f-tl)
					(on-scs rslt env)
					(ruse-load-file (car f-tl) env on-file-scs on-err)))))
	(let ((rslt (void)))
		(define (on-scs val env)
			(set! rslt val))
		(define (on-err msg)
			(printf "Error: ~v~n" msg))
		(load-files global-env on-scs on-err)
		rslt))

; Parse the command line options passed to the program.
(define (parse-command-line argv on-scs on-err)
	(let ((input-files '()))
		; Main parse function.
		(define (parse args-left)
			(unless (null? args-left)
				(let ((arg (car args-left))
							(tail (cdr args-left)))
					(cond
						((eqv? #\- (string-ref arg 0)) (parse-option arg tail))
						(else (parse-input-file arg tail))))))
		; Parse options (currently no options are supported).
		(define (parse-option arg tail)
			(on-err (format "Unknown option \"~v\"" arg))
			(parse tail))
		; Parse input specification.
		(define (parse-input-file arg tail)
			(set! input-files (append input-files (list arg)))
			(parse tail))
		; Parse the complete command line.
		(parse argv)
		(on-scs input-files)))

; Main program function.
(define (main argv)
	(let ((in-files '())
				(should-run #t))
		(define (on-scs fs)
			(set! in-files fs))
		(define (on-err msg)
			(printf "Error in command line: ~v~n" msg)
			(set! should-run #f))
		(parse-command-line argv on-scs on-err)
		(when (null? in-files)
			(begin
				(set! should-run #f)
				(printf "No input files specified.~n")))
		(when should-run
			(ruse-load-files in-files))))

; Run program - pass command line to main function.
(let ((argv (vector->list (current-command-line-arguments))))
	(main argv))
