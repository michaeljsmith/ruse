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
(ruse-global-rule 'null (quote '()))
(ruse-global-rule 'tag '(quote tag))
(ruse-global-rule '(tag @t1 @v) '(builtin list t1 v))
(ruse-global-rule 'multiply-int '(quote multiply-int))
(ruse-global-rule 'int '(quote int))
(ruse-global-rule '(int  @x) '(tag int x))
(ruse-global-rule '(multiply-int @x @y) '(int (builtin * x y)))

; Main evaluate function.
(define (ruse-eval expr env calls spos on-scs on-fail on-err)

	; Primary evaluation function.
	(define (eval expr env calls spos on-scs on-fail)
		(check-quote expr env calls spos on-scs on-fail))

	; Check whether expression is quoted, if so return the value.
	(define (check-quote expr env calls spos on-scs on-fail)
		(if (and (list? expr) (eqv? (car expr) 'quote))
			(on-scs (cadr expr) env calls spos)
			(check-quasiquote expr env calls spos on-scs on-fail)))

	; Check whether the expression is quasiquoted.
	(define (check-quasiquote expr env calls spos on-scs on-fail)
		(define (on-qq-fail)
			(expand-macros expr env calls spos on-scs on-fail))
		(if (and (list? expr) (eqv? (car expr) 'quasiquote))
			(ruse-eval-quasiquote expr env calls spos on-scs on-qq-fail on-err)
			(expand-macros expr env calls spos on-scs on-fail)))

	; Try to expand any macros before continuing.
	(define (expand-macros expr env calls spos on-scs on-fail)
		(define (on-mac-fail)
			(eval-base expr env calls spos on-scs on-fail))
		(ruse-expand-macros expr env calls spos on-scs on-mac-fail on-err))

	; Evaluate any core functions (eg builtin functions).
	(define (eval-base expr env calls spos on-scs on-fail)
		(define (on-base-fail)
			(expand-rules expr env calls spos on-scs on-fail))
		(ruse-eval-base expr env calls spos on-scs on-base-fail on-err))

	; Apply any rules that match the current expression.
	(define (expand-rules expr env calls spos on-scs on-fail)
		(define (on-expand-fail)
			(fail expr env calls spos on-scs on-fail))
		(ruse-expand-rules expr env calls spos on-scs on-expand-fail on-err))

	; I'm stumped.
	(define (fail expr env calls spos on-scs on-fail)
		(on-fail)
		(printf "Probably shouldn't get here.")
		(on-err (format "Unknown value type (~v)." expr) calls spos)
		(printf "Shouldn't get here (1).~n"))

	; Apply the function pipeline we have defined.
	(eval expr env calls spos on-scs on-fail))

; Call stack definitions.
(define (make-call-stack-frame tp rl bdngs) (list tp rl bdngs))
(define (with-call-stack-frame sf fn) (apply fn sf))

; Print out a callstack.
(define (ruse-print-call-stack calls)
	(let print-stack ((cur-calls calls))
		(unless (null? cur-calls) 
			(with-call-stack-frame
				(car cur-calls)
				(lambda (tp rl bdngs)
					(let* ((tmpl (car rl))
								 (ptn (car tmpl))
								 (body (cdr tmpl))
								 (hdr
									(cond
										((eqv? 'rule tp) 'rule)
										((eqv? 'macro tp) 'macro)
										(else (string->symbol (format "UNKNOWN FRAME TYPE(~a)" tp))))))
						(printf "~a (~a)\n" ptn hdr))))
			(print-stack (cdr cur-calls)))))

; Try to expand any macros before continuing.
(define (ruse-expand-macros expr env calls spos on-scs on-fail on-err)
	(define (on-mac-scs val mac-env mac-calls mac-spos)
		(ruse-eval val env mac-calls mac-spos on-scs on-fail on-err))
	(apply-env-macros-to-expr expr env calls spos on-mac-scs on-fail on-err))

; Apply any rules that match the current expression.
(define (ruse-expand-rules expr env calls spos on-scs on-fail on-err)
	(define (on-rule-fail)
		(on-fail))
	(define (on-rule-scs new-expr new-env new-calls new-spos)
		(define (on-rplc-eval-fail)
			(printf "Unable to evaluate replacement expression ~v~n" new-expr)
			(on-fail))
		(ruse-eval new-expr new-env new-calls new-spos on-scs on-rplc-eval-fail on-err))
	(cond
		((symbol? expr)
		 (apply-env-to-expr expr env calls spos on-rule-scs on-rule-fail on-err))
		((list? expr)
		 (begin
			 (let* ((sub-eval (lambda (sub)
													(let/cc
														return
														(define (on-eval val expr new-calls new-spos) (return val))
														(ruse-eval sub env calls spos on-eval on-rule-fail on-err))))
							(fm-exp (map sub-eval expr)))
				 (apply-env-to-expr fm-exp env calls spos on-rule-scs on-fail on-err))))
		(else (on-fail))))

(define (ruse-eval-base expr env calls spos on-scs on-fail on-err)
	; Check whether the expression is a rule definition.
	(cond
		; Handle requests to evaluate form as a scheme form.
		((and (list? expr) (eqv? (car expr) 'builtin))
		 (ruse-eval-builtin expr env calls spos on-scs on-fail on-err))
		; Handle requests to evaluate dynamic form.
		((and (list? expr) (eqv? (car expr) 'eval))
		 (ruse-eval-eval expr env calls spos on-scs on-fail on-err))
		((and (list? expr) (eqv? (car expr) 'scope))
		 (ruse-eval-scope expr env calls spos on-scs on-fail on-err))
		; Handle conditional requests.
		((and (list? expr) (eqv? (car expr) 'cond))
		 (ruse-eval-cond expr env calls spos on-scs on-fail on-err))
		; Handle rule definitions.
		((and (list? expr) (eqv? (car expr) '=))
		 (ruse-eval-rule-def expr env calls spos on-scs on-fail on-err))
		; Handle macro definitions.
		((and (list? expr) (eqv? (car expr) '=*))
		 (ruse-eval-macro-def expr env calls spos on-scs on-fail on-err))
		; Handle integer literals by returning them as is.
		((integer? expr) (on-scs expr env calls spos))
		; Handle string literals by returning them as is.
		((string? expr) (on-scs expr env calls spos))
		(else (on-fail))))

(define (ruse-eval-quasiquote expr env calls spos on-scs on-fail on-err)
	(define (recurse cur-expr)
		(define (on-unquote-fail) (on-err (format "Failed to unquote: ~v." expr) calls spos))
		(cond
			((and (list? cur-expr) (eqv? 'unquote (car cur-expr)))
			 (let/cc
				 return
				 (define (on-unquote-scs uq-val uq-env uq-calls uq-spos)
					 (return `(no-splice . ,uq-val)))
				 (ruse-eval (cadr cur-expr) env calls spos on-unquote-scs on-unquote-fail on-err)))
			((and (list? cur-expr) (eqv? 'unquote-splicing (car cur-expr)))
			 (let/cc
				 return
				 (define (on-unquote-scs uq-val uq-env uq-calls uq-spos)
					 (return `(splice . ,uq-val)))
				 (ruse-eval (cadr cur-expr) env calls spos on-unquote-scs on-unquote-fail on-err)))
			((list? cur-expr)
			 (cons
				 'no-splice
				 (let add-next ((pos cur-expr))
					 (if (null? pos)
						 null
						 (let ((arg (recurse (car pos))))
							 (if (eqv? 'splice (car arg))
								 (append (cdr arg) (add-next (cdr pos)))
								 (cons (cdr arg) (add-next (cdr pos)))))))))
			(else (cons 'no-splice cur-expr))))
	(let ((rslt (cdr (recurse (cadr expr)))))
		(on-scs rslt env calls spos)))

; Evaluate using Scheme.
(define-namespace-anchor ns-anchor)
(define eval-ns (namespace-anchor->namespace ns-anchor))
(define (ruse-eval-builtin expr env calls spos on-scs on-fail on-err)
	(let ((fm (cdr expr)))
		(define (eval-arg arg)
			(list
				'quote
				(let/cc
					arg-done
					(define (on-arg-fail) (on-err (format "Builtin eval failed to evaluate argument ~v." arg) calls spos))
					(define (on-arg-scs val new-env new-calls new-spos)
						(arg-done val))
					(ruse-eval arg env calls spos on-arg-scs on-arg-fail on-err))))
		(let* ((val-fm (map eval-arg (cdr fm)))
					 (bi-expr (cons (car fm) val-fm)))
			(let ((bi-rslt (eval bi-expr eval-ns)))
				(on-scs bi-rslt env calls spos)))))

; Evaluate dynamic form.
(define (ruse-eval-eval expr env calls spos on-scs on-fail on-err)
	(define (on-eval-arg-scs dyn-val dyn-env dyn-calls dyn-spos)
		(define (on-eval-fail) (on-err (format "Failed to eval dynamic form: ~v." dyn-val) dyn-calls dyn-spos))
		(ruse-eval dyn-val dyn-env calls spos
							 (lambda (nval nenv)
								 (on-scs nval nenv calls spos)) on-eval-fail on-err))
	(define (on-eval-arg-fail) (on-err (format "Failed to eval dynamic form argument: ~v" expr) calls spos))
	(let ((fm (cadr expr)))
		(ruse-eval fm env calls spos on-eval-arg-scs on-eval-arg-fail on-err)))

; Evaluate scope declaration.
(define (ruse-eval-scope expr env calls spos on-scs on-fail on-err)
	(define (on-scope-fail) (on-err (format "Failed to eval scope argument: ~v." expr) calls spos))
	(let ((fm (cadr expr))
				(scope-env (cons (make-scope-bdng (make-scope)) env)))
		(ruse-eval fm scope-env calls spos on-scs on-scope-fail on-err)))

; Evaluate conditional expression.
(define (ruse-eval-cond expr env calls spos on-scs on-fail on-err)
	(when (not (list? (cadr expr))) (on-err "cond arguments not list." calls spos))
	(let eval-cond ((cnd-pairs (cdr expr)))
		(if (null? cnd-pairs)
			(on-err "Cond has no cases." calls spos)
			(let* ((cnd-pair (car cnd-pairs))
						 (cnd (car cnd-pair))
						 (rslt (cadr cnd-pair)))
				(let/cc
					exit
					(define (on-rslt-fail) (on-err (format "Failed to eval cond result: ~v." rslt) calls spos))
					(define (on-cond-scs cnd-val cond-env cond-calls cond-spos)
						(if cnd-val
							(ruse-eval rslt env calls spos on-scs on-rslt-fail on-err)
							(eval-cond (cdr cnd-pairs)))
						(exit))
					(define (on-cond-fail) (on-err (format "Failed to eval cond test: ~v." cnd) calls spos))
					(if (eq? cnd 'else)
						(ruse-eval rslt env calls spos on-scs on-rslt-fail on-err)
						(ruse-eval cnd env calls spos on-cond-scs on-cond-fail on-err)))))))

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
	(cond
		((and (symbol? ptn) (ptn-is-var? ptn))
		 (match-var ptn val bdngs on-scs on-fail))
		((symbol? ptn)
		 (match-sym ptn val bdngs on-scs on-fail))
		((pair? ptn) (match-pair ptn val bdngs on-scs on-fail))
		((and (null? ptn) (null? val)) (on-scs bdngs))
		(else (on-fail))))

; Function taking a form (whose arguments have already been evaluated) and
; attempting to apply a specific rule to it.
(define (apply-rule rule expr env calls spos on-scs on-fail on-err)
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
							 (on-scs body new-env
											 (cons (make-call-stack-frame 'rule rule bdngs) calls) spos)))))
		; Using the handlers we have defined, attempt to match the pattern.
		(match-ptn ptn expr '() on-match-scs on-fail)))

; Function taking a form and attempting to apply a specific macro to it.
(define (apply-macro mac fm env calls spos on-scs on-fail on-err)
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
												 ((pair? sub-ptn)
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
							 (on-scs expnsn mac-env
											 (cons (make-call-stack-frame 'macro mac bdngs) calls) spos)))))
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
(define (apply-env-to-expr expr env calls spos on-scs on-fail on-err)
	(let recurse ((cur-env env))
		(cond
			; Have we tried every entry in the env?
			((null? cur-env) #f)
			; is the current entry a rule?
			((bdng-is-rule? (car cur-env))
			 ; Attempt to apply the rule to the expression. If it fails,
			 ; try the next one.
			 (apply-rule (bdng->rule (car cur-env)) expr env
									 calls spos on-scs
									 (lambda () (recurse (cdr cur-env)))
									 on-err))
			; Check whether the current entry is a sub-scope.
			((bdng-is-scope? (car cur-env))
			 (let ((sub-env (unbox (bdng->scope (car cur-env)))))
				 (recurse sub-env)
				 (recurse (cdr cur-env))))
			; If the env entry is not a rule, skip it.
			(else (recurse (cdr cur-env)))))

	; We found no matching rules, so we failed.
	(on-fail))

; Function taking an (unevaluated) expression and the current environment and applying
; all the macros in the current environment to the expression until one matches.
(define (apply-env-macros-to-expr expr env calls spos on-scs on-fail on-err)
	(let recurse ((cur-env env))
		(cond
			; Have we tried every entry in the env?
			((null? cur-env) #f)
			; Is the current entry a macro?
			((bdng-is-macro? (car cur-env))
			 ; Attempt to apply the macro to the expression. If it fails,
			 ; try the next one.
			 (apply-macro (bdng->rule (car cur-env)) expr env
										calls spos on-scs
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
(define (ruse-add-to-current-scope bdng env calls spos on-err)
	(let* ((top-env (car env))
				 (top-scope
					 (begin
						 (unless (bdng-is-scope? top-env)
							 (on-err (format
												 (string-append
													 "Declaration (~v) failed: "
													 "top binding is not scope.")
												 (cadr bdng)) calls spos))
						 (bdng->scope top-env))))
		(set-box! top-scope (cons bdng (unbox top-scope)))))

; Evaluate a rule definition (add it to the environment).
(define (ruse-eval-rule-def expr env calls spos on-scs on-fail on-err)
	(let ((rl-tpl (compile-rule-def (cdr expr))))
		(if rl-tpl
			(let ((rl (cons rl-tpl env)))
				(ruse-add-to-current-scope (cons 'rule rl) env calls spos on-err)
				(on-scs 'rule-def env calls spos))
			(on-fail))))

; Evaluate a macro definition (add it to the environment).
(define (ruse-eval-macro-def expr env calls spos on-scs on-fail on-err)
	(let ((mac-tpl (compile-macro-def (cdr expr))))
		(if mac-tpl
			(let ((mac (cons mac-tpl env)))
				(ruse-add-to-current-scope (cons 'macro mac) env calls spos on-err)
				(on-scs 'mac-def env calls spos))
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
						(define (on-eval-scs val new-env calls spos)
							(set! rslt val)
							(set! file-env new-env)
							(skip-current-data))
						(define (on-eval-fail)
							(set! rslt (void))
							(set! errors (+ 1 errors))
							(printf "Unable to evaluate form: ~v~n" fm)
							(skip-current-data))
						(define (on-eval-err msg calls spos)
							(set! rslt (void))
							(set! errors (+ 1 errors))
							(printf "Error while evaluating form: ~v~n  Message: ~a~n~n" fm msg)
							(ruse-print-call-stack calls)
							(printf "~n")
							(skip-current-data))
						(set! fm (read p))
						(unless (eof-object? fm)
							(begin
								(ruse-eval fm file-env null '("FILENAME" (1 1)) on-eval-scs on-eval-fail on-eval-err)
								(printf "Shouldn't get here (2).~n"))))
					(unless (eof-object? fm)
						(read-next-data))))
			(if (> errors 0)
				(on-err (format "File contained errors (~v)." errors))
				(on-scs rslt file-env)))

		; Push a top-level scope onto the environment stack.
		(set! file-env (cons (make-scope-bdng (make-scope)) file-env))
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
			(printf "~a~n" msg))
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
