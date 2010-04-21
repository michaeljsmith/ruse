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
(require scheme/string)

; Declare some helpers for initializing the environment.
(define (ruse-global-env bdng)
	(set! global-env (cons bdng global-env)))
(define (ruse-global-rule ptn bd)
	(ruse-global-env `(rule (,ptn . ,bd) ,global-env (<builtin> 1 1) ())))
(define (ruse-global-macro ptn bd)
	(ruse-global-env `(macro (,ptn . ,bd) ,global-env (<builtin> 1 1) ())))

; Initialize the environment.
(define global-env '())
(ruse-global-rule 'null (quote '()))

; Source file definitions.
(define (source? x) (and (vector? x) (eqv? (vector-ref x 0) '*source)))
(define (source-form src) (vector-ref src 4))
(define (source-file src) (vector-ref src 1))
(define (source-line src) (vector-ref src 2))
(define (source-column src) (vector-ref src 3))
(define (source fm fl ln col) (vector '*source fl ln col fm))

(define (source->datum src)
	(let recurse ((cur src))
		(cond
			((null? cur) cur)
			((source? cur)
			 (recurse (source-form cur)))
			((pair? cur) (cons (recurse (car cur)) (recurse (cdr cur))))
			((or (string? cur) (integer? cur) (symbol? cur)) cur)
			(else (car car)))))
	
(define (syntax->source stx)
	(when (source? stx) (car car))
	(let recurse ((cur stx))
		(cond
			((null? cur) cur)
			((syntax? cur)
			 (source (recurse (syntax-e cur)) (syntax-source cur) (syntax-line cur) (syntax-column cur)))
			((pair? cur) (cons (recurse (car cur)) (recurse (cdr cur))))
			((or (string? cur) (integer? cur) (symbol? cur)) cur)
			(else (car car)))))

; Main evaluate function.
(define (ruse-eval expr env calls spos on-scs on-err)

	; Primary evaluation function.
	(define (eval expr env calls spos on-scs)
		(let ((hdr
						(cond
							((not (list? expr)) (void))
							((source? (car expr)) (source-form (car expr)))
							(else (car expr)))))
			(check-source hdr expr env calls spos on-scs)))

	(define (check-source hdr expr env calls spos on-scs)
		(if (source? expr)
			(ruse-eval-source expr env calls spos on-scs on-err)
			(check-quote hdr expr env calls spos on-scs)))

	; Check whether expression is quoted, if so return the value.
	(define (check-quote hdr expr env calls spos on-scs)
		(if (eqv? hdr 'quote)
			(let* ((quote-stx (cadr expr))
						 (val (if (source? quote-stx) (source->datum quote-stx) quote-stx)))
				(on-scs val env calls spos))
			(check-quasiquote hdr expr env calls spos on-scs)))

	; Check whether the expression is quasiquoted.
	(define (check-quasiquote hdr expr env calls spos on-scs)
		(define (on-qq-fail fcalls fspos)
			(expand-macros hdr expr env calls spos on-scs))
		(if (eqv? hdr 'quasiquote)
			(ruse-eval-quasiquote expr env calls spos on-scs on-qq-fail on-err)
			(expand-macros hdr expr env calls spos on-scs)))

	; Try to expand any macros before continuing.
	(define (expand-macros hdr expr env calls spos on-scs)
		(define (on-mac-fail fcalls fspos)
			(eval-base hdr expr env calls spos on-scs))
		(ruse-expand-macros expr env calls spos on-scs on-mac-fail on-err))

	; Evaluate any core functions (eg builtin functions).
	(define (eval-base hdr expr env calls spos on-scs)
		(define (on-base-fail fcalls fspos)
			(expand-rules hdr expr env calls spos on-scs))
		(ruse-eval-base expr env calls spos on-scs on-base-fail on-err))

	; Apply any rules that match the current expression. This function will
	; error if it fails.
	(define (expand-rules hdr expr env calls spos on-scs)
		(ruse-expand-rules expr env calls spos on-scs on-err))

	; Apply the function pipeline we have defined.
	(eval expr env calls spos on-scs))

; Call stack definitions.
(define (make-call-stack-frame tp spos rl bdngs) (list tp spos rl bdngs))
(define (with-call-stack-frame sf fn) (apply fn sf))

(define (compact-format-form src-fm)
	(let ((fm (source->datum src-fm)))
		(let*
			((max-depth
				 (let recurse ((cur-fm fm))
					 (cond
						 ((null? cur-fm) 0)
						 ((list? cur-fm) (+ 1 (foldl max 0 (map recurse cur-fm))))
						 ((pair? cur-fm) (max (recurse (car cur-fm)) (recurse (cdr cur-fm))))
						 (else 0)))))
			(let try-limit ((limit-depth (max 0)))
				(if (> limit-depth max-depth)
					null
					(let
						((cur-val
							 (let recurse ((cur-fm fm) (cur-depth 0))
								 (cond
									 ((null? cur-fm) "()")
									 ((list? cur-fm)
										(if (>= cur-depth limit-depth)
											"(..)"
											(string-append
												"("
												(foldl (lambda (a b) (string-join (list b a) " ")) (recurse (car cur-fm) (+ 1 cur-depth))
															 (map (lambda (x) (recurse x (+ 1 cur-depth))) (cdr cur-fm)))
												")")))
									 ((pair? cur-fm)
										(if (>= cur-depth limit-depth)
											"(.)"
											(string-append
												"("
												(string-join (list (recurse (car cur-fm) (+ 1 cur-depth))
																					 (recurse (cdr cur-fm) (+ 1 cur-depth))) " . ")
												")")))
									 (else (format "~v" cur-fm))))))
						(if (or (null? cur-val) (< (string-length cur-val) 77))
							(let ((next (try-limit (+ 1 limit-depth))))
								(if (or (null? next) (< (string-length next) (string-length cur-val)))
									cur-val next))
							null)))))))

; Print out a callstack.
(define (ruse-print-call-stack calls spos)
	(let print-stack ((cur-calls calls)
										(prev-spos spos))
		(if (null? cur-calls) 
			(let ((file (car prev-spos))
						(line (caadr prev-spos))
						(col (cadadr prev-spos))
						(form (caddr prev-spos)))
				(printf "<top level>:~n")
				(printf "    ~a(~a,~a): ~a~n" file line col (compact-format-form form)))
			(with-call-stack-frame
				(car cur-calls)
				(lambda (tp spos rl bdngs)
					(let* ((tmpl (car rl))
								 (rl-spos (caddr rl))
								 (file (car prev-spos))
								 (line (caadr prev-spos))
								 (col (cadadr prev-spos))
								 (form (caddr prev-spos))
								 (ptn (car tmpl))
								 (body (cdr tmpl))
								 (hdr
									(cond
										((eqv? 'rule tp) 'rule)
										((eqv? 'macro tp) 'macro)
										(else (string->symbol (format "UNKNOWN FRAME TYPE(~a)" tp))))))
						(printf "In ~a ~a:\n" hdr ptn)
						(for-each
							(lambda (bdng)
								(printf "    ~a = ~a~n" (car bdng) (compact-format-form (cdr bdng))))
							bdngs)
						(printf "    ~a(~a,~a): ~a~n" file line col (compact-format-form form)))
					(print-stack (cdr cur-calls) spos))))))

; Try to expand any macros before continuing.
(define (ruse-expand-macros expr env calls spos on-scs on-fail on-err)
	(define (on-mac-scs val mac-env mac-calls mac-spos)
		(ruse-eval val env mac-calls mac-spos on-scs on-err))
	(apply-env-macros-to-expr expr env calls spos on-mac-scs on-fail on-err))

; Apply any rules that match the current expression.
(define (ruse-expand-rules expr env calls spos on-scs on-err)
	(define (on-rule-scs new-expr new-env new-calls new-spos)
		(ruse-eval new-expr new-env new-calls new-spos on-scs on-err))
	(cond
		((symbol? expr)
		 (let ((on-expand-sym-fail
						 (lambda (fcalls fspos)
							 (on-err (format "Unable to evaluate expression: ~v" (source->datum expr)) fcalls fspos))))
			 (apply-env-to-expr expr env calls spos on-rule-scs on-expand-sym-fail on-err)))
		((list? expr)
		 (begin
			 (let* ((sub-eval (lambda (sub)
													(let/cc
														return
														(define (on-eval val env new-calls new-spos) (return val))
														(ruse-eval sub env calls spos on-eval on-err))))
							(fm-exp (map sub-eval expr)))
				 (define (on-expand-form-fail fcalls fspos)
					 (on-err (format "Unable to evaluate expression: ~v" (source->datum fm-exp)) fcalls fspos))
				 (apply-env-to-expr fm-exp env calls spos on-rule-scs on-expand-form-fail on-err))))
		(else (on-err ("Unable to evaluate expression: ~v")))))

(define (ruse-eval-base expr env calls spos on-scs on-fail on-err)
	(let ((hdr
					(cond
						((not (list? expr)) (void))
						((source? (car expr)) (source-form (car expr)))
						(else (car expr)))))
		; Check whether the expression is a rule definition.
		(cond
			; Handle requests to evaluate form as a scheme form.
			((eqv? hdr 'builtin)
			 (ruse-eval-builtin expr env calls spos on-scs on-fail on-err))
			; Handle requests to evaluate dynamic form.
			((eqv? hdr 'eval)
			 (ruse-eval-eval expr env calls spos on-scs on-fail on-err))
			; Handle requests to evaluate in a sub-scope.
			((eqv? hdr 'scope)
			 (ruse-eval-scope expr env calls spos on-scs on-fail on-err))
			; Handle conditional requests.
			((eqv? hdr 'cond)
			 (ruse-eval-cond expr env calls spos on-scs on-fail on-err))
			; Handle rule definitions.
			((eqv? hdr '=)
			 (ruse-eval-rule-def expr env calls spos on-scs on-fail on-err))
			; Handle macro definitions.
			((eqv? hdr '=*)
			 (ruse-eval-macro-def expr env calls spos on-scs on-fail on-err))
			; Handle integer literals by returning them as is.
			((integer? expr) (on-scs expr env calls spos))
			; Handle string literals by returning them as is.
			((string? expr) (on-scs expr env calls spos))
			(else (on-fail calls spos)))))

; Reading the source file gives us syntax objects, which contain a form
; decorated with syntax information.  To evaluate them, we update the source
; file location and evaluate the content.
(define (ruse-eval-source expr env calls spos on-scs on-err)
	(let ((new-spos
					`(,(source-file expr) (,(source-line expr) ,(source-column expr)) ,(source-form expr))))
		(ruse-eval (source-form expr) env calls new-spos on-scs on-err)))

(define (ruse-eval-quasiquote expr env calls spos on-scs on-fail on-err)
	(define (recurse cur-expr cur-spos)
		(let ((hdr
						(cond
							((not (list? cur-expr)) (void))
							((source? (car cur-expr)) (source-form (car cur-expr)))
							(else (car cur-expr)))))
			(cond
				((source? cur-expr)
				 (recurse (source-form cur-expr)
									`(,(source-file cur-expr) (,(source-line cur-expr) ,(source-column cur-expr)))))
				((eqv? 'unquote hdr)
				 (let/cc
					 return
					 (define (on-unquote-scs uq-val uq-env uq-calls uq-spos)
						 (return `(no-splice . ,uq-val)))
					 (ruse-eval (cadr cur-expr) env calls spos on-unquote-scs on-err)))
				((eqv? 'unquote-splicing hdr)
				 (let/cc
					 return
					 (define (on-unquote-scs uq-val uq-env uq-calls uq-spos)
						 (return `(splice . ,uq-val)))
					 (ruse-eval (cadr cur-expr) env calls spos on-unquote-scs on-err)))
				((list? cur-expr)
				 (cons
					 'no-splice
					 (let add-next ((pos cur-expr))
						 (if (null? pos)
							 null
							 (let ((arg (recurse (car pos) cur-spos)))
								 (if (eqv? 'splice (car arg))
									 (append (cdr arg) (add-next (cdr pos)))
									 (cons (cdr arg) (add-next (cdr pos)))))))))
				(else (cons 'no-splice cur-expr)))))
	(let ((rslt (cdr (recurse (cadr expr) spos))))
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
					(define (on-arg-scs val new-env new-calls new-spos)
						(arg-done val))
					(ruse-eval arg env calls spos on-arg-scs on-err))))
		(let* ((val-fm (map eval-arg (cdr fm)))
					 (bi-expr (cons (source->datum (car fm)) val-fm)))
			(let ((bi-rslt (eval bi-expr eval-ns)))
				(on-scs bi-rslt env calls spos)))))

; Evaluate dynamic form.
(define (ruse-eval-eval expr env calls spos on-scs on-fail on-err)
	(define (on-eval-arg-scs dyn-val dyn-env dyn-calls dyn-spos)
		(ruse-eval dyn-val dyn-env calls spos
							 (lambda (nval nenv)
								 (on-scs nval nenv calls spos)) on-err))
	(let ((fm (cadr expr)))
		(ruse-eval fm env calls spos on-eval-arg-scs on-err)))

; Evaluate scope declaration.
(define (ruse-eval-scope expr env calls spos on-scs on-fail on-err)
	(let ((fm (cadr expr))
				(scope-env (cons (make-scope-bdng (make-scope)) env)))
		(ruse-eval fm scope-env calls spos on-scs on-err)))

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
					(define (on-cond-scs cnd-val cond-env cond-calls cond-spos)
						(if cnd-val
							(ruse-eval rslt env calls spos on-scs on-err)
							(eval-cond (cdr cnd-pairs)))
						(exit))
					(if (eq? cnd 'else)
						(ruse-eval rslt env calls spos on-scs on-err)
						(ruse-eval cnd env calls spos on-cond-scs on-err)))))))

; Pattern matching.
(define (effective-val val) (if (source? val) (source-form val) val))
(define (ptn-is-var? ptn)
	(eqv? #\@ (string-ref (symbol->string ptn) 0)))
(define (ptn->var-name ptn)
	(string->symbol (substring (symbol->string ptn) 1)))
(define (match-sym ptn val bdngs on-scs on-fail)
	(if (eqv? ptn (effective-val val))
		(on-scs bdngs)
		(on-fail)))
(define (match-var ptn val bdngs on-scs on-fail)
	(on-scs (cons (cons (ptn->var-name ptn) val) bdngs)))
(define (match-pair ptn val bdngs on-scs on-fail)
	(if (pair? (effective-val val))
		(let ((sub-on-scs
						(lambda (new-bdngs)
							(match-ptn (cdr ptn) (cdr (effective-val val)) new-bdngs on-scs on-fail))))
			(match-ptn (car ptn) (car (effective-val val)) bdngs sub-on-scs on-fail))
		(on-fail)))
(define (match-ptn ptn val bdngs on-scs on-fail)
	(cond
		((and (symbol? ptn) (ptn-is-var? ptn))
		 (match-var ptn val bdngs on-scs on-fail))
		((symbol? ptn)
		 (match-sym ptn val bdngs on-scs on-fail))
		((pair? ptn) (match-pair ptn val bdngs on-scs on-fail))
		((and (null? ptn) (null? (effective-val val))) (on-scs bdngs))
		(else (on-fail))))

; Function taking a form (whose arguments have already been evaluated) and
; attempting to apply a specific rule to it.
(define (apply-rule rule expr env calls spos on-scs on-fail on-err)
	; Extract the pattern and the body from the rule.
	(let* ((templ (car rule))
				 (rl-env (cadr rule))
				 (rl-spos (caddr rule))
				 (ptn (car templ))
				 (body (cdr templ))
				 (on-match-scs
					 (lambda (bdngs)
						 (let ((new-env rl-env))
							 ; Add all the bindings from the match to the environment.
							 (do-ec (: bdng bdngs)
											(set! new-env (cons `(rule (,(car bdng) . (quote ,(cdr bdng))) () rl-spos) new-env)))
							 (on-scs body new-env
											 (cons (make-call-stack-frame 'rule spos rule bdngs) calls) rl-spos))))
				 (on-match-fail
					 (lambda ()
						 (on-fail calls spos))))
		; Using the handlers we have defined, attempt to match the pattern.
		(match-ptn ptn expr '() on-match-scs on-match-fail)))

; Function taking a form and attempting to apply a specific macro to it.
(define (apply-macro mac fm env calls spos on-scs on-fail on-err)
	; Extract the pattern and the body from the rule.
	(let* ((templ (car mac))
				 (mac-env (cadr mac))
				 (mac-spos (caddr mac))
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
												 ((source? sub-ptn)
													(source (recurse-pattern (source-form sub-ptn))
																	(source-file sub-ptn) (source-line sub-ptn) (source-column sub-ptn)))
												 ((pair? sub-ptn)
													(let* ((sub-val (recurse-pattern (cdr sub-ptn)))
																 (new-cdr
																	 (if (source? sub-val)
																		 (source-form sub-val)
																		 sub-val)))
														(cons (recurse-pattern (car sub-ptn)) new-cdr)))
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
											 (cons (make-call-stack-frame 'macro spos mac bdngs) calls) mac-spos)))))
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
									 (lambda (fcalls fspos) (recurse (cdr cur-env)))
									 on-err))
			; Check whether the current entry is a sub-scope.
			((bdng-is-scope? (car cur-env))
			 (let ((sub-env (unbox (bdng->scope (car cur-env)))))
				 (recurse sub-env)
				 (recurse (cdr cur-env))))
			; If the env entry is not a rule, skip it.
			(else (recurse (cdr cur-env)))))

	; We found no matching rules, so we failed.
	(on-fail calls spos))

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
	(on-fail calls spos))

; Compile a rule definition into an internal format.
(define (compile-rule-def rl)
	; Function for converting the pattern.
	(define (compile-pattern ptn)
		(let recurse ((fm ptn))
			(cond
				((source? fm) (recurse (source-form fm)))
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
				((source? fm) fm)
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
				((source? fm) (recurse (source-form fm)))
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
				((source? fm) fm)
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
			(let ((rl (list rl-tpl env spos)))
				(ruse-add-to-current-scope (cons 'rule rl) env calls spos on-err)
				(on-scs 'rule-def env calls spos))
			(on-fail calls spos))))

; Evaluate a macro definition (add it to the environment).
(define (ruse-eval-macro-def expr env calls spos on-scs on-fail on-err)
	(let ((mac-tpl (compile-macro-def (cdr expr))))
		(if mac-tpl
			(let ((mac (list mac-tpl env spos)))
				(ruse-add-to-current-scope (cons 'macro mac) env calls spos on-err)
				(on-scs 'mac-def env calls spos))
			(on-fail calls spos))))

; Perform reader expansions.
(define (ruse-perform-reader-expansions expr)
	(let recurse ((cur expr))
		(cond
			((null? cur) cur)
			((source? cur)
			 (source (recurse (source-form cur)) (source-file cur) (source-line cur) (source-column cur)))
			((pair? cur) (cons (recurse (car cur)) (recurse (cdr cur))))
			((string? cur) (list 'quote (list 'string cur)))
			((integer? cur) (list 'quote (list 'integer cur)))
			((symbol? cur) cur)
			(else (begin (printf "VAL=~v~n" cur) (car car))))))

; Execute a given file.
(define (ruse-load-file f env on-scs on-err)
	(let ((rslt (void))
				(errors 0)
				(file-env env))
		(define (load-from-port p)
			(port-count-lines! p)
			(let read-next-data ()
				(let ((src null))
					(let/cc
						skip-current-data
						(define (on-eval-scs val new-env calls spos)
							(set! rslt val)
							(set! file-env new-env)
							(skip-current-data))
						(define (on-eval-err msg calls spos)
							(set! rslt (void))
							(set! errors (+ 1 errors))
							(printf "Error while evaluating form: ~v~n  Message: ~a~n~n" (source->datum src) msg)
							(ruse-print-call-stack calls spos)
							(printf "~n")
							(skip-current-data))
						(let ((stx (read-syntax f p)))
							(set! src stx)
							(unless (eof-object? stx)
								(set! src (ruse-perform-reader-expansions (syntax->source stx)))
								(begin
									(ruse-eval src file-env null '("FILENAME" (1 1)) on-eval-scs on-eval-err)
									(printf "Shouldn't get here (2).~n")))))
					(unless (eof-object? src)
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
