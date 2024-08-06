#lang eopl 

;Env = (empty-env) | (extend-env Var SchemeVal Env)
;Var = Sym

;empty-env : () → Env
(define empty-env
  (lambda () 
    (list 'empty-env)))


;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))

;apply-env : Env × Var → SchemeVal 
(define apply-env
  (lambda (env search-var)
    (cond
      ((eqv? (car env) 'empty-env) (report-no-binding-found search-var))
      ((eqv? (car env) 'extend-env)
       (let ((saved-var (cadr env))
             (saved-val (caddr env))
             (saved-env (cadddr env)))
         (if (eqv? search-var saved-var)
             saved-val
             (apply-env saved-env search-var))))
      (else
       (report-invalid-env env)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))











; Exercise 2.11
;Env = (rib-empty-env) | (rib-extend-env Var SchemeVal Env)
;Var = Sym



(define rib-empty-env
  (lambda ()
    '()))

(define rib-extend-env
  (lambda (var-lst val-lst env)
    (cons (cons var-lst (list val-lst)) env)))

;(define rib-apply-env
;  (lambda (env search-var)
;    (if (null? env)
;        (report-no-binding-found search-var)
;        (let ((saved-var-lst (car (car env))) (saved-val-lst (cdr (car env))) (rst-env (cdr env)))
;          (let ((


(define env (rib-extend-env '(a b c) '(11 12 13) (rib-extend-env '(x z) '(66 77) (rib-extend-env '(x y) '(88 99) (rib-empty-env)))))

;Exercise 2.12
