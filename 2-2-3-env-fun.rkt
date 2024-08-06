#lang eopl

;Env = Var → SchemeVal

;empty-env : () → Env
(define empty-env
    (lambda ()
      (lambda (search-var)
        (report-no-binding-found search-var))))

;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var) 
        saved-val
        (apply-env saved-env search-var)))))

;apply-env : Env × Var → SchemeVal
(define apply-env
    (lambda (env search-var)
      (env search-var)))


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for -s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: -s" env)))

;(define e (extend-env 'a 1 (extend-env 'b 2 (empty-env))))