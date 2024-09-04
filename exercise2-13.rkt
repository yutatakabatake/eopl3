#lang eopl

;Env = Var → SchemeVal

;empty-env : () → Env
(define empty-env
  (lambda ()
    (lambda (search-var)
      (if (eqv? search-var empty-env?)
          #t
          (report-no-binding-found search-var)))))

;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (cond
        ((eqv? search-var saved-var)
         saved-val)
        ((eqv? search-var empty-env?)
         (eqv? saved-env (empty-env)))))))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (env search-var)))

(define empty-env?
  (lambda (env)
    (env empty-env?)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for -s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: -s" env)))

;(define e (extend-env 'a 1 (extend-env 'b 2 (empty-env))))
;(apply-env e 'a)