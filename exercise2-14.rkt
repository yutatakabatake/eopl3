#lang eopl

;Env = Var → SchemeVal

;empty-env : () → Env
(define empty-env
  (lambda ()
    (lambda (cmd search-var)
      (cond
        ((eqv? cmd empty-env?)
         #t)
        ((eqv? cmd has-binding?)
         #f)
        (else
         (report-no-binding-found search-var))))))

;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (cmd search-var)
      (cond
        ((eqv? cmd apply-env)
         (if (eqv? search-var saved-var)
             saved-val
             (apply-env saved-env search-var)))
        ((eqv? cmd empty-env?)
         (eqv? saved-env (empty-env)))
        ((eqv? cmd has-binding?)
         (if (eqv? search-var saved-var)
             #t
             (has-binding? saved-env search-var)))))))


;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (env apply-env search-var)))

(define dummy 'dummy)

(define empty-env?
  (lambda (env)
    (env empty-env? dummy)))

(define has-binding?
  (lambda (env search-var)
    (env has-binding? search-var)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for -s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: -s" env)))

(define e (extend-env 'a 1 (extend-env 'b 2 (empty-env))))
;(apply-env e 'a)