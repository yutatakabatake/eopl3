#lang eopl

; a-Env = (a-empty-env) | (a-extend-env a-Env)
; Val = Sym

(define a-empty-env
  (lambda ()
    '()))

(define a-extend-env
  (lambda (var val a-env)
    (cons (cons var val) a-env)))

(define a-apply-env
  (lambda (a-env search-var)
    (if (null? a-env)
        (report-no-binding-found search-var)
        (let ((saved-var (car (car a-env))) (saved-val (cdr (car a-env))) (saved-env (cdr a-env)))
          (cond
            ((eqv? saved-var search-var)
             saved-val)
            (else
             (a-apply-env saved-env search-var)))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

;(define e (a-extend-env 'a 1 (a-extend-env 'b 2 (a-extend-env 'c 3 (a-empty-env)))))

;has-binding? : Env × Var -> Bool
(define has-binding?
  (lambda (a-env s)
    (if (null? a-env)
        #f
        (let ((saved-var (car (car a-env))) (saved-val (cdr (car a-env))) (saved-env (cdr a-env)))
          (cond
            ((eqv? saved-var s)
             #t)
            (else
             (has-binding? saved-env s)))))))