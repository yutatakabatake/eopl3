#lang eopl

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