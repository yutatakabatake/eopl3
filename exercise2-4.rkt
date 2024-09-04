#lang eopl

;constructors
(define empty-stack
  (lambda ()
    (list 'empty-stack)))

;constructors
(define push
  (lambda (val stk)
    (list 'push val stk)))

;observer
(define pop
  (lambda (stk)
    (cond
      ((eqv? (car stk) 'empty-stack)
       '())
      ((eqv? (car stk) 'push)
       (cdr stk))
      (else
       (report-invalid-env)))))

;observer
(define top
  (lambda (stk)
    (cond
      ((eqv? (car stk) 'empty-stack)
       '())
      ((eqv? (car stk) 'push)
       (cadr stk))
      (else
       (report-invalid-env)))))

;observers
(define empty-stack?
  (lambda (stk)
    (eqv? (car stk) 'empty-stack)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))