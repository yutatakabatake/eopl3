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
       (report-empty-stack))
      ((eqv? (car stk) 'push)
       (caddr stk))
      (else
       (report-invalid-stk)))))

;observer
(define top
  (lambda (stk)
    (cond
      ((eqv? (car stk) 'empty-stack)
       (report-empty-stack))
      ((eqv? (car stk) 'push)
       (cadr stk))
      (else
       (report-invalid-stk)))))

;observers
(define empty-stack?
  (lambda (stk)
    (eqv? (car stk) 'empty-stack)))

(define report-invalid-stk
  (lambda (stk)
    (eopl:error 'pop 'top "Bad stkironment: ~s" stk)))

(define report-empty-stack
  (lambda (stk)
    (eopl:error 'pop 'top "Empty stack: ~s" stk)))

;(define stk (push 1 (push 2 (push 3 (empty-stack)))))