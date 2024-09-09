#lang eopl

(define-datatype stack stack?
  (empty-stack)
  (push
   (val number?)
   (saved-stk stack?)))

(define pop
  (lambda (saved-stk)
    (cases stack saved-stk
      (empty-stack ()
                   (report-empty-stack))
      (push (val saved-stk)
            saved-stk))))

(define top
  (lambda (saved-stk)
    (cases stack saved-stk
      (empty-stack ()
                   (report-empty-stack))
      (push (val saved-stk)
            val))))

(define empty-stack?
  (lambda (saved-stk)
    (cases stack saved-stk
      (empty-stack ()
                   #t)
      (push (val saved-stk)
            #f))))

(define report-empty-stack
  (lambda (stk)
    (eopl:error 'pop 'top "Empty stack: ~s" stk)))

(define stk (push 2 (push 1 (empty-stack))))