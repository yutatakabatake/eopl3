#lang eopl

(define-datatype prefix-exp prefix-exp?
  (const-exp
   (num integer?))
  (diff-exp
   (operand1 prefix-exp?)
   (operand2 prefix-exp?)))

(define flatten-prefix
  (lambda (exp)
    (list (car exp) (cdr exp))))

(define parse-prefix-exp
  (lambda (exp)
    (let ((flatten-prefix-exp (flatten-prefix exp)))
      (let ((prefix (car flatten-prefix-exp))
            (elem (cadr flatten-prefix-exp)))
        (cond
          ((eqv? prefix '-)
           (diff-exp (parse-prefix-exp elem) (parse-prefix-exp (cdr elem))))
          ((integer? prefix)
           (const-exp prefix)))))))

(define search-diff
  (lambda (exp)
    (cond
      ((eqv? (car exp) '-)
       (cdr exp))
      ((integer? (car exp))
       (search-diff (cdr exp)))
      ((null? exp)
       '()))))

(define test '(- - 3 2 - 4 - 12 7))
(define pexp '(- - 5 2 1))