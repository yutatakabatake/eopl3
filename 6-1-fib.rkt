#lang eopl

(define fib-normal
  (lambda (n)
    (if (< n 2)
        1
        (+
         (fib-normal (- n 1))
         (fib-normal (- n 2))))))

(define fib
  (lambda (n)
    (fib/k n (lambda (val) val))))

(define fib/k
  (lambda (n cont)
    (if (< n 2)
        (cont 1)
        (fib/k (- n 1)
               (lambda (val1)
                 (fib/k (- n 2)
                        (lambda (val2)
                          (cont (+ val1 val2)))))))))