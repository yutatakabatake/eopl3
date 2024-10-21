#lang eopl

(define fact
  (lambda (n)
    (fact/k n (lambda (val) val))))

(define fact/k
  (lambda (n cont)
    (if (zero? n)
        (cont 1)
        (fact/k (- n 1) (lambda (val) (cont (* n val)))))))

; (fact 4)
; (fact/k 4 (lambda (val1) val1))
; (fact/k 3 (lambda (val2) ((lambda (val1) val1) (* 4 val2))))
; (fact/k 3 (lambda (val2) (* 4 val2)))
; (fact/k 2 (lambda (val3) ((lambda (val2) (* 4 val2)) (* 3 val3))))
; (fact/k 2 (lambda (val3) (* 4 (* 3 val3))))
; (fact/k 1 (lambda (val4) ((lambda (val3) (* 4 (* 3 val3))) (* 2 val4))))
; (fact/k 1 (lambda (val4) (* 4 (* 3 (* 2 val4)))))
; (fact/k 0 (lambda (val5) ((lambda (val4) (* 4 (* 3 (* 2 val4)))) (* 1 val5))))
; (fact/k 0 (lambda (val5) (* 4 (* 3 (* 2 (* 1 val5))))))
; ((lambda (val5) (* 4 (* 3 (* 2 (* 1 val5))))) 1)
; (* 4 (* 3 (* 2 1)))
; 24