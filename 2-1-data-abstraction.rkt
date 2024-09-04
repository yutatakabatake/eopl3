#lang eopl

; Exercise 2.1

(define zero (lambda () '()))

(define is-zero? (lambda (n) (null? n)))

(define successor
  (lambda (lst)
    (cond
      ((null? lst)
       '(1))
      ((not (eqv? (car lst) (- N 1)))
       (cons (+ (car lst) 1) (cdr lst)))
      ((eqv? (car lst) (- N 1))
       (if (null? (cdr lst))
           (cons 0 '(1))
           (cons 0 (successor (cdr lst))))))))

(define predecessor
  (lambda (lst)
    (cond
      ((null? lst)
       lst)
      ((not (eqv? (car lst) 0))
       (if (and (eqv? (- (car lst) 1) 0) (null? (cdr lst)))
           '()
           (cons (- (car lst) 1) (cdr lst))))
      ((eqv? (car lst) 0)
       (cons (- N 1) (predecessor (cdr lst)))))))

(define N 10)
(define ten (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (zero))))))))))))
(define one (successor (zero)))
(define two (successor (successor (zero))))
(define three (successor (successor (successor (zero)))))


;足し算
(define plus
  (lambda (num1 num2)
    (cond
      ((is-zero? num1)
       num2)
      ((is-zero? num2)
       num1)
      (else
       (successor (plus num1 (predecessor num2)))))))

;掛け算
(define mult
  (lambda (num1 num2)
    (if (or (is-zero? num1) (is-zero? num2))
        (zero)
        (plus num1 (mult num1 (predecessor num2))))))

;階乗
(define fact
  (lambda (num)
    (if (is-zero? num)
        (successor (zero))
        (mult num (fact (predecessor num))))))

