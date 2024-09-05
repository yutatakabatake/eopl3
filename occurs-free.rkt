#lang eopl

;occurs-free? : Sym × LcExp → Bool
;usage: returns #t if the symbol var occurs free in exp, otherwise returns #f.
(define occurs-free?
  (lambda (var exp)
    (cond
      ((symbol? exp) (eqv? var exp))
      ((eqv? (car exp) 'lambda)
       (and
        (not (eqv? var (car (cadr exp))))
        (occurs-free? var (caddr exp))))
      (else (or
             (occurs-free? var (car exp))
             (occurs-free? var (cadr exp)))))))

; (occurs-free? 'x 'x)
; (occurs-free? 'x 'y)
; (occurs-free? 'x '(lambda (x) (x y)))
; (occurs-free? 'x '(lambda (y) (x y)))
; (occurs-free? 'x '((lambda (x) x) (x y)))
; (occurs-free? 'x '(lambda (y) (lambda (z) (x (y z)))))