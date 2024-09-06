#lang eopl

(define report-invalid-concrete-syntax
  (lambda (datum)
    (eopl:error "invalid concrete syntax ~s" datum)))

(define-datatype lc-exp lc-exp?
  (var-exp
   (var symbol?))
  (lambda-exp
   (bound-var symbol?)
   (body lc-exp?))
  (app-exp
   (rator lc-exp?)
   (rand lc-exp?)))

(define exp1 (var-exp 'x))
(define exp2 (lambda-exp 'x (app-exp (var-exp 'x) (var-exp 'y))))
(define exp3 (app-exp (var-exp 'x) (var-exp 'y)))

; パターンマッチをしてる　lambda-expならbound-varとbodyを取り出す　extractorをしてる

(define occurs-free?
  (lambda (search-var exp)
    (cases lc-exp exp
      (var-exp (var)
               (eqv? var search-var))
      (lambda-exp (bound-var body)
                  (and
                   (not (eqv? search-var bound-var))
                   (occurs-free? search-var body)))
      (app-exp (rator rand)
               (or
                (occurs-free? search-var rator)
                (occurs-free? search-var rand))))))


(define-datatype s-list s-list?
  (empty-s-list)
  (non-empty-s-list
   (first s-exp?)
   (rest s-list?)))

(define-datatype s-exp s-exp?
  (symbol-s-exp
   (sym symbol?))
  (s-list-s-exp
   (slst s-list?)))

(define list-of
  (lambda (pred)
    (lambda (val)
      (or (null? val)
          (and (pair? val)
               (pred (car val))
               ((list-of pred) (cdr val)))))))

((list-of number?) '(1 2 3 4 5))
((list-of number?) '(1 2 3 4 5 a))

;parse-expression : SchemeVal → LcExp
(define parse-expression
  (lambda (datum)
    (cond
      ((symbol? datum) (var-exp datum))
      ((pair? datum)
       (if (eqv? (car datum) 'lambda)
           (lambda-exp
            (car (cadr datum))
            (parse-expression (caddr datum)))
           (app-exp
            (parse-expression (car datum))
            (parse-expression (cadr datum)))))
      (else (report-invalid-concrete-syntax datum)))))

(define lambda1 (parse-expression 'x))
(define lambda2 (parse-expression '(lambda (x) (+ x 1))))
(define lambda3 (parse-expression '((lambda (x) (+ x 1)) n)))