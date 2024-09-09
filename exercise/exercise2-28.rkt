#lang eopl

(define-datatype lc-exp lc-exp?
  (var-exp
   (var symbol?))
  (lambda-exp
   (bound-var symbol?)
   (body lc-exp?))
  (app-exp
   (rator lc-exp?)
   (rand lc-exp?)))

(define unparse-lc-exp-to-string
  (lambda (exp)
    (cases lc-exp exp
      (var-exp (var)
               (symbol->string var))
      (lambda-exp (bound-var body)
                  (string-append "lambda (" (symbol->string bound-var) ") " (unparse-lc-exp-to-string body)))
      (app-exp (rator rand)
               (string-append "(" (unparse-lc-exp-to-string rator) " " (unparse-lc-exp-to-string rand) ")")))))

(define exp1 (var-exp 'x))
(define exp2 (lambda-exp 'x (app-exp (var-exp 'x) (var-exp 'y))))
(define exp3 (app-exp (var-exp 'x) (var-exp 'y)))
(define exp4
  (lambda-exp 'x
              (app-exp (lambda-exp 'y
                                   (app-exp (var-exp 'y) (var-exp 'a)))
                       (var-exp 'x))))
