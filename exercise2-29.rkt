#lang eopl

(define-datatype lc-exp lc-exp?
  (var-exp
   (var symbol?))
  (lambda-exp
   (bound-var (list-of identifier?))
   (body lc-exp?))
  (app-exp
   (rator lc-exp?)
   (rand (list-of lc-exp?))))

(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define list-of
  (lambda (pred)
    (lambda (val)
      (or (null? val)
          (and (pair? val)
               (pred (car val))
               ((list-of pred) (cdr val)))))))

(define parser
  (lambda (datum)
    (cond
      ((symbol? datum)
       (var-exp datum))
      ((pair? datum)
       (if (eqv? (car datum) 'lambda)
           (lambda-exp (cadr datum)
                       (parser (caddr datum)))
           (app-exp (parser (car datum))
                    (map parser (cdr datum)))))
      (else
       (report-invalid-concrete-syntax datum)))))

(define report-invalid-concrete-syntax
  (lambda (datum)
    (eopl:error "invalid concrete syntax ~s" datum)))

(define input1 'x)
(define input2 '(lambda (x) (x y)))
(define input3 '(x y))