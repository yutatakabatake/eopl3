#lang eopl

(define-datatype env env?
  (empty-env)
  (extend-env
   (var symbol?)
   (val number?)
   (saved-env env?)))

(define apply-env
  (lambda (environment search-var)
    (cases env environment
      (empty-env ()
                 (report-no-binding-found))
      (extend-env (var val saved-env)
                  (if (eqv? search-var var)
                      val
                      (apply-env saved-env search-var))))))

(define has-binding?
  (lambda (environment search-var)
    (cases env environment
      (empty-env ()
                 #f)
      (extend-env (var val saved-env)
                  (if (eqv? search-var var)
                      #t
                      (has-binding? saved-env search-var))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

;(define e (extend-env 'x 1 (extend-env 'y 2 (empty-env))))
;(apply-env e 'x)