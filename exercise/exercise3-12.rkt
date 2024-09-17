#lang eopl

;condを拡張

;Env = (empty-env) | (extend-env Var SchemeVal Env)
;Var = Sym

;empty-env : () → Env
(define empty-env
  (lambda ()
    (lambda (search-var)
      (report-no-binding-found search-var))))

;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var)
          saved-val
          (apply-env saved-env search-var)))))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (env search-var)))

;init-env : () → Env
;usage: (init-env) = [i=⌈1⌉,v=⌈5⌉,x=⌈10⌉]
(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))


;Expressed values
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (cons-val
   (first expval?)
   (rest expval?))
  (emptylist-val)
  (list-val
   (elems (list-of expval?))))

;interface
;expval->num : ExpVal → Int
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

;expval->bool : ExpVal → Bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

;同じデータ型を出力するextractorも作って良い
;expval->car : ExpVal → ExpVal
(define expval->car
  (lambda (val)
    (cases expval val
      (cons-val (first rest) first)
      (else
       (report-expval-extractor-error 'car val)))))

;expval->cdr : ExpVal → ExpVal
(define expval->cdr
  (lambda (val)
    (cases expval val
      (cons-val (first rest) rest)
      (else
       (report-expval-extractor-error 'cdr val)))))

;expval->null? : ExpVal → bool
(define expval->null?
  (lambda (val)
    (cases expval val
      (emptylist-val ()
                     #t)
      (cons-val (first rest)
                #f)
      (else
       (report-expval-extractor-error 'null? val)))))


;Syntax data types
;BNFでの文法
(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (minus-exp
   (exp1 expression?))
  (add-exp
   (exp1 expression?)
   (exp2 expression?))
  (mult-exp
   (exp1 expression?)
   (exp2 expression?))
  (quot-exp
   (exp1 expression?)
   (exp2 expression?))
  (equal?-exp
   (exp1 expression?)
   (exp2 expression?))
  (greater?-exp
   (exp1 expression?)
   (exp2 expression?))
  (less?-exp
   (exp1 expression?)
   (exp2 expression?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (emptylist-exp)
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp1 expression?))
  (null?-exp
   (exp1 expression?))
  (list-exp
   (exps (list-of expression?))))


;value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-env))))))

;value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (minus-exp (exp)
                 (num-val (* -1 (expval->num (value-of exp env)))))
      (add-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val
                    (+ num1 num2)))))
      (mult-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (* num1 num2)))))
      (quot-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (/ num1 num2)))))
      (equal?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (bool-val
                       (equal? num1 num2)))))
      (greater?-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (let ((num1 (expval->num val1))
                            (num2 (expval->num val2)))
                        (bool-val
                         (> num1 num2)))))
      (less?-exp (exp1 exp2)
                 (let ((val1 (value-of exp1 env))
                       (val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1))
                         (num2 (expval->num val2)))
                     (bool-val
                      (< num1 num2)))))
      (cons-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (cons-val val1 val2)))
      (emptylist-exp ()
                     (emptylist-val))
      (car-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (expval->car val1)))
      (cdr-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (cons-val (expval->cdr val1) (emptylist-val))))
      (null?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (bool-val (expval->null? val1))))
      (list-exp (exps)
                (if (null? exps)
                    (emptylist-val)
                    (list-val (map (lambda (exp-elem) (value-of exp-elem env)) exps)))))))


(define scanner-spec-let
  '((whitespace (whitespace) skip) ; Skip the whitespace
    ; Any arbitrary string of characters following a "%" upto a newline are skipped.
    (comment ("%" (arbno (not #\newline))) skip)
    ; An identifier is a letter followed by an arbitrary number of contiguous digits,
    ; letters, or specified punctuation characters.
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    ; A number is any digit followed by an arbitrary number of digits
    ; or a "-" followed by a digit and an arbitrary number of digits.
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define grammar-let
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression (identifier) var-exp)

    ; zero?-exp : zero?(a)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    ; diff-exp : -(a,b) -> (- a b)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    ; if-exp : if a then b else c
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    ; let-exp : let y = a in b
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    ; minus-exp : minus(a)
    (expression
     ("minus" "(" expression ")")
     minus-exp)

    ; add-exp : +(a,b) -> (+ a b)
    (expression
     ("+" "(" expression "," expression ")")
     add-exp)

    ; mult-exp : *(a,b) -> (* a b)
    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)

    ; quot-exp : /(a,b) -> (/ a b)
    (expression
     ("/" "(" expression "," expression ")")
     quot-exp)

    ; equal?-exp : equal?(a,b)
    (expression
     ("equal?" "(" expression "," expression ")")
     equal?-exp)

    ; greater?-exp : greater?(a,b)
    (expression
     ("greater?" "(" expression "," expression ")")
     greater?-exp)

    ; less?-exp : less?(a,b)
    (expression
     ("less?" "(" expression "," expression ")")
     less?-exp)

    ; cons-exp : cons(a,b)
    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    ; emptylist-exp : emptylist -> '()
    (expression
     ("emptylist")
     emptylist-exp)

    ; car-exp : car(a,b) -> a
    (expression
     ("car" "(" expression ")")
     car-exp)

    ; cdr-exp : cdr(a,b) -> (b)
    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    ; null?-exp : null?(a)
    (expression
     ("null?" "(" expression ")")
     null?-exp)

    ; list-exp : list(a,b,c,...) -> (a,b,c,...)
    (expression
     ("list" "(" (separated-list expression ",") ")" )
     list-exp)
    ))

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

;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-let grammar-let))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-let grammar-let)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-emptylist-error
  (lambda (val)
    (eopl:error 'emptylist "Emptylist: ~s" val)))