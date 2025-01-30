#lang eopl

; Schemeのbuilt-inと同じconcrete syntaxにする

; environment ----------------------------------------------------------
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?)))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var) saved-val
                      (apply-env saved-env search-var))))))

;init-env : () → Env
;usage: (init-env) = [i=⌈1⌉,v=⌈5⌉,x=⌈10⌉]
(define init-env
  (lambda ()
    (empty-env)))


;Expressed values -----------------------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

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

; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))

;Syntax data types -----------------------------------------------------
(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (var-exp
   (var identifier?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (proc-exp
   (var (list-of identifier?))
   (body expression?))
  (call-exp
   (binop binop?)
   (rator expression?)
   (rands (list-of expression?)))
  ; (exp-exp
  ;  (exp1 expression?))
  )

(define-datatype binop binop?
  (none-op)
  (plus-op)
  (minus-op)
  (mult-op)
  (div-op))

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
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (binop1 rator rands)
                (cases binop binop1
                  (none-op ()
                           (let ((proc (expval->proc (value-of rator env)))
                                 (arg (map (lambda (exp) (value-of exp env)) rands)))
                             (apply-procedure proc arg)))
                  (else
                   (let ((val1 (value-of rator env))
                         (vals (map (lambda (exp) (value-of exp env)) rands)))
                     (let ((num1 (expval->num val1))
                           (nums (map (lambda (val) (expval->num val)) vals)))
                       (value-of-binop binop1 num1 nums))))))
      ; (exp-exp (exp1)
      ;          (value-of exp1 env))
      )))

(define apply-procedure
  (lambda (proc1 arg)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (if (null? vars)
                     (value-of body saved-env)
                     (let ((var (car vars))
                           (rest-var (cdr vars))
                           (val (car arg))
                           (rest-val (cdr arg)))
                       (apply-procedure (procedure rest-var
                                                   body
                                                   (extend-env var val saved-env))
                                        rest-val)))))))

(define value-of-binop
  (lambda (binop1 num1 nums)
    (cases binop binop1
      (none-op ()
               (eopl:error 'binop "none-op"))
      (plus-op ()
               (num-val (apply + (cons num1 nums))))
      (minus-op ()
                (num-val (apply - (cons num1 nums))))
      (mult-op ()
               (num-val (apply * (cons num1 nums))))
      (div-op ()
              (num-val (apply / (cons num1 nums)))))))


(define scanner-spec-proc
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

(define grammar-proc
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression (identifier) var-exp)
    ; 式をカッコで括りたい
    ; (expression
    ;  ("(" expression ")")
    ;  exp-exp)

    ; zero?-exp : zero?(a)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    ; if-exp : if a then b else c
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    ; let-exp : let y = a in b
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    ; proc-exp : proc(a) b
    (expression
     ("lambda" "(" (arbno identifier) ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" binop expression (arbno expression) ")")
     call-exp)

    (binop
     ()
     none-op)

    (binop
     ("+")
     plus-op)

    (binop
     ("-")
     minus-op)

    (binop
     ("*")
     mult-op)

    (binop
     ("/")
     div-op)
    ))

(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-proc grammar-proc))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-proc grammar-proc)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))
