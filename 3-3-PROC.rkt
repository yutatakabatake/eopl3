#lang eopl

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
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))

(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var val saved-env))))))

;Expressed values
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

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
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?)))

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
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg))))))

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

    ; proc-exp : proc(a) b
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression expression ")")
     call-exp)
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

(define test
  "let x = 200
           in let f = proc (z) -(z,x)
              in let x = 100
                 in let g = proc (z) -(z,x)
                    in -((f 1), (g 1))")

(define test2
  "let f = proc (x) -(x,11)
      in (f (f 77))")

; (value-of <<let f = proc (x) -(x,11) in (f (f 77))>> env)
; (value-of <<(f (f 77))>> (extend-env f (value-of <<proc(x) -(x,11)>> env) env))
; (value-of <<(f (f 77))>> (extend-env f (proc-val (procedure x <<-(x,11)>> env)) env))
; (apply-procedure (value-of <<f>> (extend-env f (proc-val (procedure x <<-(x,11)>> env)) env))
;                  (value-of <<(f 77)>> (extend-env f (proc-val (procedure x <<-(x,11)>> env)) env)))
; (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                  (apply-procedure (value-of <<f>> (extend-env f (proc-val (procedure x <<-(x,11)>> env)) env))
;                                   (value-of <<77>> (extend-env f (proc-val (procedure x <<-(x,11)>> env)) env))))
; (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                  (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                                   (num-val 77)))
; (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                  (value-of <<-(x,11)>> (extend-env x (num-val 77))))
; (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                  (num-val (- (value-of <<x>> (extend-env x (num-val 77)))
;                              (value-of <<11>> (extend-env x (num-val 77))))))
; (apply-procedure (proc-val (procedure x <<-(x,11)>> env))
;                  (num-val 66))
; (value-of <<-(x,11)>> (extend-env x (num-val 66) env))
; (num-val (value-of <<x>>)
;          (value-of <<11>>))
; (num-val 55)


(define test3
  "(proc (f) (f (f 77))
       proc (x) -(x,11))")

(define test4 "
let x = 77 in
  let f = proc (x) -(x,11) in
    -((f x), (f (f x)))
")

; (value-of <<let x = 55 in let f = proc (x) -(x,11) in -((f x), (f (f x)))>> init-env)
; (value-of <<let f = proc (x) -(x,11) in -((f x), (f (f x)))>> (extend-env x (num-val 77) init-env))
; (value-of <<-((f x), (f (f x)))>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env)))

; (num-val -
;          (expval->num (value-of <<(f x)>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env))))
;          (expval->num (value-of <<(f (f x))>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env)))))

; (num-val -
;          (expval->num (apply-procedure (expval->proc (value-of <<f>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env))))
;                                        (value-of <<x>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env)))))
;          (expval->num (apply-procedure (expval->proc (value-of <<f>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env))))
;                                        (value-of <<(f x)>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env))))))

; (num-val -
;          (expval->num (apply-procedure (expval->proc (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))))
;                                        (num-val 77)))
;          (expval->num (apply-procedure (expval->proc (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))))
;                                        (apply-procedure (expval->proc (value-of <<f>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env))))
;                                                         (value-of <<x>> (extend-env f (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))) (extend-env x (num-val 77) init-env)))))))

; (num-val -
;          (expval->num (apply-procedure (procedure x <<0(x,11)>> (extend-env x (num-val 77) init-env))
;                                        (num-val 77)))
;          (expval->num (apply-procedure (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))
;                                        (apply-procedure (expval->proc (proc-val (procedure x <<-(x,11)>> (extend-env x (num-val 77) init-env))))
;                                                         (num-val77)))))