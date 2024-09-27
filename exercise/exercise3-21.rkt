#lang eopl

; 複数の引数をとるprocに拡張
; ex3-23 再帰を使って階乗を計算　Yコンビネータ？　
; ex3-24 相互に再帰するoddとeven

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

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

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
                       (apply-procedure (procedure rest-var body (extend-env var val saved-env)) rest-val)))))))

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
   (var (list-of identifier?))
   (body expression?))
  (letproc-exp
   (p-name identifier?)
   (p-var identifier?)
   (p-body expression?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))
  (mult-exp
   (exp1 expression?)
   (exp2 expression?)))

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
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (letproc-exp (p-name p-var p-body body)
                   (let ((val1 (proc-val (procedure p-var p-body env))))
                     (value-of body (extend-env p-name val1 env))))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (map (lambda (exp) (value-of exp env)) rand)))
                  (apply-procedure proc arg)))
      (mult-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (* num1 num2))))))))

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
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    ; letproc-exp : letproc a (b) = c in d
    (expression
     ("letproc" identifier "(" identifier ")" "=" expression "in" expression)
     letproc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ; mult-exp : *(a,b) -> (* a b)
    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)
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
  "(proc (x, y, z) -(-(x, y),z)
  200 4 36)")

(define test2
  "let makemult = proc (maker)
                    proc (x)
                      if zero?(x)
                      then 0
                      else -(((maker maker) -(x,1)), -4)
    in let times4 = proc (x) ((makemult makemult) x) 
      in (times4 3)")

; (times4 3)
; = ((makemult makemult) 3)
; = ((proc (maker)
;       proc (x)
;         if zero?(x)
;            then 0
;           else -(((maker maker) -(x,1)), -4)   makemult) 3)
; = (proc (x)
;      if zero?(x)
;      then 0
;      else -(((makemult makemult) -(x,1)), -4)  3)
; = if zero?(3)
;   then 0
;   else -(((makemult makemult) -(3,1)), -4)
; = -(((makemult makemult) -(3,1)), -4)
; = -(((makemult makemult) 2), -4)
; = -(((proc (maker)
;         proc (x)
;           if zero?(x)
;           then 0
;           else -(((maker maker) -(x,1)), -4)   makemult) 2), -4)
; = -((proc (x)
;         if zero?(x)
;         then 0
;         else -(((makemult makemult) -(x,1)), -4) 2), -4)
; = -(if zero?(2)
;      then 0
;      else -(((makemult makemult) -(2,1)), -4), -4)
; = -(-(((makemult makemult) 1), -4), -4)           ← ((makemult makemult) 2) が -(((makemult makemult) 1), -4)になる
; = -(-(-(((makemult makemult) 0), -4), -4), -4)
; = -(-(-(0, -4), -4), -4)
; = 12


(define sigma
  "let makemult = proc (maker)
                    proc (x)
                      if zero?(x)
                      then 0
                      else -(((maker maker) -(x,1)), -(0,x))
    in let sigma = proc (x) ((makemult makemult) x)
      in (sigma 10)")

(define fact
  "let makemult = proc (maker)
                    proc (x)
                      if zero?(x)
                      then 1
                      else *(((maker maker) -(x,1)), x)
    in let fact = proc (x) ((makemult makemult) x)
      in (fact 5)")