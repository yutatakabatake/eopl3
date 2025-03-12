#lang eopl

; extend-env-recを効率的にする
; extend-env-recでクロージャ生成を一度だけする
; 相互再帰，複数引数関数

; Environment -----------------------------------------------------------
; Env = Var → SchemeVal

; empty-env : () → Env
(define empty-env
  (lambda ()
    '()))

; extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (list saved-var saved-val saved-env)))

; (define extend-env-rec
;   (lambda (p-name b-var body saved-env)
;     (let ((vec (make-vector 1)))
;       (let ((new-env (extend-env p-name vec saved-env)))
;         (vector-set! vec 0
;                      (proc-val (procedure b-var body new-env)))
;         new-env))))




(define extend-env-list
  (lambda (saved-vars saved-vals saved-env)
    (if (null? saved-vars)
        saved-env
        (let ([saved-var (car saved-vars)]
              [saved-val (car saved-vals)]
              [rest-var (cdr saved-vars)]
              [rest-val (cdr saved-vals)])
          (extend-env saved-var saved-val (extend-env-list rest-var rest-val saved-env))))))

; apply-env: Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (cond
      ((null? env)
       (report-no-binding-found search-var))
      ((eqv? (car env) search-var)
       (let ([saved-val (cadr env)])
         (if (vector? saved-val) ; vector?がtrueならextend-env-recを使っている
             (vector-ref saved-val 0)
             saved-val)))
      (else
       (let ([saved-env (caddr env)])
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

; Expressed values -----------------------------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

; proc? : SchemeVal → Bool
(define proc?
  (lambda (val)
    (procedure? val))) ; procedure?はracketの組み込み


; procedure : Var × Exp × Env → Proc
(define procedure
  (lambda (vars body env)
    (lambda (vals)
      (value-of body (extend-env-list vars vals env)))))

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
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  (call-exp
   (rator expression?)
   (rands (list-of expression?)))
  (letrec-exp
   (proc-names (list-of identifier?))
   (bound-varss (list-of (list-of identifier?)))
   (proc-bodies (list-of expression?))
   (letrec-body expression?)))

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
      (let-exp (vars exps body)
               (let ((vals (map (lambda (exp) (value-of exp env)) exps)))
                 (value-of body
                           (extend-env-list vars vals env))))
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (map (lambda (rand) (value-of rand env)) rands)))
                  (apply-procedure proc arg)))
      (letrec-exp (proc-names bound-varss proc-bodies letrec-body)
                  (value-of letrec-body (extend-env-rec* proc-names bound-varss proc-bodies env))))))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (proc1 val)))

(define scanner-spec-letrec
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

(define grammar-letrec
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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    ; proc-exp : proc(a) b
    (expression
     ("proc" "(" (arbno identifier) ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec"
      (arbno identifier "(" (arbno identifier) ")" "=" expression)
      "in" expression)
     letrec-exp)))

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
  (sllgen:make-string-parser scanner-spec-letrec grammar-letrec))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-letrec grammar-letrec)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define sigma
  "letrec sigma (x) = if zero?(x) 
                      then 0
                      else -((sigma -(x,1)), -(0,x))
    in (sigma 4)")

(define even-odd
  "letrec
    even(x) = if zero?(x) then 1 else (odd -(x,1))
    odd(x) = if zero?(x) then 0 else (even -(x,1))
  in (odd 13)")

(define even-odd2
  "letrec
    even(x y) = if zero?(x) then 1 else (odd -(x,1) 0)
    odd(x y) = if zero?(x) then 0 else (even -(x,1) 0)
  in (odd 13 0)")