#lang eopl

; 引数を受け取らないでexp,env,cont,val,proc1を共有するレジスタとする
; 引数なしの関数で末尾呼び出し tail call


(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-var identifier?)
   (body expression?)
   (env environment?)))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var) saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-name b-var p-body saved-env)
                      (if (eqv? search-var p-name)
                          (proc-val (procedure b-var p-body env))
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


(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (var identifier?)
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


(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (saved-cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff2-cont
   (val1 expval?)
   (saved-cont continuation?))
  (rator-cont
   (rand expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rand-cont
   (val1 expval?)
   (saved-cont continuation?)))


; apply-cont : () → FinalAnswer
; usage: : reads registers
; cont : Cont
; val : ExpVal
(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.~%")
                val)
      (zero1-cont (saved-cont)
                  (set! cont saved-cont)
                  (set! val (bool-val (zero? (expval->num val))))
                  (apply-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (set! cont saved-cont)
                    (set! exp body)
                    (set! env (extend-env var val saved-env))
                    (value-of/k))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (set! cont saved-cont)
                    (if (expval->bool val)
                        (set! exp exp2)
                        (set! exp exp3))
                    (set! env saved-env)
                    (value-of/k))
      (diff1-cont (exp2 saved-env saved-cont)
                  (set! cont (diff2-cont val saved-cont))
                  (set! exp exp2)
                  (set! env saved-env)
                  (value-of/k))
      (diff2-cont (val1 saved-cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (set! cont saved-cont)
                    (set! val (num-val (- num1 num2)))
                    (apply-cont)))
      (rator-cont (rand saved-env saved-cont)
                  (set! cont (rand-cont val saved-cont))
                  (set! exp rand)
                  (set! env saved-env)
                  (value-of/k))
      (rand-cont (rator-val saved-cont)
                 (let ((rator-proc (expval->proc rator-val)))
                   (set! cont saved-cont)
                   (set! proc1 rator-proc)
                   (set! val val)
                   (apply-procedure/k))))))

; apply-procedure/k : () → FinalAnswer
; usage: : relies on registers
; proc1 : Proc
; val : ExpVal
; cont : Cont
(define apply-procedure/k
  (lambda ()
    (cases proc proc1
      (procedure (var body saved-env)
                 (set! exp body)
                 (set! env (extend-env var val saved-env))
                 (value-of/k)))))

;Syntax data types
;BNFでの文法
(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (var-exp
   (var identifier?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (letrec-exp
   (proc-name identifier?)
   (bound-var identifier?)
   (proc-body expression?)
   (letrec-body expression?))
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
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (call-exp
   (rator expression?)
   (rand expression?)))

(define exp 'uninitialized)
(define env 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define proc1 'uninitialized)

; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (set! cont (end-cont))
                 (set! exp exp1)
                 (set! env (init-env))
                 (value-of/k)))))

; value-of/k : () → FinalAnswer
; usage: : relies on registers
; exp : Exp
; env : Env
; cont : Cont
; 次に評価したい式を新しいexpとする

(define value-of/k
  (lambda ()
    (cases expression exp
      (const-exp (num)
                 (set! val (num-val num))
                 (apply-cont))
      (var-exp (var)
               (set! val (apply-env env var))
               (apply-cont))
      (proc-exp (var body)
                (set! val (proc-val (procedure var body env)))
                (apply-cont))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (set! exp letrec-body)
                  (set! env (extend-env-rec p-name b-var p-body env))
                  (value-of/k))
      (zero?-exp (exp1)
                 (set! cont (zero1-cont cont))
                 (set! exp exp1)
                 (value-of/k))
      (let-exp (var exp1 body)
               (set! cont (let-exp-cont var body env cont))
               (set! exp exp1)
               (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! cont (if-test-cont exp2 exp3 env cont))
              (set! exp exp1)
              (value-of/k))
      (diff-exp (exp1 exp2)
                (set! cont (diff1-cont exp2 env cont))
                (set! exp exp1)
                (value-of/k))
      (call-exp (rator rand)
                (set! cont (rator-cont rand env cont))
                (set! exp rator)
                (value-of/k)))))


(define scanner-spec-trampoline
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

(define grammar-trampoline
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

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec"
      identifier "(" identifier ")" "=" expression
      "in" expression)
     letrec-exp)

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
  (sllgen:make-string-parser scanner-spec-trampoline grammar-trampoline))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-trampoline grammar-trampoline)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))


(define sigma
  "letrec sigma (x) = if zero?(x) 
                      then 0
                      else -((sigma -(x,1)), -(0,x))
    in (sigma 10)")