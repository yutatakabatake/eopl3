#lang eopl

; procedural represtntation of continuation, trampoline

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
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc val)))))


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

; Bounce = ExpVal ∪ (() → Bounce)
; FinalAnswer = ExpVal

; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
                 (trampoline
                  (value-of/k exp (init-env) (end-cont)))))))

; trampoline : Bounce → FinalAnswer
(define trampoline
  (lambda (bounce)
    (if (expval? bounce)
        bounce
        (trampoline (bounce)))))

; value-of/k : Exp × Env × Cont → Bounce
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (apply-env env var)))
      (proc-exp (var body)
                (apply-cont cont
                            (proc-val
                             (procedure var body env))))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of/k letrec-body
                              (extend-env-rec p-name b-var p-body env)
                              cont))
      (zero?-exp (exp1)
                 (value-of/k exp1 env
                             (zero1-cont cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont)))
      (let-exp (var exp1 body)
               (value-of/k exp1 env
                           (let-exp-cont var body env cont)))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                (value-of/k rator env
                            (rator-cont rand env cont))))))



; Cont = ExpVal → FinalAnswer
; end-cont : () → Cont
(define end-cont
  (lambda ()
    (lambda (val)
      (begin
        (eopl:printf "End of computation.~%")
        val))))

; zero1-cont : Cont → Cont
(define zero1-cont
  (lambda (cont)
    (lambda (val)
      (apply-cont cont
                  (bool-val
                   (zero? (expval->num val)))))))

; let-exp-cont : Var × Exp × Env × Cont → Cont
(define let-exp-cont
  (lambda (var body env cont)
    (lambda (val)
      (value-of/k body (extend-env var val env) cont))))

; if-test-cont : Exp × Exp × Env × Cont → Cont
(define if-test-cont
  (lambda (exp2 exp3 env cont)
    (lambda (val)
      (if (expval->bool val)
          (value-of/k exp2 env cont)
          (value-of/k exp3 env cont)))))

; diff1-cont : Exp × Env × Cont → Cont
(define diff1-cont
  (lambda (exp2 env cont)
    (lambda (val1)
      (value-of/k exp2 env (diff2-cont val1 cont)))))

; diff2-cont : ExpVal × Cont → Cont
(define diff2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((num1 (expval->num val1))
            (num2 (expval->num val2)))
        (apply-cont cont (num-val (- num1 num2)))))))

; rator-cont : Exp × Env × Cont → Cont
(define rator-cont
  (lambda (rand env cont)
    (lambda (val1)
      (value-of/k rand env (rand-cont val1 cont)))))

; rand-cont :
(define rand-cont
  (lambda (val1 cont)
    (lambda (val2)
      (let ((proc1 (expval->proc val1)))
        (lambda () (apply-procedure/k proc1 val2 cont))))))

; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont v)
    (cont v)))

; apply-procedure/k : Proc × ExpVal × Cont → Bounce
(define apply-procedure/k
  (lambda (proc1 val cont)
    (lambda ()
      (cases proc proc1
        (procedure (var body saved-env)
                   (value-of/k body
                               (extend-env var val saved-env)
                               cont))))))


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
    in (sigma 4)")



; (trampoline (value-of/k <<letrec sigma (x) = if zero?(x) then 0 else -((sigma -(x,1)), -(0,x)) in (sigma 4)>> env (end-cont)))
; (trampoline (value-of/k <<(sigma 4)>> (extend-env-rec sigma x <<if ...>> env) ((end-cont))))
; (trampoline (value-of/k <<sigma>> (extend-env-rec sigma x <<if ...>> env) (rator-cont <<4>> (extend-env-rec sigma x <<if ...>> env) (end-cont))))
; (trampoline (apply-cont (rator-cont <<4>> (extend-env-rec sigma x <<if ...>> env) (end-cont)) (proc-val (procedure x <<if ...>> env))))
; (trampoline (value-of/k <<4>> (extend-env-rec sigma x <<if ...>>) (rand-cont (proc-val (procedure x <<if ...>> env)) (end-cont))))
; (trampoline (apply-cont (rand-cont (proc-val (procedure x <<if ...>> env)) (end-cont)) (num-val 4)))
; (trampoline (apply-procedure/k (procedure x <<if ...>> env)) (num-val 4) (end-cont))
; (trampoline (value-of/k <<if ...>> (extend-env x (num-val 4) env) (end-cont)))
; (trampoline (value-of/k <<zero?(x)>> (extend-env x (num-val 4) env) (if-test-cont <<0>> <<-((sigma -(x,1)), -(0,x))>> (extend-env x (num-val 4) env) (end-cont))))
; (trampoline (value-of/k <<x>> (extend-env x (num-val 4) env) (if-test-cont <<0>> <<-((sigma -(x,1)), -(0,x))>> (extend-env x (num-val 4) env) (end-cont))))
; (trampoline ())