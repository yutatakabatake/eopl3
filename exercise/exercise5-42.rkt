#lang eopl

; letccを拡張
; throwは違うかも


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
   (proc proc?))
  (list-val
   (lst (list-of expval?)))
  (cont-val
   (cont continuation?)))

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

; expval->proc : ExpVal → Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))

; expval->proc : ExpVal → ListOf(Int)
(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list v)))))

;expval->cont : ExpVal → Cont
(define expval->cont
  (lambda (val)
    (cases expval val
      (cont-val (cont) cont)
      (else (report-expval-extractor-error 'cont val)))))

; 継続のデータ型
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (rator-cont
   (rand expression?)
   (env environment?)
   (cont continuation?))
  (rand-cont
   (val1 expval?)
   (cont continuation?))
  (try-cont
   (var identifier?)
   (handler-exp expression?)
   (env environment?)
   (cont continuation?))
  (raise1-cont
   (saved-cont continuation?))
  (null1-cont
   (cont continuation?))
  (car-cont
   (cont continuation?))
  (cdr-cont
   (cont continuation?))
  (throw1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (throw2-cont
   (val1 expval?)
   (cont continuation?)))

; FinalAnswer = ExpVal
; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin
                  (eopl:printf "End of computation.~%")
                  val))
      (zero1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val
                               (zero? (expval->num val)))))
      (let-exp-cont (var body saved-env saved-cont)
                    (value-of/k body
                                (extend-env var val saved-env)
                                saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (if (expval->bool val)
                        (value-of/k exp2 saved-env saved-cont)
                        (value-of/k exp3 saved-env saved-cont)))
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont (num-val (- num1 num2)))))
      (rator-cont (rand env cont)
                  (value-of/k rand env (rand-cont val cont)))
      (rand-cont (val1 cont)
                 (let ((proc1 (expval->proc val1)))
                   (apply-procedure/k proc1 val cont)))
      (try-cont (var handler-exp env cont)
                (apply-cont cont val))
      (raise1-cont (cont)
                   (apply-handler val cont))
      (null1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val (null? (expval->list val)))))
      (car-cont (cont)
                (apply-cont cont (car (expval->list val))))
      (cdr-cont (cont)
                (apply-cont cont (list-val (cdr (expval->list val)))))
      (throw1-cont (exp2 env cont)
                   (value-of/k exp2 env
                               (throw2-cont val cont)))
      (throw2-cont (val1 cont)
                   (apply-cont (expval->cont val) val1)))))

; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var val saved-env)
                             cont)))))

; apply-handler : ExpVal × Cont → FinalAnswer
; 作った継続を落としていって直近のtry-contを見つける
(define apply-handler
  (lambda (val cont)
    (cases continuation cont
      (try-cont (var handler-exp saved-env saved-cont)
                (value-of/k handler-exp
                            (extend-env var val saved-env)
                            saved-cont))
      (end-cont ()
                (report-uncaught-exception))
      (diff1-cont (exp2 saved-env saved-cont)
                  (apply-handler val saved-cont))
      (diff2-cont (val1 saved-cont)
                  (apply-handler val saved-cont))
      (rator-cont (rand saved-env saved-cont)
                  (apply-handler val saved-cont))
      (rand-cont (val1 saved-cont)
                 (apply-handler val saved-cont))
      (raise1-cont (saved-cont)
                   (apply-handler val saved-cont))
      (zero1-cont (saved-cont)
                  (apply-handler val saved-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (apply-handler val saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (apply-handler val saved-cont))
      (null1-cont (saved-cont)
                  (apply-handler val saved-cont))
      (car-cont (saved-cont)
                (apply-handler val saved-cont))
      (cdr-cont (saved-cont)
                (apply-handler val saved-cont))
      (throw1-cont (exp2 env saved-cont)
                   (apply-handler val saved-cont))
      (throw2-cont (val1 saved-cont)
                   (apply-handler val saved-cont)))))


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
   (rand expression?))
  (try-exp
   (exp1 expression?)
   (var identifier?)
   (handler-exp expression?))
  (raise-exp
   (exp1 expression?))
  (list-exp
   (lst (list-of number?)))
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp1 expression?))
  (null?-exp
   (exp1 expression?))
  (emptylist-exp)
  (letcc-exp
   (var identifier?)
   (body expression?))
  (throw-exp
   (exp1 expression?)
   (exp2 expression?)))

;Syntax data types
;BNFでの文法
; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-cont))))))

; value-of/k : Exp × Env × Cont → FinalAnswer
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
                            (rator-cont rand env cont)))

      (try-exp (exp1 var handler-exp)
               (value-of/k exp1 env
                           (try-cont var handler-exp env cont)))
      (raise-exp (exp1)
                 (value-of/k exp1 env
                             (raise1-cont cont)))
      (list-exp (lst)
                (apply-cont cont
                            (list-val (map num-val lst))))
      (emptylist-exp ()
                     (apply-cont cont (list-val '())))
      (null?-exp (exp1)
                 (value-of/k exp1 env
                             (null1-cont cont)))
      (car-exp (exp1)
               (value-of/k exp1 env
                           (car-cont cont)))
      (cdr-exp (exp1)
               (value-of/k exp1 env
                           (cdr-cont cont)))
      (letcc-exp (var body)
                 (value-of/k body (extend-env var (cont-val cont) env)
                             cont))
      (throw-exp (exp1 exp2)
                 (value-of/k exp1 env
                             (throw1-cont exp2 env cont))))))


(define scanner-spec-exception
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

(define grammar-exception
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

    (expression
     ("try" expression "catch" "(" identifier ")" expression)
     try-exp)

    (expression
     ("raise" expression)
     raise-exp)

    (expression
     ("list" "(" (separated-list number ",") ")")
     list-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("emptylist")
     emptylist-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("letcc" identifier "in" expression)
     letcc-exp)

    (expression
     ("throw" expression "to" expression)
     throw-exp)))

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
  (sllgen:make-string-parser scanner-spec-exception grammar-exception))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-exception grammar-exception)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-uncaught-exception
  (lambda ()
    (eopl:error 'apply-handler "uncaught exception!")))


(define index-test
  "let index
           = proc (n)
              letrec inner (lst)
               = if null?(lst)
                 then raise 99
                 else if zero?(-(car(lst),n))
                      then 0
                      else -((inner cdr(lst)), -1)
                in proc (lst)
                    try (inner lst)
                        catch (x) -1
    in ((index 5) list(2, 3))")