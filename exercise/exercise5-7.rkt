#lang eopl

;letを任意の数の変数宣言をするように拡張

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
   (env environment?))
  (extend-env-list
   (vars (list-of identifier?))
   (vals (list-of expval?))
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
                          (apply-env saved-env search-var)))
      (extend-env-list (vars vals env)
                       (if (eqv? search-var (car vars))
                           (car vals)
                           (apply-env (extend-env-list (cdr vars) (cdr vals) env) search-var))))))

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
   (lst (list-of expval?))))

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

; expval->list : ExpVal → ListOf(ExpVal)
(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list val)))))

; expval->car : ExpVal → ExpVal
(define expval->car
  (lambda (val)
    (cases expval val
      (list-val (lst) (car lst))
      (else (report-expval-extractor-error 'car val)))))



; 継続のデータ型
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (cont continuation?))
  (letfst-exp-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?)
   (env environment?)
   (cont continuation?))
  (letrst-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (vals (list-of expval?))
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
  (let21-cont
   (var1 identifier?)
   (var2 identifier?)
   (exp2 expression?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (let22-cont
   (var1 identifier?)
   (val1 expval?)
   (var2 identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (let31-cont
   (var1 identifier?)
   (var2 identifier?)
   (exp2 expression?)
   (var3 identifier?)
   (exp3 expression?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (let32-cont
   (var1 identifier?)
   (val1 expval?)
   (var2 identifier?)
   (var3 identifier?)
   (exp3 expression?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (let33-cont
   (var1 identifier?)
   (val1 expval?)
   (var2 identifier?)
   (val2 expval?)
   (var3 identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (cons2-cont
   (val1 expval?)
   (cont continuation?))
  (null1-cont
   (cont continuation?))
  (car-cont
   (cont continuation?))
  (cdr-cont
   (cont continuation?))
  (listfst-cont
   (lst (list-of expression?))
   (env environment?)
   (cont continuation?))
  (listrst-cont
   (lst (list-of expression?))
   (val-lst expval?)
   (env environment?)
   (cont continuation?))
  )

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
      (letfst-exp-cont (vars exps body saved-env saved-cont)
                       (if (null? exps)
                           (value-of/k body
                                       (extend-env (car vars) val saved-env)
                                       saved-cont)
                           (value-of/k (car exps) saved-env
                                       (letrst-cont vars (cdr exps) (list val) body saved-env saved-cont))))
      (letrst-cont (vars exps vals body saved-env saved-cont)
                   (if (null? exps)
                       (value-of/k body
                                   (extend-env-list vars (append vals (list val)) saved-env)
                                   saved-cont)
                       (value-of/k (car exps) saved-env
                                   (letrst-cont vars (cdr exps) (append vals (list val)) body saved-env saved-cont))))

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

      (let21-cont (var1 var2 exp2 body env cont)
                  (value-of/k exp2 env
                              (let22-cont var1 val var2 body env cont)))

      (let22-cont (var1 val1 var2 body env cont)
                  (value-of/k body
                              (extend-env var1 val1
                                          (extend-env var2 val env))
                              cont))

      (let31-cont (var1 var2 exp2 var3 exp3 body env cont)
                  (value-of/k exp2 env
                              (let32-cont var1 val var2 var3 exp3 body env cont)))

      (let32-cont (var1 val1 var2 var3 exp3 body env cont)
                  (value-of/k exp3 env
                              (let33-cont var1 val1 var2 val var3 body env cont)))

      (let33-cont (var1 val1 var2 val2 var3 body env cont)
                  (value-of/k body
                              (extend-env var1 val1
                                          (extend-env var2 val2
                                                      (extend-env var3 val env)))
                              cont))
      (cons1-cont (exp2 env cont)
                  (value-of/k exp2 env
                              (cons2-cont val cont)))
      (cons2-cont (val1 cont)
                  (apply-cont cont (list-val (cons val1 (list val)))))
      (null1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val (null? (expval->list val)))))
      (car-cont (cont)
                (apply-cont cont (expval->car val)))
      (cdr-cont (cont)
                (apply-cont cont (cdr (expval->list val))))
      (listfst-cont (lst env cont)
                    (if (null? lst)
                        (apply-cont cont (list-val (list val)))
                        (value-of/k (car lst) env
                                    (listrst-cont (cdr lst) (list-val (list val)) env cont))))
      (listrst-cont (lst val-lst env cont)
                    (if (null? lst)
                        (apply-cont cont (list-val (append (expval->list val-lst) (list val))))
                        (value-of/k (car lst) env
                                    (listrst-cont (cdr lst) (list-val (append (expval->list val-lst) (list val))) env cont))))
      )))

; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var val saved-env)
                             cont)))))

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
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (let2-exp
   (var1 identifier?)
   (exp1 expression?)
   (var2 identifier?)
   (exp2 expression?)
   (body expression?))
  (let3-exp
   (var1 identifier?)
   (exp1 expression?)
   (var2 identifier?)
   (exp2 expression?)
   (var3 identifier?)
   (exp3 expression?)
   (body expression?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp1 expression?))
  (null?-exp
   (exp1 expression?))
  (emptylist-exp)
  (list-exp
   (lst (list-of expression?)))
  )


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
      (let-exp (vars exps body)
               (if (null? vars)
                   (value-of/k body env cont)
                   (value-of/k (car exps) env
                               (letfst-exp-cont vars (cdr exps) body env cont))))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                (value-of/k rator env
                            (rator-cont rand env cont)))
      (let2-exp (var1 exp1 var2 exp2 body)
                (value-of/k exp1 env
                            (let21-cont var1 var2 exp2 body env cont)))
      (let3-exp (var1 exp1 var2 exp2 var3 exp3 body)
                (value-of/k exp1 env
                            (let31-cont var1 var2 exp2 var3 exp3 body env cont)))
      (cons-exp (exp1 exp2)
                (value-of/k exp1 env
                            (cons1-cont exp2 env cont)))
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
      (list-exp (lst)
                (if (null? lst)
                    (apply-cont cont (list-val '()))
                    (value-of/k (car lst) env
                                (listfst-cont (cdr lst) env cont)))
                ))))


(define scanner-spec-cont-letrec
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

(define grammar-cont-letrec
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
     ("let2" identifier "=" expression
             identifier "=" expression
             "in" expression)
     let2-exp)

    (expression
     ("let3" identifier "=" expression
             identifier "=" expression
             identifier "=" expression
             "in" expression)
     let3-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

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
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

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
  (sllgen:make-string-parser scanner-spec-cont-letrec grammar-cont-letrec))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-cont-letrec grammar-cont-letrec)))

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
  "let x = 30
      in let x = -(x,1)
             y = -(x,2)
         in -(x,y)")