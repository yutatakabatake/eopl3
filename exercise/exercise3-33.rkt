#lang eopl

; 相互再帰，複数引数関数の実装

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-list
   (vars (list-of identifier?))
   (vals (list-of expval?))
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (p-bodies (list-of expression?))
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
      (extend-env-list (saved-vars saved-vals saved-env)
                       (if (null? saved-vars)
                           (apply-env saved-env search-var)
                           (if (eqv? (car saved-vars) search-var)
                               (car saved-vals)
                               (apply-env (extend-env-list (cdr saved-vars) (cdr saved-vals) saved-env)
                                          search-var))))
      (extend-env-rec* (p-names b-varss p-bodies saved-env)
                       (if (null? p-names)
                           (apply-env saved-env search-var)
                           (let ((res (has-proc? search-var p-names b-varss p-bodies)))
                             (if (car res)
                                 (proc-val (procedure (cadr res) (caddr res) env))
                                 (apply-env saved-env search-var))))))))

; 複数のprocedureからsearch-varに束縛されたprocedureを探す
(define has-proc?
  (lambda (search-var p-names b-varss p-bodies)
    (if (null? p-names)
        (list #f)
        (if (eqv? (car p-names) search-var)
            (list #t (car b-varss) (car p-bodies))
            (has-proc? search-var (cdr p-names) (cdr b-varss) (cdr p-bodies))))))

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
               (let ((vals (map (value-of exp env) exps)))
                 (value-of body
                           (extend-env-list vars vals env))))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (rand) (value-of rand env)) rands)))
                  (apply-procedure proc args)))
      (letrec-exp (proc-names bound-varss proc-bodies letrec-body)
                  (value-of letrec-body (extend-env-rec* proc-names bound-varss proc-bodies env))))))

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
                       (apply-procedure (procedure rest-var body (extend-env var val saved-env))
                                        rest-val)))))))


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

    ; letrec-exp : letrec a (b) = c in d
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression)
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