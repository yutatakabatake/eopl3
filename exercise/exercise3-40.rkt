#lang eopl
; lexical address translatorとinterpreterにletrecを拡張
; インタプリタ未完成

; static environment -------------------------------------------------
; Senv = Listof(pair(Label, Sym))
; Lexaddr = N

; empty-senv : () → Senv
(define empty-senv
  (lambda ()
    '()))

; extend-senv : Var × Senv → Senv
(define extend-senv
  (lambda (var senv)
    (cons (list 'extend-senv var) senv)))

; extend-senv : ListOf(Var) × Senv → Senv
(define extend-senv*
  (lambda (vars senv)
    (let ([new-vars
           (reverse (map (lambda (var) (list 'extend-senv var)) vars))])
      (append new-vars senv))))

; extend-senv-rec : Var × Senv → Senv
(define extend-senv-rec
  (lambda (var senv)
    (cons (list 'exptend-senv-rec var) senv)))

; apply-senv : Senv × Var → Lexaddr
(define apply-senv
  (lambda (senv var)
    (cond
      ((null? senv)
       (report-unbound-var var))
      ((eqv? var (cadar senv))
       0)
      (else
       (+ 1 (apply-senv (cdr senv) var))))))

; init-senv : () → Senv
(define init-senv
  (lambda ()
    (empty-senv)))

; nameless-environment -------------------------------------------------
; nameless-environment? : SchemeVal → Bool
(define nameless-environment?
  (lambda (x)
    #t))

; empty-nameless-env : () → Nameless-env
(define empty-nameless-env
  (lambda ()
    '()))

; extend-nameless-env : ExpVal × Nameless-env → Nameless-env
(define extend-nameless-env
  (lambda (val nameless-env)
    (cons (list 'normal val) nameless-env)))

(define extend-nameless-env-with-unpacking
  (lambda (val nameless-env)
    (cases expval val
      (pair-val (fst rst)
                (extend-nameless-env-with-unpacking
                 rst
                 (extend-nameless-env fst nameless-env)))
      (emptylist-val ()
                     (extend-nameless-env val nameless-env))
      (else
       (eopl:error 'extend-nameless-env-with-unpacking "~s must be pair-val" val)))))

(define extend-nameless-env-rec
  (lambda (val nameless-env)
    (cons (list 'rec val) nameless-env)))

; apply-nameless-env : Nameless-env × Lexaddr → ExpVal
(define apply-nameless-env
  (lambda (nameless-env n)
    (let ((cell (list-ref nameless-env n)))
      (let ((label (car cell))
            (val (cadr cell)))
        (if (eqv? 'rec label)
            (cases expval val
              (proc-val (proc1)
                        (cases proc proc1
                          (procedure (body env)
                                     (proc-val (procedure body nameless-env)))))
              (else (eopl:error 'apply-nameless-env "recursive value ~s must be proc-val" val)))
            val
            )))))

(define init-nameless-env
  (lambda ()
    (empty-nameless-env)))


;Expressed values -------------------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (pair-val
   (first expval?)
   (rest expval?))
  (emptylist-val))

; procedure : Nameless-exp × Nameless-env → Proc
(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-nameless-env nameless-environment?)))

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

(define expval->first
  (lambda (val)
    (cases expval val
      (pair-val (fst rst)
                fst)
      (else (report-expval-extractor-error 'pair val)))))

(define expval->rest
  (lambda (val)
    (cases expval val
      (pair-val (fst rst)
                rst)
      (else (report-expval-extractor-error 'pair val)))))


;Syntax data types -------------------------------------------------
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
   (rand expression?))
  (emptylist-exp)
  (pack-exp
   (exps (list-of expression?)))
  (unpack-exp
   (vars (list-of identifier?))
   (exp1 expression?)
   (body expression?))
  (letrec-exp
   (p-name identifier?)
   (b-var identifier?)
   (p-body expression?)
   (letrec-body expression?))
  (nameless-var-exp
   (num number?))
  (nameless-let-exp
   (exp1 expression?)
   (body expression?))
  (nameless-proc-exp
   (body expression?))
  (nameless-unpack-exp
   (exp1 expression?)
   (body expression?))
  (nameless-letrec-exp
   (p-body expression?)
   (letrec-body expression?)))

; translator -------------------------------------------------
; translation-of-program : Program → Nameless-program
(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program
                  (translation-of exp1 (init-senv)))))))

; translation-of : Exp × Senv → Nameless-exp
(define translation-of
  (lambda (exp senv)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (diff-exp (exp1 exp2)
                (diff-exp
                 (translation-of exp1 senv)
                 (translation-of exp2 senv)))
      (zero?-exp (exp1)
                 (zero?-exp
                  (translation-of exp1 senv)))
      (if-exp (exp1 exp2 exp3)
              (if-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)
               (translation-of exp3 senv)))
      (var-exp (var)
               (nameless-var-exp
                (apply-senv senv var)))
      (let-exp (var exp1 body)
               (nameless-let-exp
                (translation-of exp1 senv)
                (translation-of body
                                (extend-senv var senv))))
      (proc-exp (var body)
                (nameless-proc-exp
                 (translation-of body
                                 (extend-senv var senv))))
      (call-exp (rator rand)
                (call-exp
                 (translation-of rator senv)
                 (translation-of rand senv)))
      (emptylist-exp ()
                     (emptylist-exp))
      (pack-exp (exps)
                (pack-exp (translation-of-pack-exp exps senv)))
      (unpack-exp (vars exp1 body)
                  (nameless-unpack-exp
                   (translation-of exp1 senv)
                   (translation-of body (extend-senv* vars senv))))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (nameless-letrec-exp
                   (translation-of p-body (extend-senv b-var
                                                       (extend-senv p-name senv)))
                   (translation-of letrec-body (extend-senv-rec p-name senv))))
      (else
       (report-invalid-source-expression exp)))))

(define translation-of-pack-exp
  (lambda (exps senv)
    (if (null? exps)
        '()
        (cons (translation-of (car exps) senv)
              (translation-of-pack-exp (cdr exps) senv)))))


; interpreter -------------------------------------------------
; value-of-program : Nameless-program → ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-nameless-env))))))

; value-of : Nameless-exp × Nameless-env → ExpVal
(define value-of
  (lambda (exp nameless-env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 nameless-env))
                      (val2 (value-of exp2 nameless-env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 nameless-env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 nameless-env)))
                (if (expval->bool val1)
                    (value-of exp2 nameless-env)
                    (value-of exp3 nameless-env))))
      (call-exp (rator rand)
                (display "env :")
                (display nameless-env)
                (newline)
                (let ((proc (expval->proc (value-of rator nameless-env)))
                      (arg (value-of rand nameless-env)))
                  (apply-procedure proc arg)))
      (emptylist-exp ()
                     (emptylist-val))
      (pack-exp (exps)
                (value-of-pack-exp exps nameless-env))
      (nameless-var-exp (n)
                        (apply-nameless-env nameless-env n))
      (nameless-let-exp (exp1 body)
                        (let ((val (value-of exp1 nameless-env)))
                          (value-of body
                                    (extend-nameless-env val nameless-env))))
      (nameless-proc-exp (body)
                         (proc-val
                          (procedure body nameless-env)))
      (nameless-unpack-exp (exp1 body)
                           (let ((val (value-of exp1 nameless-env)))
                             (value-of body (extend-nameless-env-with-unpacking val nameless-env))))
      (nameless-letrec-exp (p-body letrec-body)
                           (let ((val (proc-val (procedure p-body nameless-env))))
                             (value-of letrec-body (extend-nameless-env-rec val nameless-env))))

      (else
       (report-invalid-translated-expression exp)))))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (body saved-nameless-env)
                 (value-of body
                           (extend-nameless-env val saved-nameless-env))))))

(define value-of-pack-exp
  (lambda (exps nameless-env)
    (if (null? (cdr exps))
        (value-of (car exps) nameless-env)
        (pair-val (value-of (car exps) nameless-env)
                  (value-of-pack-exp (cdr exps) nameless-env)))))

; grammar -----------------------------------------------------------------------------
(define scanner-spec-nameless
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

(define grammar-nameless
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

    (expression
     ("emptylist")
     emptylist-exp)

    (expression
     ("pack" "(" (separated-list expression ",") ")")
     pack-exp)

    (expression
     ("unpack" (arbno identifier) "=" expression "in" expression)
     unpack-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec"
      identifier "(" identifier ")" "=" expression
      "in" expression)
     letrec-exp)

    (expression ("%nameless-var" number) nameless-var-exp)

    (expression
     ("%let" expression "in" expression)
     nameless-let-exp)

    (expression
     ("%lexproc" expression)
     nameless-proc-exp)

    (expression
     ("%lexunpack" expression)
     nameless-unpack-exp)

    (expression
     ("%letrec" expression)
     nameless-letrec-exp)
    ))


; run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program
     (translation-of-program
      (scan&parse string)))))

; translate : String → Nameless-program
(define translate
  (lambda (string)
    (translation-of-program
     (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-nameless grammar-nameless))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program (translation-of-program pgm)))
                        (sllgen:make-stream-parser scanner-spec-nameless grammar-nameless)))

(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define report-unbound-var
  (lambda (var)
    (eopl:error 'translation-of "unbound variable in code: ~s" var)))

(define report-invalid-source-expression
  (lambda (exp)
    (eopl:error 'value-of
                "Illegal expression in source code: ~s" exp)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-invalid-translated-expression
  (lambda (exp)
    (eopl:error 'value-of
                "Illegal expression in translated code: ~s" exp)))

(define test
  "let l = pack(1, 2, 3, emptylist) in 
    let f = proc(x) -(x,-100) in
      unpack a b c d = l in 
        (f c)")

(define test2
  "let x = 5 in 
    letrec sigma (x) = if zero?(x) 
                       then 0
                       else -((sigma -(x,1)), -(0,x)) in
      (sigma x)")

(define test3
  "let l = pack(1, 2, pack(3, 4, emptylist), emptylist) in 
    unpack a b c d = l in 
      c")

(define test4
  "let x = 1 in x")