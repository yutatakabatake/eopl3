#lang eopl

; CPS-OUTを評価するインタプリタ

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env*
   (vars (list-of identifier?))
   (vals (list-of expval?))
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (p-bodies (list-of tfexp?))
   (env environment?)))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env* (saved-vars saved-vals saved-env)
                   (if (null? saved-vars)
                       (apply-env saved-env search-var)
                       (if (eqv? (car saved-vars) search-var)
                           (car saved-vals)
                           (apply-env (extend-env* (cdr saved-vars) (cdr saved-vals) saved-env) search-var))))
      (extend-env-rec* (p-names b-varss p-bodies saved-env)
                       (if (null? p-names)
                           (apply-env saved-env search-var)
                           (if (eqv? search-var (car p-names))
                               (proc-val (procedure (car b-varss) (car p-bodies) env))
                               (apply-env (extend-env-rec* (cdr p-names) (cdr b-varss) (cdr p-bodies) saved-env) search-var)))))))

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
   (vars  (list-of identifier?))
   (body tfexp?)
   (saved-env environment?)))

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


; CPS-OUT
(define-datatype cps-out-program cps-out-program?
  (cps-a-program
   (exp1 tfexp?)))

(define-datatype simple-exp simple-exp?
  (cps-const-exp
   (num number?))
  (cps-var-exp
   (var identifier?))
  (cps-diff-exp
   (simple1 simple-exp?)
   (simple2 simple-exp?))
  (cps-zero?-exp
   (simple1 simple-exp?))
  (cps-proc-exp
   (vars (list-of identifier?))
   (body tfexp?))
  (cps-sum-exp
   (simple-exps (list-of simple-exp?))))

(define-datatype tfexp tfexp?
  (simple-exp->exp
   (simple-exp1 simple-exp?))
  (cps-let-exp
   (var identifier?)
   (simple1 simple-exp?)
   (body tfexp?))
  (cps-letrec-exp
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (p-bodies (list-of tfexp?))
   (body tfexp?))
  (cps-if-exp
   (simple1 simple-exp?)
   (body1 tfexp?)
   (body2 tfexp?))
  (cps-call-exp
   (rator simple-exp?)
   (rands (list-of simple-exp?))))

(define value-of-program
  (lambda (pgm)
    (cases cps-out-program pgm
      (cps-a-program (exp1)
                     (value-of/k exp1 (init-env) (end-cont))))))

; value-of-simple-exp : SimpleExp × Env -> FinalAnswer
(define value-of-simple-exp
  (lambda (simple env)
    (cases simple-exp simple
      (cps-const-exp (num) (num-val num))
      (cps-var-exp (var) (apply-env env var))
      (cps-diff-exp (simple1 simple2)
                    (let ((val1
                           (expval->num
                            (value-of-simple-exp simple1 env)))
                          (val2
                           (expval->num
                            (value-of-simple-exp simple2 env))))
                      (num-val
                       (- val1 val2))))
      (cps-zero?-exp (simple1)
                     (bool-val
                      (zero?
                       (expval->num
                        (value-of-simple-exp simple1 env)))))
      (cps-proc-exp (vars body)
                    (proc-val
                     (procedure vars body env)))
      (cps-sum-exp (simple-exps)
                   (let ((vals (map (lambda (simple-exp) (value-of-simple-exp simple-exp env)) simple-exps)))
                     (let ((nums (map expval->num vals)))
                       (num-val
                        (apply + nums))))))))

; value-of/k : TfExp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases tfexp exp
      (simple-exp->exp (simple-exp1)
                       (apply-cont cont
                                   (value-of-simple-exp simple-exp1 env)))
      (cps-let-exp (var rhs body)
                   (let ((val (value-of-simple-exp rhs env)))
                     (value-of/k body
                                 (extend-env* (list var) (list val) env)
                                 cont)))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (value-of/k letrec-body
                                  (extend-env-rec* p-names b-varss p-bodies env)
                                  cont))
      (cps-if-exp (simple1 body1 body2)
                  (if (expval->bool (value-of-simple-exp simple1 env))
                      (value-of/k body1 env cont)
                      (value-of/k body2 env cont)))
      (cps-call-exp (rator rands)
                    (let ((rator-proc
                           (expval->proc
                            (value-of-simple-exp rator env)))
                          (rand-vals
                           (map
                            (lambda (simple)
                              (value-of-simple-exp simple env)) rands)))
                      (apply-procedure/k rator-proc rand-vals cont))))))


; 継続のデータ型
(define-datatype continuation continuation?
  (end-cont))

; FinalAnswer = ExpVal
; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin
                  (eopl:printf "End of computation.~%")
                  val)))))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body
                             (extend-env* vars args saved-env)
                             cont)))))



(define scanner-spec-cps-out
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

(define grammar-cps-out
  '((cps-out-program (tfexp) cps-a-program)

    (simple-exp (number) cps-const-exp)
    (simple-exp (identifier) cps-var-exp)

    ; diff-exp : -(a,b) -> (- a b)
    (simple-exp
     ("-" "(" simple-exp "," simple-exp ")")
     cps-diff-exp)

    ; zero?-exp : zero?(a)
    (simple-exp
     ("zero?" "(" simple-exp ")")
     cps-zero?-exp)

    ; proc-exp : proc(a) b
    (simple-exp
     ("proc" "(" (separated-list identifier ",") ")" tfexp)
     cps-proc-exp)

    ; add-exp : +(a,b,...)
    (simple-exp
     ("+" "("  (separated-list simple-exp ",") ")")
     cps-sum-exp)

    (tfexp
     (simple-exp)
     simple-exp->exp)

    ; let-exp : let y = a in b
    (tfexp
     ("let" identifier "=" simple-exp "in" tfexp)
     cps-let-exp)

    ; letrec-exp : letrec(a) = b in c
    (tfexp
     ("letrec"
      (arbno identifier "(" identifier ")" "=" tfexp)
      "in" tfexp)
     cps-letrec-exp)

    ; if-exp : if a then b else c
    (tfexp
     ("if" simple-exp "then" tfexp "else" tfexp)
     cps-if-exp)

    ; call-exp : (a b)
    (tfexp
     ("(" simple-exp (arbno simple-exp) ")")
     cps-call-exp)))

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
  (sllgen:make-string-parser scanner-spec-cps-out grammar-cps-out))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-cps-out grammar-cps-out)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))