#lang eopl

; CPS-INをCPS-OUTに変換する
; 変換したCPS-OUTを評価する

; environment ------------------------------------------------------------------
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

;Expressed values -------------------------------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (vars  (list-of identifier?))
   (body tfexp?)
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

; conitnuation -----------------------------------------------------------------
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

; CPS-IN ----------------------------------------------------------------------
(define-datatype program program?
  (a-program
   (exp1 inpexp?)))

(define-datatype inpexp inpexp?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 inpexp?)
   (exp2 inpexp?))
  (zero?-exp
   (exp1 inpexp?))
  (if-exp
   (exp1 inpexp?)
   (exp2 inpexp?)
   (exp3 inpexp?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 inpexp?)
   (body inpexp?))
  (letrec-exp
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (p-bodies (list-of inpexp?))
   (letrec-body inpexp?))
  (proc-exp
   (vars (list-of identifier?))
   (rands (list-of inpexp?)))
  (call-exp
   (rator inpexp?)
   (rands (list-of inpexp?)))
  (sum-exp
   (exps (list-of inpexp?))))

(define scanner-spec-cps-in
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

(define grammar-cps-in
  '((program (inpexp) a-program)
    (inpexp (number) const-exp)

    (inpexp
     ("-" "(" inpexp "," inpexp ")")
     diff-exp)

    (inpexp
     ("+" "(" (separated-list inpexp ",") ")")
     sum-exp)

    (inpexp
     ("zero?" "(" inpexp ")")
     zero?-exp)

    (inpexp
     ("if" inpexp "then" inpexp "else" inpexp)
     if-exp)

    (inpexp
     ("letrec"
      (arbno identifier "(" (arbno identifier) ")"
             "=" inpexp)
      "in"
      inpexp)
     letrec-exp)

    (inpexp (identifier) var-exp)

    (inpexp
     ("let" identifier "=" inpexp "in" inpexp)
     let-exp)

    (inpexp
     ("proc" "(" (arbno identifier) ")" inpexp)
     proc-exp)

    (inpexp
     ("(" inpexp (arbno inpexp) ")")
     call-exp)))

; CPS-OUT ---------------------------------------------------------------------
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

; translate --------------------------------------------------------------------
;translate : String → cps-out-program
(define translate
  (lambda (string)
    (cps-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-cps-in grammar-cps-in))

; cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cps-a-program
                  (cps-of-exps (list exp1)
                               (lambda (new-args)
                                 (simple-exp->exp (car new-args)))))))))

; cps-of-exps : Listof(InpExp) × (Listof(InpExp) → TfExp) → TfExp
; expsの最初の非単純な式を見つけて、その値を変数に束縛して継続を呼び出す
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ((exps exps))
      ; cps-of-rest : Listof(InpExp) → TfExp
      (let ((pos (list-index
                  (lambda (exp)
                    (not (inp-exp-simple? exp)))
                  exps)))
        (if (not pos)
            (builder (map cps-of-simple-exp exps))  ; 全ての式が単純な場合
            (let ((var (fresh-identifier 'var)))    ; 最初の非単純な式を変数に束縛して継続(無名関数)を呼び出す
              (cps-of-exp
               (list-ref exps pos)
               (cps-proc-exp (list var)
                             (cps-of-rest
                              (list-set exps pos (var-exp var)))))))))))

;  cps-of-exp : InpExp × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp k-exp)
    (cases inpexp exp
      (const-exp (num)
                 (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var)
               (make-send-to-cont k-exp (cps-var-exp var)))
      (proc-exp (vars body)
                (make-send-to-cont k-exp
                                   (cps-proc-exp (append vars (list 'k%00))
                                                 (cps-of-exp body (cps-var-exp 'k%00)))))
      (zero?-exp (exp1) (cps-of-zero?-exp exp1 k-exp))
      (diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 k-exp))
      (sum-exp (exps) (cps-of-sum-exp exps k-exp))
      (if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp))
      (let-exp (var exp1 body) (cps-of-let-exp var exp1 body k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp
                   p-names b-varss p-bodies letrec-body k-exp))
      (call-exp (rator rands)
                (cps-of-call-exp rator rands k-exp)))))

; cps-of-simple-exp : InpExp → SimpleExp
; usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases inpexp exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp
                 (cps-of-simple-exp exp1)
                 (cps-of-simple-exp exp2)))
      (zero?-exp (exp1)
                 (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps)
               (cps-sum-exp (map cps-of-simple-exp exps)))
      (else
       (report-invalid-exp-to-cps-of-simple-exp exp)))))


; cps-of-zero?-exp : InpExp × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (make-send-to-cont
                    k-exp
                    (cps-zero?-exp
                     (car simples)))))))

; cps-of-diff-exp : InpExp × InpExp × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps
     (list exp1 exp2)
     (lambda (simples)
       (make-send-to-cont
        k-exp
        (cps-diff-exp
         (car simples)
         (cadr simples)))))))

; cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 k-exp)
                               (cps-of-exp exp3 k-exp))))))

; cps-of-let-exp : Var × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-let-exp
  (lambda (id rhs body k-exp)
    (cps-of-exps (list rhs)
                 (lambda (simples)
                   (cps-let-exp id
                                (car simples)
                                (cps-of-exp body k-exp))))))

; cps-of-letrec-exp : Listof(Var) × Listof(Listof(Var)) × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (cps-letrec-exp
     p-names
     (map
      (lambda (b-vars) (append b-vars (list 'k%00)))
      b-varss)
     (map
      (lambda (p-body)
        (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)
     (cps-of-exp letrec-body k-exp))))

; cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (simples)
                   (cps-call-exp
                    (car simples)
                    (append (cdr simples) (list k-exp)))))))

; cps-of-sum-exp : Listof(InpExp) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont
                    k-exp
                    (cps-sum-exp simples))))))

; make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp)
    (cps-call-exp k-exp (list simple-exp))))

; inp-exp-simple? : InpExp → Bool
(define inp-exp-simple?
  (lambda (exp)
    (cases inpexp exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2)
                (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

; CPS-OUTを実行する ------------------------------------------------------------
(define run
  (lambda (string)
    (value-of-program (translate string))))

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

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body
                             (extend-env* vars args saved-env)
                             cont)))))

(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define list-index
  (lambda (pred lst)
    (if (eqv? '() (list-index-ex pred lst 0))
        #f
        (list-index-ex pred lst 0))))

(define list-index-ex
  (lambda (pred lst n)
    (if (null? lst)
        '()
        (if (pred (car lst))
            n
            (list-index-ex pred (cdr lst) (+ n 1))))))

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

(define list-set
  (lambda (lst n x)
    (if (null? lst)
        '()
        (if (zero? n)
            (cons x (cdr lst))
            (cons (car lst) (list-set (cdr lst) (- n 1) x))))))

(define every?
  (lambda (pred lst)
    (if (pred (car lst))
        (if (eqv? '() (cdr lst))
            #t
            (every? pred (cdr lst)))
        #f)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple inpexp to cps-of-simple-exp: ~s"
                exp)))

(define sigma
  "letrec sigma (x) = if zero?(x) 
                      then 0
                      else +((sigma -(x,1)), x)
    in (sigma 5)")