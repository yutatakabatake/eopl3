#lang eopl

; CPS-INからCPS-OUTに変換するtranslator

; CPS-IN
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


;translate : String → cps-out-program
(define translate
  (lambda (string)
    (cps-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-cps-in grammar-cps-in))


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

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple inpexp to cps-of-simple-exp: ~s"
                exp)))

(define sigma
  "letrec sigma (x) = if zero?(x) 
                      then 0
                      else -((sigma -(x,1)), -(0,x))
    in (sigma 10)")