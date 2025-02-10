#lang eopl

; 型推論

; type environment ----------------------------------------------
; Tenv= Var → Type
(define-datatype type-environment type-environment?
  (empty-tenv)
  (extend-tenv
   (var identifier?)
   (ty type?)
   (tenv type-environment?)))

(define apply-tenv
  (lambda (tenv search-var)
    (cases type-environment tenv
      (empty-tenv ()
                  (eopl:error 'apply-tenv "Unbound variable ~s" search-var))
      (extend-tenv (saved-var saved-type saved-tenv)
                   (if (eqv? saved-var search-var)
                       saved-type
                       (apply-tenv saved-tenv search-var))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type)
                 (extend-tenv 'v (int-type)
                              (extend-tenv 'i (int-type)
                                           (empty-tenv))))))

;Syntax data types ---------------------------------------------------
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
   (otype optional-type?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (letrec-exp
   (p-result-otype optional-type?)
   (proc-name identifier?)
   (bound-var identifier?)
   (b-var-otype optional-type?)
   (proc-body expression?)
   (letrec-body expression?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type type?)
   (result-type type?))
  (tvar-type
   (serial-number number?)))

(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type (t1 t2) #t)
      (else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type
                        "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-types
                        "Not a proc type: ~s" ty)))))

(define-datatype optional-type optional-type?
  (no-type)
  (a-type
   (ty type?)))

; optype->type : OptionalType → Type
(define otype->type
  (lambda (otype)
    (cases optional-type otype
      (no-type () (fresh-tvar-type))
      (a-type (ty) ty))))

; fresh-tvar-type : () → Type
(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))

;  Answer= Type × Subst
(define-datatype answer answer?
  (an-answer
   (ty type?)
   (subst substitution?)))

; substitution -----------------------------------------------------
; empty-subst : ()→ Subst
(define empty-subst (lambda () '()))

; extend-subst : Subst × Tvar × Type → Subst
; usage: tvar not already bound in subst.
(define extend-subst
  (lambda (subst tvar ty)
    (cons
     (cons tvar ty)
     (map (lambda (p)
            (let ((oldlhs (car p))
                  (oldrhs (cdr p)))
              (cons
               oldlhs
               (apply-one-subst oldrhs tvar ty))))
          subst))))

(define pair-of
  (lambda (pred1 pred2)
    (lambda (val)
      (and (pair? val) (pred1 (car val)) (pred2 (cdr val))))))

(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type (serial-number) #t)
      (else #f))))

(define substitution?
  (list-of (pair-of tvar-type? type?)))

; apply-one-subst : Type × Tvar × Type → Type
; 型ty0に出現する型変数tvarをty1で置き換える t0[tv = t1]
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (apply-one-subst arg-type tvar ty1)
                  (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type : Type × Subst → Type
; 全ての型変数を代入する
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1 subst)
                  (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
                 (let ((tmp (assoc ty subst)))
                   (if tmp
                       (cdr tmp)
                       ty))))))

; type inference -----------------------------------------------------
; type-of-program : Program → Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cases answer (type-of exp1
                                        (init-tenv) (empty-subst))
                   (an-answer (ty subst)
                              (apply-subst-to-type ty subst)))))))

; type-of : Exp × Tenv × Subst → Answer
(define type-of
  (lambda (exp tenv subst)
    (cases expression exp
      (const-exp (num) (an-answer (int-type) subst))
      (zero?-exp (exp1)
                 (cases answer (type-of exp1 tenv subst)
                   (an-answer (ty1 subst1)
                              (let ((subst2
                                     (unifier ty1 (int-type) subst1 exp)))
                                (an-answer (bool-type) subst2)))))
      (diff-exp (exp1 exp2)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (ty1 subst1)
                             (let ((subst1
                                    (unifier ty1 (int-type) subst1 exp1)))
                               (cases answer (type-of exp2 tenv subst1)
                                 (an-answer (ty2 subst2)
                                            (let ((subst2
                                                   (unifier ty2 (int-type)
                                                            subst2 exp2)))
                                              (an-answer (int-type) subst2))))))))
      (if-exp (exp1 exp2 exp3)
              (cases answer (type-of exp1 tenv subst)
                (an-answer (ty1 subst)
                           (let ((subst
                                  (unifier ty1 (bool-type) subst exp1)))
                             (cases answer (type-of exp2 tenv subst)
                               (an-answer (ty2 subst)
                                          (cases answer (type-of exp3 tenv subst)
                                            (an-answer (ty3 subst)
                                                       (let ((subst
                                                              (unifier ty2 ty3 subst exp)))
                                                         (an-answer ty2 subst))))))))))
      (var-exp (var)
               (an-answer (apply-tenv tenv var) subst))
      (let-exp (var exp1 body)
               (cases answer (type-of exp1 tenv subst)
                 (an-answer (exp1-type subst)
                            (type-of body
                                     (extend-tenv var exp1-type tenv)
                                     subst))))
      (proc-exp (var otype body)
                (let ((var-type (otype->type otype)))
                  (cases answer (type-of body
                                         (extend-tenv var var-type tenv)
                                         subst)
                    (an-answer (body-type subst)
                               (an-answer
                                (proc-type var-type body-type)
                                subst)))))
      (call-exp (rator rand)
                (let ((result-type (fresh-tvar-type)))
                  (cases answer (type-of rator tenv subst)
                    (an-answer (rator-type subst)
                               (cases answer (type-of rand tenv subst)
                                 (an-answer (rand-type subst)
                                            (let ((subst
                                                   (unifier
                                                    rator-type
                                                    (proc-type
                                                     rand-type result-type)
                                                    subst
                                                    exp)))
                                              (an-answer result-type subst))))))))
      (letrec-exp (p-result-otype p-name b-var b-var-otype
                                  p-body letrec-body)
                  (let ((p-result-type (otype->type p-result-otype))
                        (p-var-type (otype->type b-var-otype)))
                    (let ((tenv-for-letrec-body
                           (extend-tenv p-name
                                        (proc-type p-var-type p-result-type)
                                        tenv)))
                      (cases answer (type-of p-body
                                             (extend-tenv b-var p-var-type
                                                          tenv-for-letrec-body)
                                             subst)
                        (an-answer (p-body-type subst)
                                   (let ((subst
                                          (unifier p-body-type p-result-type
                                                   subst p-body)))
                                     (type-of letrec-body
                                              tenv-for-letrec-body
                                              subst))))))))))


; unifier : Type × Type × Subst × Exp → Subst
(define unifier
  (lambda (ty1 ty2 subst exp)
    (let ((ty1 (apply-subst-to-type ty1 subst))
          (ty2 (apply-subst-to-type ty2 subst)))
      (cond
        ; ty1とty2の型が同じならsubstに保持しない
        ((equal? ty1 ty2) subst)
        ; どちらかが型変数ならno-occurerenceチェックをしてからsubstに追加する
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (let ((subst (unifier
                       (proc-type->arg-type ty1)
                       (proc-type->arg-type ty2)
                       subst exp)))
           (let ((subst (unifier
                         (proc-type->result-type ty1)
                         (proc-type->result-type ty2)
                         subst exp)))
             subst)))
        ;  ty1とty2の型が違う場合は型エラー
        (else (report-unification-failure ty1 ty2 exp))))))

; no-occurrence? : Tvar × Type → Bool
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
                 (and
                  (no-occurrence? tvar arg-type)
                  (no-occurrence? tvar result-type)))
      (tvar-type (serial-number) (not (equal? tvar ty))))))

; type-to-external-form : Type → List
; エラーメッセージの表示用
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type)
                 (list
                  (type-to-external-form arg-type)
                  '->
                  (type-to-external-form result-type)))
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "ty"
                   (number->string serial-number)))))))

; --------------------------------------------------------------------
; TvarTypeSym = a symbol ending with a digit
; A-list= Listof(Pair(TvarTypeSym,TvarTypeSym))

; equal-up-to-gensyms? : S-exp × S-exp → Bool
(define equal-up-to-gensyms?
  (lambda (sexp1 sexp2)
    (equal?
     (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
     (apply-subst-to-sexp (canonical-subst sexp2) sexp2))))

; canonical-subst : S-exp→ A-list
(define canonical-subst
  (lambda (sexp)
    ; loop : S-exp × A-list → A-list
    (let loop ((sexp sexp) (table '()))
      (cond
        ((null? sexp) table)
        ((tvar-type-sym? sexp)
         (cond
           ((assq sexp table) table)
           (else
            (cons
             (cons sexp (ctr->ty (length table)))
             table))))
        ((pair? sexp)
         (loop (cdr sexp)
               (loop (car sexp) table)))
        (else table)))))

; tvar-type-sym? : Sym → Bool
(define tvar-type-sym?
  (lambda (sym)
    (and (symbol? sym)
         (char-numeric? (car (reverse (symbol->list sym)))))))

; symbol->list : Sym → List
(define symbol->list
  (lambda (x)
    (string->list (symbol->string x))))

; apply-subst-to-sexp : A-list × S-exp → S-exp
(define apply-subst-to-sexp
  (lambda (subst sexp)
    (cond
      ((null? sexp) sexp)
      ((tvar-type-sym? sexp)
       (cdr (assq sexp subst)))
      ((pair? sexp)
       (cons
        (apply-subst-to-sexp subst (car sexp))
        (apply-subst-to-sexp subst (cdr sexp))))
      (else sexp))))

; ctr->ty : N → Sym
(define ctr->ty
  (lambda (n)
    (string->symbol
     (string-append "tvar" (number->string n)))))

(define report-unification-failure
  (lambda (ty1 ty2 exp)
    (eopl:error 'unification-failure
                "Type mismatch: ~s doesn't match ~s in ~s~%"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-no-occurence!
                "Can't unify: type variable ~s occurs in type ~s in expression ~s~%"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

(define scanner-spec
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

(define grammar
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
     ("proc" "(" identifier ":" optional-type ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression expression ")")
     call-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec"
      optional-type identifier "(" identifier ":" optional-type ")" "=" expression
      "in" expression)
     letrec-exp)

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" type "->" type ")")
     proc-type)

    (type
     ("%tver-type" number)
     tvar-type)

    (optional-type
     ("?")
     no-type)

    (optional-type
     (type)
     a-type)))


(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

;type-check : String → Type
(define type-check
  (lambda (string)
    (type-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'type-of-expression
                "Rator not a proc type:~%~s~%had rator type ~s"
                rator
                (type-to-external-form rator-type))))

(define test1
  "proc (x : int) -(x,1)")

(define test2
  "letrec
    int double (x : int) = if zero?(x)
                            then 0
                            else -((double -(x,1)), -2)
    in double")

(define test3
  "proc (f : ?) proc (n : ?) (f zero?(n))")

(define test4
  "letrec
    ? foo (x : ?) = if zero?(x)
                    then 1
                    else -(x, (foo -(x,1)))
    in (foo 5)")

(define test5
  "letrec
        ? even (x : int) = if zero?(x) then 1 else (odd -(x,1))
        bool odd (x : ?) = if zero?(x) then 0 else (even -(x,1))
    in (odd 13)")