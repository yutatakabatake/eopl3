#lang eopl

; if-expのテスト式がbool型でなければ他の式をチェックしない

; type environment ----------------------------------------------
; Tenv= Var → Type
(define-datatype type-environment type-environment?
  (empty-tenv)
  (extend-tenv
   (var identifier?)
   (ty type?)
   (tenv type-environment?))
  (extend-tenv-list
   (vars (list-of identifier?))
   (tys (list-of type?))
   (tenv type-environment?)))

(define apply-tenv
  (lambda (tenv search-var)
    (cases type-environment tenv
      (empty-tenv ()
                  (eopl:error 'apply-tenv "Unbound variable ~s" search-var))
      (extend-tenv (saved-var saved-type saved-tenv)
                   (if (eqv? saved-var search-var)
                       saved-type
                       (apply-tenv saved-tenv search-var)))
      (extend-tenv-list (vars types saved-tenv)
                        (if (null? vars)
                            (apply-tenv saved-tenv search-var)
                            (if (eqv? (car vars) search-var)
                                (car types)
                                (apply-tenv (extend-tenv-list (cdr vars) (cdr types) saved-tenv)
                                            search-var)))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type)
                 (extend-tenv 'v (int-type)
                              (extend-tenv 'i (int-type)
                                           (empty-tenv))))))

;Syntax data types ---------------------------------------------------
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
   (var identifier?)
   (ty type?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (letrec-exp
   (p-result-type type?)
   (proc-name identifier?)
   (bound-var identifier?)
   (b-var-type type?)
   (proc-body expression?)
   (letrec-body expression?))
  (assign-exp
   (var identifier?)
   (exp1 expression?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type type?)
   (result-type type?)))

; type checker -----------------------------------------------------
; type-of-program : Program→ Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (type-of exp1 (init-tenv))))))

; type-of : Exp × Tenv → Type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ((ty1 (type-of exp1 tenv))
                      (ty2 (type-of exp2 tenv)))
                  (check-equal-type! ty1 (int-type) exp1)
                  (check-equal-type! ty2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ((ty1 (type-of exp1 tenv)))
                   (check-equal-type! ty1 (int-type) exp1)
                   (bool-type)))
      (if-exp (exp1 exp2 exp3)
              (let ((ty1 (type-of exp1 tenv)))
                (check-equal-type! ty1 (bool-type) exp1)
                (let ((ty2 (type-of exp2 tenv))
                      (ty3 (type-of exp3 tenv)))
                  (check-equal-type! ty2 ty3 exp)
                  ty2)))
      (let-exp (vars exps body)
               (let ((exps-type (map (lambda (exp) (type-of exp tenv)) exps)))
                 (type-of body
                          (extend-tenv-list vars exps-type tenv))))
      (proc-exp (var var-type body)
                (let ((result-type
                       (type-of body
                                (extend-tenv var var-type tenv))))
                  (proc-type var-type result-type)))
      (call-exp (rator rand)
                (let ((rator-type (type-of rator tenv))
                      (rand-type (type-of rand tenv)))
                  (cases type rator-type
                    (proc-type (arg-type result-type)
                               (begin
                                 (check-equal-type! arg-type rand-type rand)
                                 result-type))
                    (else
                     (report-rator-not-a-proc-type
                      rator-type rator)))))
      (letrec-exp (p-result-type p-name b-var b-var-type
                                 p-body letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv p-name
                                      (proc-type b-var-type p-result-type)
                                      tenv)))
                    (let ((p-body-type
                           (type-of p-body
                                    (extend-tenv b-var b-var-type
                                                 tenv-for-letrec-body))))
                      (check-equal-type!
                       p-body-type p-result-type p-body)
                      (type-of letrec-body tenv-for-letrec-body))))
      (assign-exp (var exp1)
                  (let ((var-type (apply-tenv tenv var))
                        (body-type (type-of exp1 tenv)))
                    (check-equal-type! var-type body-type exp)
                    ; unspecified
                    (int-type))))))


; check-equal-type! : Type × Type × Exp→ Unspecified
; 2つの型が等しいか比較する
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (when (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp))))

; report-unequal-types : Type × Type × Exp→ Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
                "Types didn’t match: ~s != ~a in~%~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

; type-to-external-form : Type→ List
; 型を読みやすいリストに変換する
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type)
                 (list
                  (type-to-external-form arg-type)
                  '->
                  (type-to-external-form result-type))))))

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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    ; proc-exp : proc(a) b
    (expression
     ("proc" "(" identifier ":" type ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression expression ")")
     call-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec"
      type identifier "(" identifier ":" type ")" "=" expression
      "in" expression)
     letrec-exp)

    (expression
     ("set" identifier "=" expression)
     assign-exp)

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" type "->" type ")")
     proc-type)))


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

(define sigma
  "letrec 
    int sigma (x : int) = if zero?(x) 
                          then 0
                          else -((sigma -(x,1)), -(0,x))
    in (sigma 4)")

(define test1
  "proc (x : int) -(x,1)")

(define test2
  "letrec
    int double (x : int) = if zero?(x)
                            then 0
                            else -((double -(x,1)), -2)
    in double")

(define test3
  "proc (f : (bool -> int)) proc (n : int) (f zero?(n))")

(define test4
  "zero?(0)")

(define test5
  "if zero?(0) then 1 else 2")

(define test6
  "if zero?(0) then 1 else proc (x : int) -(x,1)")

(define test7
  "let a = 1
       b = 2
       c = 3 in
       if zero?(a) then (proc (n : int) -(n,1) b) else c")

(define test8
  "let x = 0 in
    set x = 100")

(define test9
  "let x = zero?(0) in
    set x = 100")

(define test10
  "if 1 then 3 else 4")