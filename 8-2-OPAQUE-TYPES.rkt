#lang eopl
; transparent type, opaque type, qualified type references

; environment --------------------------------------------------------
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
  (extend-env-with-module
   (m-name symbol?)
   (m-val typed-module?)
   (saved-env environment?)))

(define-datatype typed-module typed-module?
  (simple-module
   (bindings environment?)))

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
      (extend-env-with-module (m-name m-val saved-env)
                              (apply-env saved-env search-var)))))

; lookup-qualified-var-in-env : Sym × Sym × Env → ExpVal
(define lookup-qualified-var-in-env
  (lambda (m-name var-name env)
    (let ((m-val (lookup-module-name-in-env m-name env)))
      (cases typed-module m-val
        (simple-module (bindings)
                       (apply-env bindings var-name))))))

; lookup-module-name-in-env : Sym * Env -> Typed-Module
(define lookup-module-name-in-env
  (lambda (m-name env)
    (cases environment env
      (empty-env ()
                 (report-no-module-binding-found m-name))
      (extend-env (var val saved-env)
                  (lookup-module-name-in-env m-name saved-env))
      (extend-env-rec (p-name b-var body saved-env)
                      (lookup-module-name-in-env m-name saved-env))
      (extend-env-with-module (saved-m-name m-val saved-env)
                              (if (eqv? saved-m-name m-name)
                                  m-val ;typed-module
                                  (lookup-module-name-in-env m-name saved-env))))))

; type environment ---------------------------------------------------
; Tenv = Var → Type
(define-datatype type-environment type-environment?
  (empty-tenv)
  (extend-tenv
   (var identifier?)
   (ty type?)
   (tenv type-environment?))
  (extend-tenv-with-module
   (name symbol?)
   (interface interface?)
   (saved-tenv type-environment?))
  (extend-tenv-with-type ; named type, qualified typeをexpanded typeとして保存
   (name symbol?)
   (type type?)
   (saved-tenv type-environment?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type type?)
   (result-type type?))
  (named-type
   (name symbol?))
  (qualified-type
   (m-name symbol?)
   (t-name symbol?)))

(define apply-tenv
  (lambda (tenv search-var)
    (cases type-environment tenv
      (empty-tenv ()
                  (eopl:error 'apply-tenv "Unbound variable ~s" search-var))
      (extend-tenv (saved-var saved-type saved-tenv)
                   (if (eqv? saved-var search-var)
                       saved-type
                       (apply-tenv saved-tenv search-var)))
      (extend-tenv-with-module (name interface saved-tenv)
                               (apply-tenv saved-tenv search-var))
      (extend-tenv-with-type (name saved-type saved-env)
                             (apply-tenv saved-env search-var)))))

; lookup-qualified-var-in-tenv : Sym × Sym × Tenv → Type
(define lookup-qualified-var-in-tenv
  (lambda (m-name var-name tenv)
    (let ((iface (lookup-module-name-in-tenv tenv m-name)))
      (cases interface iface
        (simple-iface (decls)
                      (lookup-variable-name-in-decls var-name decls))))))

(define lookup-module-name-in-tenv
  (lambda (tenv search-m-name)
    (cases type-environment tenv
      (empty-tenv ()
                  (report-no-module-binding-found search-m-name))
      (extend-tenv (m-name iface saved-tenv)
                   (lookup-module-name-in-tenv saved-tenv search-m-name))
      (extend-tenv-with-module (m-name iface saved-tenv)
                               (if (eqv? m-name search-m-name)
                                   iface
                                   (lookup-module-name-in-tenv saved-tenv search-m-name)))
      (extend-tenv-with-type (t-name type saved-tenv)
                             (lookup-module-name-in-tenv saved-tenv search-m-name)))))

(define lookup-variable-name-in-decls
  (lambda (var-name decls)
    (if (null? decls)
        (report-no-qualified-variable-found var-name)
        (let* ((decl (car decls))
               (var (decl->name decl))
               (type (decl->type decl)))
          (if (eqv? var var-name)
              type
              (lookup-variable-name-in-decls var-name (cdr decls)))))))

; extend-tenv-with-decl : Decl × Tenv → Tenv
; declを型環境に追加する
; invariantsをチェックするための型環境を作る
(define extend-tenv-with-decl
  (lambda (decl1 tenv)
    (cases decl decl1
      (val-decl (name ty) tenv)
      (transparent-type-decl (name ty)
                             (extend-tenv-with-type
                              name
                              (expand-type ty tenv)
                              tenv))
      (opaque-type-decl (name)
                        (extend-tenv-with-type
                         name
                         ;  declsの中の型環境ではqualified type
                         (qualified-type (fresh-module-name '%unknown) name)
                         tenv)))))

(define fresh-module-name
  (let ((sn 0))
    (lambda (module-name)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string module-name)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))
; expressed value ----------------------------------------------------
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
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))


;Syntax data types ---------------------------------------------------
(define-datatype program program?
  (a-program
   (m-defs (list-of module-defn?))
   (exp1 expression?)))

(define-datatype module-definition module-defn?
  (a-module-definition
   (m-name identifier?)
   (expected-iface interface?)
   (m-body module-body?)))

(define-datatype interface interface?
  (simple-iface
   (decls (list-of decl?))))

(define-datatype decl decl?
  (val-decl
   (var identifier?)
   (ty type?))
  (opaque-type-decl
   (t-name symbol?))
  (transparent-type-decl
   (t-name symbol?)
   (ty type?)))

(define val-decl?
  (lambda (decl1)
    (cases decl decl1
      (val-decl (var ty)
                #t)
      (else
       #f))))

(define transparent-type-decl?
  (lambda (decl1)
    (cases decl decl1
      (transparent-type-decl (t-name ty)
                             #t)
      (else #f))))

(define opaque-type-decl?
  (lambda (decl1)
    (cases decl decl1
      (opaque-type-decl (t-name)
                        #t)
      (else #f))))

(define decl->name
  (lambda (decl1)
    (cases decl decl1
      (val-decl (var ty)
                var)
      (opaque-type-decl (t-name)
                        t-name)
      (transparent-type-decl (t-name ty)
                             t-name))))

(define decl->type
  (lambda (decl1)
    (cases decl decl1
      (val-decl (var ty)
                ty)
      (opaque-type-decl (t-name)
                        (eopl:error 'decl->type "can't take type of opaque type declaration ~s" decl1))
      (transparent-type-decl (t-name ty)
                             ty))))

(define-datatype module-body module-body?
  (defns-module-body
    (defns (list-of definition?))))

(define-datatype definition definition?
  (val-defn
   (var-name identifier?)
   (exp1 expression?))
  (type-defn
   (name symbol?)
   (ty type?)))

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
  (qualified-var-exp
   (m-name identifier?)
   (var-name identifier?)))

; interpreter --------------------------------------------------------
; value-of-program : Program→ ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (m-defns body)
                 (value-of body
                           (add-module-defns-to-env m-defns (empty-env)))))))

; add-module-defns-to-env : Listof(Defn) × Env → Env
(define add-module-defns-to-env
  (lambda (defns env)
    (if (null? defns)
        env
        (cases module-definition (car defns)
          (a-module-definition (m-name iface m-body)
                               (add-module-defns-to-env
                                (cdr defns)
                                (extend-env-with-module
                                 m-name
                                 (value-of-module-body m-body env)
                                 env)))))))

; value-of-module-body : ModuleBody × Env → TypedModule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-module
         (defns-to-env defns env))))))

; defns-to-env : Listof(Defn) × Env → Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases definition (car defns)
          (val-defn (var exp)
                    (let ((val (value-of exp env)))
                      (let ((new-env (extend-env var val env)))
                        (extend-env var val
                                    (defns-to-env
                                      (cdr defns) new-env)))))
          (type-defn (type-name type)
                     (defns-to-env (cdr defns) env))))))

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
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (proc-exp (var ty body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg)))
      (letrec-exp (p-result-type proc-name bound-var b-var-type proc-body letrec-body)
                  (value-of letrec-body (extend-env-rec proc-name bound-var proc-body env)))
      (qualified-var-exp (m-name var-name)
                         (lookup-qualified-var-in-env m-name var-name env)))))

(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var val saved-env))))))


; checker ------------------------------------------------------------
; module bodyがinterfaceでの宣言を満たすかのチェック

; type-of-program : Program → Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (module-defns body)
                 (type-of body
                          (add-module-defns-to-tenv module-defns
                                                    (empty-tenv)))))))

; add-module-defns-to-tenv : Listof(ModuleDefn) × Tenv → Tenv
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
          (a-module-definition (m-name expected-iface m-body)
                               (let ((actual-iface (interface-of m-body tenv))) ; インタフェースが持つ型はexpandされる
                                 (if (<:-iface actual-iface expected-iface tenv)
                                     (let ((new-tenv
                                            (extend-tenv-with-module
                                             m-name
                                             (expand-iface
                                              m-name expected-iface tenv) ; インタフェースが持つ型はexpandされる
                                             tenv)))
                                       (add-module-defns-to-tenv
                                        (cdr defns) new-tenv))
                                     (report-module-doesnt-satisfy-iface
                                      m-name expected-iface actual-iface))))))))

; interface-of : ModuleBody × Tenv → Iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface
         (defns-to-decls defns tenv))))))

; defns-to-decls : Listof(Defn) × Tenv → Listof(Decl)
; インタフェースの定義とボディの宣言の型を比較するためにdefnをdeclに変換する
; 比較する時の型はexpandされていなければならない
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases definition (car defns)
          (val-defn (var-name exp)
                    (let ((ty (type-of exp tenv)))
                      (let ((new-env (extend-tenv var-name ty tenv))) ; tyはtype-ofでexpandされている保証がある
                        (cons
                         (val-decl var-name ty)
                         (defns-to-decls (cdr defns) new-env)))))
          (type-defn (name ty)
                     (let ((new-env
                            (extend-tenv-with-type
                             name
                             (expand-type ty tenv) ; 型環境に追加する時はexpandする
                             tenv)))
                       (cons
                        (transparent-type-decl name ty) ; bodyでは全ての型はtransparentである
                        (defns-to-decls (cdr defns) new-env))))))))

; <:-iface : Iface × Iface × Tenv → Bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases interface iface1
      (simple-iface (decls1)
                    (cases interface iface2
                      (simple-iface (decls2)
                                    (<:-decls decls1 decls2 tenv)))))))

; <:-decls : Listof(Decl) × Listof(Decl) × Tenv → Bool
(define <:-decls
  (lambda (decls1 decls2 tenv)
    (cond
      ((null? decls2) #t)
      ((null? decls1) #f)
      (else
       (let ((name1 (decl->name (car decls1)))
             (name2 (decl->name (car decls2))))
         (if (eqv? name1 name2)
             (and
              (<:-decl
               (car decls1) (car decls2) tenv)
              (<:-decls
               (cdr decls1) (cdr decls2)
               (extend-tenv-with-decl
                (car decls1) tenv))) ; bodyの方のdeclを型環境に追加する　bodyの下の定義に影響するから let*スコープ
             (<:-decls
              (cdr decls1) decls2
              (extend-tenv-with-decl
               (car decls1) tenv))))))))

; <:-decl : Decl × Decl × Tenv → Bool
(define <:-decl
  (lambda (decl1 decl2 tenv)
    (or
     (and
      (val-decl? decl1)
      (val-decl? decl2)
      (equiv-type?
       (decl->type decl1)
       (decl->type decl2) tenv))
     (and
      (transparent-type-decl? decl1)
      (transparent-type-decl? decl2)
      (equiv-type?
       (decl->type decl1)
       (decl->type decl2) tenv))
     (and ; interfaceではopaqueで宣言してbodyではtransparentのように書く
      (transparent-type-decl? decl1)
      (opaque-type-decl? decl2))
     (and
      (opaque-type-decl? decl1)
      (opaque-type-decl? decl2)))))

; equiv-type? : Type × Type × Tenv → Bool
(define equiv-type?
  (lambda (ty1 ty2 tenv)
    (equal?
     (expand-type ty1 tenv)
     (expand-type ty2 tenv))))

; expand-iface : Sym × Iface × Tenv → Iface
(define expand-iface
  (lambda (m-name iface tenv)
    (cases interface iface
      (simple-iface (decls)
                    (simple-iface
                     (expand-decls m-name decls tenv))))))

; expand-decls : Sym × Listof(Decl) × Tenv → Listof(Decl)
; インタフェースで定義した型を全てexpandして型環境に追加する
(define expand-decls
  (lambda (m-name decls internal-tenv)
    (if (null? decls)
        '()
        (cases decl (car decls)
          (opaque-type-decl (t-name)
                            (let ((expanded-type
                                   (qualified-type m-name t-name)))
                              (let ((new-env
                                     (extend-tenv-with-type
                                      t-name expanded-type internal-tenv)))
                                (cons
                                 (transparent-type-decl t-name expanded-type) ; qualified typeが型環境から探せるように
                                 (expand-decls
                                  m-name (cdr decls) new-env))))) ; let*スコープ
          (transparent-type-decl (t-name ty)
                                 (let ((expanded-type
                                        (expand-type ty internal-tenv)))
                                   (let ((new-env
                                          (extend-tenv-with-type
                                           t-name expanded-type internal-tenv)))
                                     (cons
                                      (transparent-type-decl t-name expanded-type)
                                      (expand-decls
                                       m-name (cdr decls) new-env))))) ; let*スコープ
          (val-decl (var-name ty)
                    (let ((expanded-type
                           (expand-type ty internal-tenv)))
                      (cons
                       (val-decl var-name expanded-type)
                       (expand-decls
                        m-name (cdr decls) internal-tenv))))))))

; expand-type : Type × Tenv → ExpandedType
(define expand-type
  (lambda (ty tenv)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (expand-type arg-type tenv)
                  (expand-type result-type tenv)))
      (named-type (name)
                  (lookup-type-name-in-tenv tenv name))
      (qualified-type (m-name t-name)
                      (lookup-qualified-type-in-tenv m-name t-name tenv)))))

(define lookup-type-name-in-tenv
  (lambda (tenv search-name)
    (cases type-environment tenv
      (empty-tenv ()
                  (raise-tenv-lookup-failure-error 'type search-name tenv))
      (extend-tenv (var ty saved-tenv)
                   (lookup-type-name-in-tenv saved-tenv search-name))
      (extend-tenv-with-module (name iface saved-tenv)
                               (lookup-type-name-in-tenv saved-tenv search-name))
      (extend-tenv-with-type (name type saved-tenv)
                             (if (eqv? name search-name)
                                 type
                                 (lookup-type-name-in-tenv saved-tenv search-name))))))

(define raise-tenv-lookup-failure-error
  (lambda (kind var tenv)
    (eopl:pretty-print
     (list 'tenv-lookup-failure: (list 'missing: kind var) 'in:
           tenv))
    (eopl:error 'lookup-variable-name-in-tenv)))


(define lookup-qualified-type-in-tenv
  (lambda (m-name t-name tenv)
    (let ((iface (lookup-module-name-in-tenv tenv m-name)))
      (cases interface iface
        (simple-iface (decls)
                      ;; this is not right, because it doesn't distinguish
                      ;; between type and variable declarations.  Exercise: fix
                      ;; this so that it raises an error if t-name is declared
                      ;; in a val-decl.
                      (lookup-variable-name-in-decls t-name decls))))))

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
              (let ((ty1 (type-of exp1 tenv))
                    (ty2 (type-of exp2 tenv))
                    (ty3 (type-of exp3 tenv)))
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))
      (let-exp (var exp1 body)
               (let ((exp1-type (type-of exp1 tenv)))
                 (type-of body
                          (extend-tenv var (expand-type exp1-type tenv) tenv))))
      (proc-exp (var var-type body)
                (let ((result-type
                       (type-of body
                                (extend-tenv var (expand-type var-type tenv) tenv))))
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
      (letrec-exp (p-result-type p-name b-var b-var-type p-body letrec-body)
                  (let ((tenv-for-letrec-body ; letrec-bodyの型を決めるときの型環境
                         (extend-tenv p-name
                                      (expand-type (proc-type b-var-type p-result-type) tenv)
                                      tenv)))
                    (let ((p-body-type
                           (type-of p-body
                                    (extend-tenv b-var (expand-type b-var-type tenv) ; p-bodyの型を決めるのにtenv-for-letrec-bodyは使えない
                                                 tenv-for-letrec-body))))
                      (check-equal-type!
                       p-body-type p-result-type p-body) ; p-result-type はexpand-typeを使わないといけない　p-result-typeがqualified-typeだったら間違いが起こる
                      (type-of letrec-body tenv-for-letrec-body))))
      (qualified-var-exp (m-name var-name)
                         (lookup-qualified-var-in-tenv m-name var-name tenv)))))


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
                  (type-to-external-form result-type)))
      (named-type (name)
                  name)
      (qualified-type (m-name t-name)
                      (list 'from m-name 'take t-name)))))

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
  '((program ((arbno module-definition) expression) a-program)

    (module-definition
     ("module" identifier "interface" iface "body" module-body)
     a-module-definition)

    (iface
     ("[" (arbno decl) "]")
     simple-iface)

    (decl
     (identifier ":" type)
     val-decl)

    (decl
     ("opaque" identifier)
     opaque-type-decl)

    (decl
     ("transparent" identifier "=" type)
     transparent-type-decl)

    (module-body
     ("[" (arbno definition) "]")
     defns-module-body)

    (definition
      (identifier "=" expression)
      val-defn)

    (definition
      ("type" identifier "=" type)
      type-defn)

    (expression (number) const-exp)
    (expression (identifier) var-exp)

    ; zero?-exp : zero?(a)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    ; diff-exp : -(a,b)
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

    ; proc-exp : proc(a : type) b
    (expression
     ("proc" "(" identifier ":" type ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression expression ")")
     call-exp)

    ; letrec-exp : letrec(a : type) = b in c
    (expression
     ("letrec"
      type identifier "(" identifier ":" type ")" "=" expression
      "in" expression)
     letrec-exp)

    (expression
     ("from" identifier "take" identifier)
     qualified-var-exp)

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
     (identifier)
     named-type)

    (type
     ("from" identifier "take" identifier)
     qualified-type)

    ))


;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;type-check : String → Type
(define type-check
  (lambda (string)
    (type-to-external-form (type-of-program (scan&parse string)))))

(define check-run
  (lambda (string)
    (display (type-check string))
    (display " : ")
    (run string)))
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec grammar)))

(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-no-module-binding-found
  (lambda (m-name)
    (eopl:error 'lookup-module-name-in-env "No module binding for ~s" m-name)))

(define report-no-qualified-variable-found
  (lambda (var-name)
    (eopl:error 'lookup-variable-name-in-decls "No qualified variable found for ~s" var-name)))

(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-iface actual-iface)
    (eopl:error 'add-module-defns-to-tenv
                "Module ~s doesn't satisfy its interface. Expected: ~s, Actual: ~s" m-name expected-iface actual-iface)))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'type-of-expression
                "Rator not a proc type:~%~s~%had rator type ~s"
                rator
                (type-to-external-form rator-type))))


(define test6
  "module m1
   interface
   [ a : int ]
   body
   [ a = letrec int sigma (x : int) = if zero?(x) 
                      then 0
                      else -((sigma -(x,1)), -(0,x))
          in (sigma 10)]
    from m1 take a")

(define ex8.6
  "module m1
    interface
    [transparent t = int
     z : t
     s : (t -> t)
     is-z? : (t -> bool)]
    body
    [type t = int
     z = 33
     s = proc (x : t) -(x,-1)
     is-z? = proc (x : t) zero?(-(x,z))]
   proc (x : from m1 take t)
     (from m1 take is-z? -(x,0))")

(define ex8.7
  "module m1
    interface
    [opaque t
     z : t
     s : (t -> t)
     is-z? : (t -> bool)]
    body
    [type t = int
     z = 33
     s = proc (x : t) -(x,-1)
     is-z? = proc (x : t) zero?(-(x,z))]
     proc (x : from m1 take t)
  (from m1 take is-z? x)")

(define ex8.8
  "module colors
    interface
    [opaque color
     red : color
     green : color
     is-red? : (color -> bool)]
    body
    [type color = int
     red = 0
     green = 1
     is-red? = proc (c : color) zero?(c)]
  let x = from colors take red in x")

(define ex8.9
  "module ints1
    interface
    [opaque t
     zero : t
     succ : (t -> t)
     pred : (t -> t)
     is-zero : (t -> bool)]
    body
    [type t = int
     zero = 0
     succ = proc(x : t) -(x,-5)
     pred = proc(x : t) -(x,5)
     is-zero = proc (x : t) zero?(x)]
  let z = from ints1 take zero
    in let s = from ints1 take succ
      in (s (s z))")

(define ex8.11
  "module ints1
    interface
    [opaque t
     zero : t
     succ : (t -> t)
     pred : (t -> t)
     is-zero : (t -> bool)]
    body
    [type t = int
     zero = 0
     succ = proc(x : t) -(x,-5)
     pred = proc(x : t) -(x,5)
     is-zero = proc (x : t) zero?(x)]
  let z = from ints1 take zero
    in let s = from ints1 take succ
      in let p = from ints1 take pred
        in let z? = from ints1 take is-zero
          in letrec int to-int (x : from ints1 take t) =
            if (z? x)
            then 0
            else -((to-int (p x)), -1)
          in (to-int (s (s z)))")

(define ex8.13
  "module mybool
    interface
    [opaque t
     true : t
     false : t
     and : (t -> (t -> t))
     not : (t -> t)
     to-bool : (t -> bool)]
    body
    [type t = int
     true = 0
     false = 13
     and = proc (x : t)
            proc (y : t)
              if zero?(x) then y else false
     not = proc (x : t)
            if zero?(x) then false else true
     to-bool = proc (x : t) zero?(x)]
  let true = from mybool take true
    in let false = from mybool take false
      in let and = from mybool take and
        in ((and true) false)")

; ???
(define test
  "module m1
    interface
    [opaque t
     transparent u = (t -> int)
     z : t
     f : (t -> (int -> int))]
    body
    [type t = int 
     type u = (t -> t) 
     z = 0
     f = proc (x : t)
        if zero?(x)
        then proc (x : t)
              -(x,-100)
        else proc (x : t)
              -(x,-200)]
  let f = from m1 take f in
    let z = from m1 take z in 
      ((f z) 0)")