#lang eopl
; simple moduleを持つ言語を実装
; interfaceで宣言した値だけをプログラムのボディで使える
; モジュールのinterfaceとbodyで値の型を揃える
; モジュールのinterfaceで宣言した値を全てbodyでsupplyする
; interfaceで宣言した順番にbodyでsupplyする
; 複数のモジュールを定義できるがlet*と同じスコープ

; typed module -------------------------------------------------------
(define-datatype typed-module typed-module?
  (simple-module
   (bindings environment?)))

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
                                  m-val
                                  (lookup-module-name-in-env m-name saved-env))))))

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
   (expected-iface iface?)
   (m-body module-body?)))

(define-datatype iface iface?
  (simple-iface
   (decls (list-of decl?))))

(define-datatype decl decl?
  (val-decl
   (var identifier?)
   (ty type?)))

(define-datatype module-body module-body?
  (defns-module-body
    (defns (list-of definition?))))

(define-datatype definition definition?
  (val-defn
   (var-name identifier?)
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

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type type?)
   (result-type type?)))

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
                                      (cdr defns) new-env)))))))))

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

    (module-body
     ("[" (arbno definition) "]")
     defns-module-body)

    (definition
      (identifier "=" expression)
      val-defn)

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
     proc-type)))


;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

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

(define test1
  "module m1
   interface
   [a : int
    b : int
    c : int]
   body
   [a = 33
   x = -(a,1) % = 32
   b = -(a,x) % = 1
   c = -(x,b)] % = 31
  let a = 10 
  in -(-(from m1 take a,
         from m1 take b),
       a)")

(define test2
  "module m1
   interface
    [u : bool]
   body
    [u = 33]
  44")

(define test3
  "module m1
    interface
    [u : int
     v : int]
    body
    [u = 33]
  44")

(define test4
  "module m1
    interface
    [u : int
     v : int]
    body
    [v = 33
     u = 44]
  from m1 take u")

(define test5
  "module m1
    interface
    [u : int]
    body
    [u = 44]
  module m2
    interface
    [v : int]
    body
    [v = -(from m1 take u,11)]
  -(from m1 take u, from m2 take v)")