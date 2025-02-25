#lang eopl 
; simple moduleを持つ言語を実装
; interfaceで宣言した値だけをプログラムのボディで使える
; モジュールのinterfaceとbodyで値の型を揃える
; モジュールのinterfaceで宣言した値を全てbodyでsupplyする
; interfaceで宣言した順番にbodyでsupplyする
; 複数のモジュールを定義できるがlet*と同じスコープ


;Syntax data types ---------------------------------------------------
(define-datatype program program?
  (a-program
   (m-defs (list-of module-defn?))
   (exp1 expression?)))

(define-datatype module-defn module-defn?
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
    (defns (list-of defn?))))

(define-datatype defn defn?
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
   (letrec-body expression?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type type?)
   (result-type type?)))


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

(define gramar
  '((program ((arbno module-defn) expression) a-program)
    
    (module-defn ("module" identifier "interface" iface "body" module-body) a-module-definition)
    
    (iface ("[" (arbno decl) "]") simple-iface)
    
    (decl (identifier ":" type) val-decl)
    
    (module-body ("[" (arbno defn) "]") defns-module-body)
    
    (defn (identifier "=" expression) val-defn)
    
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