#lang eopl
; 文 Statementを追加
; read文を追加

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val reference?) ;denoted value = reference
   (env environment?))
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-vars (list-of identifier?))
   (p-bodies (list-of expression?))
   (env environment?)))

(define extend-env-list
  (lambda (vars vals env)
    (let ((var (car vars))
          (rst-vars (cdr vars))
          (val (car vals))
          (rst-vals (cdr vals)))
      (if (null? rst-vars)
          (extend-env var (newref val) env)
          (begin
            (extend-env-list rst-vars rst-vals (extend-env var (newref val) env)))))))

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
      (extend-env-rec (p-names b-vars p-bodies saved-env)
                      (let ((n (location search-var p-names)))
                        (if n
                            (newref
                             (proc-val
                              (procedure
                               (list-ref b-vars n)
                               (list-ref p-bodies n)
                               env)))
                            (apply-env saved-env search-var)))))))

;; location : Sym * Listof(Sym) -> Maybe(Int)
;; (location sym syms) returns the location of sym in syms or #f is
;; sym is not in syms.  We can specify this as follows:
;; if (memv sym syms)
;;   then (list-ref syms (location sym syms)) = sym
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms))
       => (lambda (n)
            (+ n 1)))
      (else #f))))

;init-env : () → Env
;usage: (init-env) = [i=⌈1⌉,v=⌈5⌉,x=⌈10⌉]
(define init-env
  (lambda ()
    (empty-env)))


(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
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

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of body
                           (extend-env-list vars vals saved-env))))))


; empty-store : () → Sto
(define empty-store
  (lambda () '()))

; usage: A Scheme variable containing the current state of the store. Initially set to a dummy value.
(define the-store 'uninitialized)

; get-store : () → Sto
(define get-store
  (lambda () the-store))

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; reference? : SchemeVal → Bool
(define reference?
  (lambda (v)
    (integer? v)))

; newref : ExpVal → Ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

; deref : Ref → ExpVal
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

; setref! : Ref × ExpVal → Unspecified
; usage: sets the-store to a state like the original, but with position ref containing val.
; the-storeを更新している
(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                ; usage: returns a list like store1, except that position ref1 contains val.
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (report-invalid-reference ref the-store))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))


;Syntax data types
;BNFでの文法
(define-datatype program program?
  (a-program
   (stm1 statement?)))

(define-datatype statement statement?
  (assing-stmt
   (var identifier?)
   (exp1 expression?))
  (print-stmt
   (exp1 expression?))
  (cat-stmt
   (stmts (list-of statement?)))
  (if-stmt
   (test expression?)
   (then-stmt statement?)
   (else-stmt statement?))
  (while-stmt
   (test expression?)
   (body statement?))
  (block-stmt
   (vars (list-of identifier?))
   (stmt1 statement?))
  (read-stmt
   (var identifier?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (add-exp
   (exp1 expression?)
   (exp2 expression?))
  (mult-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  (call-exp
   (rator expression?)
   (rands (list-of expression?)))
  (letrec-exp
   (proc-names (list-of identifier?))
   (bound-vars (list-of identifier?))
   (proc-bodies (list-of expression?))
   (letrec-body expression?))
  (assign-exp
   (var identifier?)
   (exp1 expression?))
  (not-exp
   (exp1 expression?)))

; interpreter -------------------------------------------------
; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (stmt1)
                 (results-of stmt1 (init-env))))))

; results-of : Stmt * env * σ → σ
(define results-of
  (lambda (stmt env)
    (cases statement stmt
      (assing-stmt (var exp1)
                   (setref! (apply-env env var)
                            (value-of exp1 env)))
      (print-stmt (exp1)
                  (display (value-of exp1 env))
                  (newline))
      (cat-stmt (stmts)
                (let ((fst (car stmts))
                      (rst (cdr stmts)))
                  (if (null? rst)
                      (results-of fst env)
                      (begin
                        (results-of fst env)
                        (results-of (cat-stmt rst) env)))))
      (if-stmt (test then-stmt else-stmt)
               (let ((val (value-of test env)))
                 (if (expval->bool val)
                     (results-of then-stmt env)
                     (results-of else-stmt env))))
      (while-stmt (test body)
                  (let ((val (value-of test env)))
                    (if (expval->bool val)
                        (begin
                          (results-of body env)
                          (results-of (while-stmt test body) env))
                        (get-store))))
      (block-stmt (vars stmt1)
                  (results-of stmt1 (extend-env-block env vars)))
      (read-stmt (var)
                 (let ((num (read)))
                   (let ((val (num-val num)))
                     (setref! (apply-env env var) val)))))))

(define extend-env-block
  (lambda (env vars)
    (let ((fst (car vars))
          (rst (cdr vars)))
      (if (null? rst)
          (extend-env fst (newref 'uninitialized) env)
          (extend-env-block
           (extend-env fst (newref 'uninitialized) env)
           rst)))))

;value-of : Exp × Env σ → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (add-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val
                    (+ num1 num2)))))
      (mult-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (* num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      ; バインドされるのは参照
      ; 新しいlocationを作る，storalbe valueはval1
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var (newref val1) env))))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (exp) (value-of exp env)) rands)))
                  (apply-procedure proc args)))
      (letrec-exp (proc-names bound-vars proc-bodies letrec-body)
                  (value-of letrec-body (extend-env-rec proc-names bound-vars proc-bodies env)))
      ; (begin-exp (exp1 exps)
      ;            (value-of-begin-exp (cons exp1 exps) env))
      ; 環境内でvarを探してバインドされている参照を得る
      ; exp1を評価した値を参照先に割り当てる
      (assign-exp (var exp1)
                  (begin
                    (setref!
                     (apply-env env var)
                     (value-of exp1 env))
                    (num-val 27)))
      (not-exp (exp1)
               (let ((val (value-of exp1 env)))
                 (bool-val (not (expval->bool val))))))))


(define scanner-spec-implicit-refs
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

(define grammar-implicit-refs
  '((program (statement) a-program)

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

    (expression
     ("+" "(" expression "," expression ")")
     add-exp)

    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)

    ; let-exp : let y = a in b
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    ; proc-exp : proc(a) b
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression)
     letrec-exp)

    ; begin-exp : begin a ; b ; c end
    ; (expression
    ;  ("begin" expression (arbno ";" expression) "end")
    ;  begin-exp)

    (expression
     ("set" identifier "=" expression)
     assign-exp)

    (expression
     ("not" "(" expression ")")
     not-exp)

    (statement
     (identifier "=" expression)
     assing-stmt)

    (statement
     ("print" expression)
     print-stmt)

    (statement
     ("{" (separated-list statement ";") "}")
     cat-stmt)

    (statement
     ("if" expression statement statement)
     if-stmt)

    (statement
     ("while" expression statement)
     while-stmt)

    (statement
     ("var" (separated-list identifier ",") ";" statement)
     block-stmt)

    (statement
     ("read" identifier)
     read-stmt)
    ))



(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define any?
  (lambda (x) #t))

;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-implicit-refs grammar-implicit-refs))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-implicit-refs grammar-implicit-refs)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))

; 7
(define pgm1
  "var x,y ; {x = 3; y = 4; print +(x,y)}")

; 12
(define pgm2
  "var x,y,z; {x = 3; 
               y = 4;
               z = 0;
               while not(zero?(x))
                 {z = +(z,y); x = -(x,1)};
               print z}")
; 3 4 3
(define pgm3
  "var x; {x = 3; 
          print x;
          var x; {x = 4; print x};
          print x}")

; 12
(define pgm4
  "var f,x; {f = proc(x,y) *(x,y); x = 3;
            print (f 4 x)}")

(define pgm5
  "if zero?(0) print 100  print 200")

(define pgm6
  "var x,y ; {x = 3; y = 4; read y; print +(x,y)}")

(define pgm7
  "var x,y,z ; {x = 3; y = 4; read z; print +(+(x,y),z)}")