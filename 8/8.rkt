#lang racket

;; This file presents a bare-bones model of a class-based,
;; object-oriented programming language. From afar, the model 
;; resembles a Java without types, inheritance, and assignments. 

;; NOTE: 
;; A few elements of this model anticipate the extensions requested 
;; in problem set 7. In particular, the model already suggests where 
;; to specify types and the outer let-expression in reductions plays the
;; role of a 'dumb' store.

(require redex)

;; -----------------------------------------------------------------------------
;; SYNTAX 

(define-language CBOO ;; class-based, object-orientd
  (p ::= ;; a program 
     (c ...
      ;; initial expression to launch the execution:
      e))
  (c ::= ;; a class definition
     (class cname ((t field) ...) m ...))
  (m ::= ;; a method expression
     (def mname ((t param) ...) e))
  (e ::= 
     x
     n
     (+ e e)
     (* e e)
     this
     (let ((t x e) ...) e) ;; ** like a block in Java, but 'parallel' scope
     (get e field)         ;; ** syntax improvement
     (new cname e ...)
     (send e mname e ...))
  (n ::=
     number)
  (t ::= 
     Object
     Number
     cname)
  ;; variable names, hinting at their role 
  (cname x)
  (mname x)
  (field x)
  (param x)
  (x variable-not-otherwise-mentioned))

;; examples
;; -----------------------------------------------------------------------------
;; Examples with Run-time errors

(define bad1
  (term 
   ((new non-existant-class))))

(define bad2
  (term
   ((class my-class ())
    (let ((Object my-object (new my-class)))
      (send my-object no-method)))))

(define bad3
  (term
   ((class my-class ())
    (let ((Object my-object (new my-class)))
      (get my-object no-field)))))


;; This is an error that should be caught by a type checker
;; but the current evaluate function does not signal a run-time
;; error
(define bad4
  (term
   (this)))

(define bad5
  (term
   ((class my-class ())
    (* 5 (new my-class)))))

(define bad-big
  (term
   ((class my-class 
      ((Object x) (Object y))
      (def add-fields () (+ (get this x) (get this y))))
    (let ((Object o1 (new my-class 0 0))
          (Object o2 (new my-class 3 4))
          (Object o3 (new my-class o1 o2)))
      (send o3 add-fields)))))

(module+ test
  (test-equal (redex-match? CBOO p bad1) #t)
  (test-equal (redex-match? CBOO p bad2) #t)
  (test-equal (redex-match? CBOO p bad3) #t)
  (test-equal (redex-match? CBOO p bad4) #t)
  (test-equal (redex-match? CBOO p bad5) #t)
  (test-equal (redex-match? CBOO p bad-big) #t))
;; -----------------------------------------------------------------------------
;; Type Checking for CBOO

(define-extended-language CBOO-ctx CBOO
  (Γ ::=
    (var-type ...))
  (visited ::=
    ((cname mname) ...))
  (var-type ::=
    (t x)
    (t this)))

(define-judgment-form CBOO-ctx
  #:contract (typed p)
  #:mode (typed I)
  [(where (c ... e) p)
   (typed/classes (c ...))
   (typed/e (c ...) () () e t)
   -------------------- typed-p
   (typed p)])

(define-judgment-form CBOO-ctx
  #:contract (typed/classes (c ...))
  #:mode (typed/classes I)
  [(typed/class (c ...) c) ...
   --------------------
   (typed/classes (c ...))])

(define-judgment-form CBOO-ctx
  #:contract (typed/class (c ...) c)
  #:mode (typed/class I I)
  [(where (class cname ((t field) ...) m ...) c_active)
   (typed/method (c ...) cname m) ...
   --------------------
   (typed/class (c ...) c_active)])

(define-judgment-form CBOO-ctx
  #:contract (typed/method (c ...) cname m)
  #:mode (typed/method I I I)
  [(where (def mname ((t param) ...) e) m)
   (typed/e (c ...) ((cname this) (t param) ...) ((cname mname)) e t_e)
   --------------------
   (typed/method (c ...) cname m)])

(define-judgment-form CBOO-ctx
  #:contract (typed/e (c ...) Γ visited e t)
  #:mode (typed/e I I I I O)
  [(where (var-type_a ... (t x) var-type_b ...) Γ)
   (side-condition ,(not (member (term x) (term (var-type_a ...)))))
   -------------------- e-var
   (typed/e (c ...) Γ visited x t)]
  [-------------------- e-num
   (typed/e (c ...) Γ visited n Number)]
  [(typed/e (c ...) Γ visited e_l Number)
   (typed/e (c ...) Γ visited e_r Number)
   -------------------- e-add
   (typed/e (c ...) Γ visited (+ e_l e_r) Number)]  
  [(typed/e (c ...) Γ visited e_l Number)
   (typed/e (c ...) Γ visited e_r Number)
   -------------------- e-mul
   (typed/e (c ...) Γ visited (* e_l e_r) Number)]
  [(where (var-type_a ... (t this) var-type_b ...) Γ)
   (side-condition ,(not (member (term (t this)) (term (var-type_a ...)))))
   -------------------- e-this
   (typed/e (c ...) Γ visited this t)]
  [(where (var-type ...) Γ)
   (where Γ_2 ((t_let x) ... var-type ...))
   (typed/e (c ...) Γ visited e_let t_let) ...
   (typed/e (c ...) Γ_2 visited e t)
   -------------------- e-let
   (typed/e (c ...) Γ visited (let ((t_let x e_let) ...) e) t)]
  [(typed/e (c ...) Γ visited e cname)
   (where (c_1 ... (class cname ((t_field x) ..._n) m ...) c_2 ...) (c ...))
   (where (any_1 ... (t x_field) any_2 ...) ((t_field x) ...))
   -------------------- e-get
   (typed/e (c ...) Γ visited (get e x_field) t)]
  [(where (c_1 ... (class cname ((t_field x) ..._n) m ...) c_2 ...) (c ...))
   (typed/e (c ...) Γ visited e t_field) ...
   -------------------- e-new
   (typed/e (c ...) Γ visited (new cname e ..._n) cname)]
  [(where ((cname_visited mname_visited) ...) visited)
   (typed/e (c ...) Γ visited e_to cname)
   (where (c_1
	   ... 
	   (class cname (any ...) 
	     m_1 ... 
	     (def mname ((t_param param) ..._n) e_m)
	     m_2 ...)
	   c_2 ...)
	  (c ...))
   (typed/e (c ...) Γ visited e_param t_param) ...
   (side-condition ,(not (member (term (cname mname)) (term visited))))
   (where (var-type ...) Γ)
   (where Γ_2 ((cname this) (t_param param) ... var-type ...))
   (typed/e (c ...) Γ_2 ((cname mname) (cname_visited mname_visited) ...) e_m t)
   -------------------- e-send
   (typed/e (c ...) Γ visited (send e_to mname e_param ..._n) t)])

(module+ test
  (define-syntax-rule (types p0)
    (test-equal (term (judgment-holds (typed p0)))
                (term (judgment-holds #t))))

  (define-syntax-rule (~types p0)
    (test-equal (term (judgment-holds (typed p0)))
                (term (judgment-holds #f))))

  ;; Well-typed programs
  (types (1))
  (types ((+ 1 1)))
  (types ((let ((Number x 1)) x)))
  (types ((let ((Number x 1) (Number y 1)) (* x y))))
  (types ((class C ()) (new C)))
  (types ((class C ((Number c))) (new C 3)))
  (types ((class A ()) (class B ()) (let ((A a (new A))) a)))
  (types ((class C () (def m ((Number n)) (* n n))) 
          (let ((C c (new C))) (send c m 9))))
  (types ((class C () (def m () (send this n)) (def n () 5)) 0))

  ;; Poorly-typed Programs
  (~types ((class C ()) (+ (new C) 3)))
  (~types ((class A ()) (class B ()) (let ((A a (new B))) a)))
  (~types ((class A ()) (class B () (def b () (+ 3 (new A)))) 0))
  (~types ((class C ()) (+ (new C) 3)))
  (~types ((class C () (def m ((Number n)) (* n n))) 
           (let ((C c (new C)))
             (send c m (new C)))))
  (~types ((class C () (def m () (send this m))) 0))
  (~types (this))
  (~types ((class C () (def m () (send (new B) m this)))
           (class B () (def m ((C c)) (send (new A) m c)))
           (class A () (def m ((C c)) (send c m)))
           0))
  (~types ((class C () (def m () (send (new B) m (new C))))
           (class B () (def m ((C c)) (send (new A) m c)))
           (class A () (def m ((C c)) (send c m)))
           0)))

(define-metafunction CBOO
  typed-evaluate : p -> any or "type error"
  [(typed-evaluate p) (evaluate p)
   (side-condition (judgment-holds (typed p)))]
  [(typed-evaluate p) "type error"])

(module+ test
  (test-equal (term (typed-evaluate ,bad1)) "type error")
  (test-equal (term (typed-evaluate ,bad2)) "type error")
  (test-equal (term (typed-evaluate ,bad3)) "type error")
  (test-equal (term (typed-evaluate ,bad4)) "type error")
  (test-equal (term (typed-evaluate ,bad5)) "type error")
  (test-equal (term (typed-evaluate ,bad-big)) "type error")

  (define-syntax-rule 
    (runs-well/typed p0 v)
    (test-equal (e-=α (term (typed-evaluate ,p0)) v) #t))

  (runs-well/typed ((let ((Number x 1)) x)) 1)
  (runs-well/typed ((let ((Number x 1) (Number y 1)) (* x y))) 1)
  (runs-well/typed ((class C ()) (new C)) (new C))
  (runs-well/typed ((class C ((Number c))) (new C 3))
                   (let ((Object x (new C 3))) x))
  (runs-well/typed ((class A ()) (class B ()) (let ((A a (new A))) a))
                   (let ((Object l (new A))) l)))

;; -----------------------------------------------------------------------------

(define p0
  (term
   (;; class definitions: 
    (class rectangle ((Object width) (Object height))
      (def w() (get this width))
      (def h() (get this height))
      (def area() 
	   (let ((Object w (send this w))
		 (Object h (get this height)))
	     (* w h)))) 
    (class start-here ()
      (def main()
	   (send (new rectangle 200 300) area)))
    ;; initial expression 
    (send (new start-here) main))))

(define p1
  (term
   (;; class definitions: 
    (class rectangle ((Object width) (Object height))
      (def w() (get this width))
      (def h() (get this height))
      (def area() 
        (let ((Object w (send this w))
              (Object h (get this height)))
          (* w h)))) 
    (class start-here ()
      (def main()
        (send (new rectangle 200 300) area)))
    ;; initial expression 
    (send (new start-here) main))))

(define p2
  (term 
   ((class main ((Object inits))
      (def main ((Object argv))
        this))
    (send (new main 1) main 2))))

(define bug1
  (term 
   ((class bug ((Object a)))
    (let ()
      (let ((Object x (new bug 1))
            (Object y (new bug 2)))
        (+ (get x a) (get y a)))))))

(module+ test
  (define-syntax-rule
    (grammatically-correct p0)
    (test-equal (redex-match? CBOO p p0) #t))
  
  (grammatically-correct p0) 
  (grammatically-correct p1) 
  (grammatically-correct p2)
  (grammatically-correct bug1))

;; α equivalence 

;; CBOO.e CBOO.e -> Boolean 
;; (e-α= e1 e2) is true if expression e1 is alpha-equivalent to e2 
;; works for closed expressions only 
(define (e-=α e1 e2)
  (define-extended-language CBOO-sd CBOO
    (e .... (var sd))
    (sd natural))
  ;; (sd e (x ...)) maps e to a static distance form or e, 
  ;; relative to the preceding bindings x ...; roughly speaking, 
  ;; sd replaces each occurrence of a variable x_* with a static
  ;; distance record (var n) where n is the depth of x_* in (x ...)
  (define-metafunction CBOO-sd 
    sd : e (x ...) -> e 
    [(sd x (x_1 ... x x_2 ...)) 
     (var sd)
     (side-condition (not (member (term x) (term (x_1 ...)))))
     (where sd ,(length (term (x_1 ...))))]
    [(sd this any) this]
    [(sd n any) n]
    [(sd (new cname e ...) any) (new cname (sd e any) ...)]
    [(sd (+ e_1 e_2) any) (+ (sd e_1 any) (sd e_2 any))]
    [(sd (* e_1 e_2) any) (* (sd e_1 any) (sd e_2 any))]
    [(sd (send e_t mname e ...) any) (send (sd e_t any) mname (sd e any) ...)]
    [(sd (let ((t x e) ...) e_b) (x_1 ...))
     ;; eliminate binding occurrence of variables because their names 
     ;; might differ and ignoring this difference is the whole point 
     ;; of alpha equivalence; ALSO note parallel binding 
     (let ((t ^ (sd e (x_1 ...))) ...) (sd e_b (x ... x_1 ...)))])
  ;; --- now convert to sd and compare with plain equal --- 
  (equal? (term (sd ,e1 ())) (term (sd ,e2 ()))))

(module+ test
  (test-equal 
   (e-=α (term (let ((Object x 1)) (+ x 2)))
         (term (let ((Object y 1)) (+ y 2))))
   #t)
  
  (test-equal 
   (e-=α (term (let ((Object x 1)) (let ((Object y 2)) (+ x y))))
         (term (let ((Object y 1)) (let ((Object z 2)) (+ y z)))))
   #t)
  
  (test-equal 
   (e-=α (term (let ((Object x 1)) 
                 (let ((Object y (let ((Object x 9)) (+ x 7))))
                   (+ x y))))
         (term (let ((Object y 1))
                 (let ((Object z (let ((Object x 9)) (+ x 7))))
                   (+ y z)))))
   #t)
  
  (test-equal 
   (e-=α (term (let ((Object x 1)) 
                 (let ((Object y (let ((Object w 9)) (+ x w))))
                   (+ x y))))
         (term (let ((Object y 1))
                 (let ((Object z (let ((Object v 9)) (+ y v))))
                   (+ y z)))))
   #t)
  
  (test-equal 
   (e-=α (term (let ((Object x (let ((Object y 3)) y)))
                 (let ((Object y 2))
                   (+ x y))))
         (term (let ((Object x (let ((Object z 3)) z))) 
                 (let ((Object y 2))
                   (+ x y)))))
   #t))

;; substitution 

;; (subst-n (x1 e1) (x2 e2) ... e) replaces x1 with e1, x2 with e2, etc in e
;; without messing up the binding structure 
(define-metafunction CBOO
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) any_3])

;; (subst x1 e1 e) replaces x1 with e1 in e 
;; without messing up the binding structure 
(define-metafunction CBOO
  subst : x any any -> any
  ;; 1. x_1 bound, so don't continue in let's body but subst in surrounding bindings
  [(subst x_1 any_1 (let ((t_2 x_2 any_2) ... (t_1 x_1 any_*) (t_3 x_3 any_3) ...) e)) 
   (let ((t_2 x_2 (subst x_1 any_1 any_2)) ... (t_1 x_1 any_*) (t_3 x_3 (subst x_1 any_1 any_3)) ...)
     e)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (let ((t_2 x_2 any_2) ... ) any_b))
   (let ((t_2 x_new (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_2))) ...)
     (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_b)))
   (where (x_new ...)
          ,(variables-not-in (term (x_1 any_1 any_2 ... any_b)) (term (x_2 ...))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

;; (subst-vars (x_1 x_11) ... any) replaces x_1 by x_11 in any 
;; regardless of binding structure 
(define-metafunction CBOO
  subst-vars : (any_x any) ... any -> any
  [(subst-vars (any_x1 any_1) any_x1) any_1]
  [(subst-vars (any_x1 any_1) (any_2 ...)) 
   ((subst-vars (any_x1 any_1) any_2) ...)]
  [(subst-vars (any_x1 any_1) any_2) any_2]
  [(subst-vars (any_x1 any_1) (any_x_2 any_2) ... any_3) 
   (subst-vars (any_x1 any_1) (subst-vars (any_x_2 any_2) ... any_3))]
  [(subst-vars any) any])

(module+ test
  #;
  (define-syntax-rule 
    (=-up-to-α (x e) ... e_body e_expected)
    (test-equal (term (subst-n (x e) ... e_body)) (term e_expected) #:equiv e-=α))
  
  ;; if you are not running the cutting edge drracket, use this instead: 
  (define-syntax-rule 
    (=-up-to-α (x e) ... e_body e_expected)
    (test-equal  (e-=α (term (subst-n (x e) ... e_body)) (term e_expected)) #t))
  
  (=-up-to-α (x 1) (* x 2) 
             (* 1 2))
  
  (=-up-to-α (x 1) (let ((Object y 3)) (* x 2)) 
             (let ((Object y 3)) (* 1 2)))
  
  (=-up-to-α (x 1) (let ((Object y (let ((Object x 4)) x))) (* x 2)) 
             (let ((Object y (let ((Object x 4)) x))) (* 1 2)))
  
  (=-up-to-α (x 1) (let ((Object y (let ((Object w 4)) x))) (* x 2))
             (let ((Object y (let ((Object w 4)) 1))) (* 1 2))))

;; ---------------------------------------------------------------------------------------------------
;; SEMANTICS 

;; extend the language with run-time values and evaluation contexts 
(define-extended-language CBOO-dynamic CBOO 
  (E ::= ;; expression contexts 
     hole 
     (get E field)
     (+ v ... E e ...)
     (* v ... E e ...)
     (new cname v ... E e ...)
     (send E mname e ...)
     (send v mname v ... E e ...)
     (let ((t x v) ... (t x E) (t x e) ...) e))
  (v ::= ;; values 
     this
     n
     x)
  (o ::= 
     v
     ;; BUG: bug1 revealed that (new cname v ...) cannot be a value.
     ;; Otherwise the reduction relation is neither standard nor correct. 
     (new cname v ...)))

;; (evaluate p) reduces program p to canonical form and unloads it as a value
(define-metafunction CBOO-dynamic 
  evaluate : p -> any
  [(evaluate p) 
   any
   (where p_l (load p))
   (where (p_v) ,(apply-reduction-relation* ->oo (term p_l)))
   (where any (unload p_v))]
  [(evaluate p) 
   ,(error 'evaluate "program reduced to more than one canonical form")
   (where p_l (load p))
   (where (p_v ...) ,(apply-reduction-relation* ->oo (term p_l)))])

;; (load p) makes sure that the body of the program is a let 
;; that binds x-s to v-s (pre-existing or inserted)
(define-metafunction CBOO-dynamic
  load : p -> p
  [(load (name p (c ... (let ((t x v) ...) e)))) p]
  [(load (c ... e)) (c ... (let () e))])

;; (unload p) turns a canonical let into a plain value by substituting
;; the bound values for the bound variables in the body
(define-metafunction CBOO-dynamic
  unload : p -> (let ((t x o) ...) v) or v or "run-time error"
  [(unload (c ... (let ((t x o) ...) v_p))) 
   (let ((t_f x_f o_f) any_1 ...) v_p)
   (where ((t_f x_f o_f) any_1 ...) (free ((t x o) ...) v_p))]
  [(unload (c ... (let ((t x o) ...) v_p))) 
   v_p
   (where () (free ((t x o) ...) v_p))]
  ;; ** broadened unload to take care of stuck states 
  [(unload p) "run-time error"])

;; (free ((t x o) ...) v) collects the (t x o) ... from the 
;; declarations whose declared variable occurs free in v
(define-metafunction CBOO-dynamic 
  free : ((t x o) ...) v -> ((t x o) ...) or "run-time error"
  [(free any_1 n) ()]
  [(free ((t_1 x_1 o_1) ... (t x o) (t_2 x_2 o_2) ...) x) ((t x o))]
  [(free any_1 x) "run-time error"]
  [(free any_1 this) ()]
  [(free any_1 (get e field)) (free any_1 e)]
  [(free any_1 (send e mname e_1 ...)) (set-union* (free any_1 e) (free any_1 e_1) ...)]
  [(free any_1 (new cname e_1 ...)) (set-union* (free any_1 e_1) ...)]
  [(free any_1 (+ e e_1)) (set-union* (free any_1 e) (free any_1 e_1))]
  [(free any_1 (* e e_1)) (set-union* (free any_1 e) (free any_1 e_1))]
  [(free any_1 (let ((t x e_x) ...) e)) 
   (set-union* (set-minus (free any_1 e) x ...) (free any_1 e_x) ...)])

;; (set-minus (any_1 ...] any_2 ...) removes the any_2s from the (any_1 ...) list
(module+ test
  (test-equal (term (set-minus ((Object x 1) (Object y 2)) z x)) (term ((Object y 2)))))
(define-metafunction CBOO-dynamic 
  set-minus : ((t x o) ...) x ... -> ((t x o) ...)
  [(set-minus any_1) any_1]
  [(set-minus ((t_1 x_1 o_1) ... (t x o) (t_2 x_2 o_2) ...) x x_r ...) 
   (set-minus ((t_1 x_1 o_1) ... (t_2 x_2 o_2) ...) x_r ...)]
  [(set-minus any_1 x x_r ...) (set-minus any_1 x_r ...)])

;; (set-union* ((t x o) ...) ...) produces the n-ary set-union of the declarations 
(module+ test
  (test-equal 
   (term (set-union* ((Object x 1) (Object y 2)) 
                     ((Object z 3) (Object x 1))
                     ((Object w 4))))
   ;; this is a cheat: we are using lists for sets, order matters
   (term ((Object w 4) (Object z 3) (Object x 1) (Object y 2)))))
(define-metafunction CBOO-dynamic 
  set-union* : ((t x o) ...) ... -> ((t x o) ...)
  [(set-union* any_1) any_1]
  [(set-union* any_1 any_2 any_3 ...) (set-union* (set-union any_1 any_2) any_3 ...)])

;; (set-union ((t x o) ...) ...) produces the biary set-union of the declarations 
(define-metafunction CBOO-dynamic 
  set-union : ((t x o) ...) ((t x o) ...) -> ((t x o) ...)
  [(set-union any_1 ()) any_1]
  [(set-union any_1 ((t x o) (t_r x_r o_r) ...))
   (set-union any_1 ((t_r x_r o_r) ...))
   (side-condition (member (term (t x o)) (term any_1)))]
  [(set-union any_1 ((t x o) (t_r x_r o_r) ...))
   ((t x o) any_3 ...)
   (where (any_3 ...) (set-union any_1 ((t_r x_r o_r) ...)))])

;; p_1 ->oo p_2 means program p_1 reduces to p_2 (emphasis: program)
;; notes: 
;; (1) every program p_i has the shape 
;;     class definition 1
;;     ...
;;     class definition n
;;     (let ( [t x_1 v_1] ... ) e) 
;; (2) the reductions work on e, which specifies the instruction 'sequence'
;; (3) the context of e contains the interpretation of the instructions
;;     for eample:
;;       if e = E[x] says look in the outer let binding to find 
;;       the current value (object) for x 
;;       if e = E[(new C ...)] says look in the class definitions for C
;;       so that you can create a object and name it in the outer let 
;;       if e = E[(send x m v ...)] says look in let for x's value
;;       and in the class definitions for m's method definition; then 
;;       proceed as if this were a β_v reduction 

(define ->oo
  (reduction-relation 
   CBOO-dynamic 
   #:domain p
   (--> (c_1 ... 
         (class x_c ((t field) ..._c) m ...) 
         c_2 ... 
         (let ((t_1 x_1 o_1) ...) (in-hole E (new x_c v ..._c))))
        ;; --- reduce to ---
        (c_1 ... 
         (class x_c ((t field) ...) m ...) 
         c_2 ... 
         (let ((Object x_new (new x_c v ...))
               (t_1 x_1 o_1) ...) 
           (in-hole E x_new)))
        (where x_new ,(variable-not-in (term (x_1 ... E)) (term l)))
        new)
   (--> (c_1 ... 
         (class x_c ((t_1 field_1) ..._c (t field) (t_2 field_2) ...) m ...)
         c_2 ... 
         (let 
             ((t_3 x_3 o_3) ... 
              (t_new x_new (new x_c v_* ..._c v v_+ ...))
              (t_4 x_4 o_4) ...) 
           (in-hole E (get x_new field))))
        ;; --- reduce to ---
        (c_1 ... 
         (class x_c ((t_1 field_1) ... (t field) (t_2 field_2) ...) m ...)
         c_2 ... 
         (let
             ((t_3 x_3 o_3) ... 
              (t_new x_new (new x_c v_* ... v v_+ ...))
              (t_4 x_4 o_4) ...) 
           (in-hole E v)))
        get)
   (--> (c_1 ... 
         (class cname ((t field) ...) 
           m_1 ... (def mname ((t_p x_p) ..._c) e) m_2 ...)
         c_2 ...
         (let ((t_1 x_1 o_1) ...
               (t_x x (new cname v_x ...))
               (t_2 x_2 o_2) ...)
           (in-hole E (send x mname v ..._c))))
        ;; --- reduce to ---
        (c_1 ... 
         (class cname ((t field) ...) 
           m_1 ... (def mname ((t_p x_p) ...) e) m_2 ...)
         c_2 ...
         (let ((t_1 x_1 o_1) ... 
               (t_x x (new cname v_x ...))
               (t_2 x_2 o_2) ...)
           (in-hole E (subst-vars (this x) (subst-n (x_p v) ... e)))))
        send)
   (--> (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E (let ((t x v) ...) e))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E (subst-n (x v) ... e))))
        let)
   (--> (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E (+ n_1 n_2))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E n)))
        (where n ,(+ (term n_1) (term n_2)))
        +)
   (--> (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E (* n_1 n_2))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 o_1) ...) (in-hole E n)))
        (where n ,(* (term n_1) (term n_2)))
        *)))

(module+ test
  #;
  (define-syntax-rule 
    (runs-well p0 v)
    (test-equal (term (evaluate ,p0)) v #:equiv e-=α))
  
  ;; if you are not running the cutting edge drracket, use this instead: 
  (define-syntax-rule 
    (runs-well p0 v)
    (test-equal (e-=α (term (evaluate ,p0)) v) #t))
  
  (runs-well p0 60000)
  (runs-well p1 60000)
  (runs-well p2 (term (let ((Object l (new main 1))) l)))
  (runs-well bug1 3)
  
  (define-syntax-rule
    (gets-stuck p_e)
    (test-equal (term (evaluate ,p_e)) "run-time error"))
  
  (test-results))
