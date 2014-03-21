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
     (get field x)
     (get field this)
     this
     n
     (+ e e)
     (* e e)
     (new cname e ...)
     (send e mname e ...)
     (let ((t x e) ...) e e ...))
  (n ::=
     number)
  (t ::= 
     Object)
  ;; variable names, hinting at their role 
  (cname x)
  (mname x)
  (field x)
  (param x)
  (x variable-not-otherwise-mentioned))

;; examples

(define p1
  (term
   (;; class definitions: 
    (class rectangle ((Object width) (Object height))
      (def w() (get width this))
      (def h() (get height this))
      (def area() 
        (let ((Object w (send this w))
              (Object h (get height this)))
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

;; erroneous programs 
(define e1-new-bad-class
  (term 
   ((send (new Main) m))))

(define e2-object-without-class
  (term 
   ((let ((Object x (new Main))) 
      (send x m)))))

(define e3-class-without-method
  (term 
   ((class Main ()
      (def k()
        42))
    (let ((Object x (new Main))) 
      (send x m)))))

(define e4-bad-*
  (term 
   ((class Main()
      (def m()
        (send this k this))
      (def k((Object x))
        (* x 42)))
    (send (new Main) m))))

(define e5-bad-+
  (term 
   ((class Main()
      (def m()
        (send this k this))
      (def k((Object x))
        (+ x 42)))
    (send (new Main) m))))

(module+ test
  (test-equal (redex-match? CBOO p p1) #t)
  (test-equal (redex-match? CBOO p p2) #t)
  (test-equal (redex-match? CBOO p e1-new-bad-class) #t)
  (test-equal (redex-match? CBOO p e2-object-without-class) #t)
  (test-equal (redex-match? CBOO p e3-class-without-method) #t)
  (test-equal (redex-match? CBOO p e4-bad-*) #t)
  (test-equal (redex-match? CBOO p e5-bad-+) #t))

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
    [(sd (let ((t x e) ...) e_b ...) (x_1 ...))
     (let () (sd e (x ... x_1 ...)) ... (sd e_b (x ... x_1 ...)) ...)])
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
  ;; 1. x_1 bound, so don't continue in let's body 
  [(subst x_1 any_1 
          (let ((t_2 x_2 any_2) ... (t_1 x_1 any_*) (t_3 x_3 any_3) ...)
            e ...))
   (let ((t_2 x_2 (subst x_1 any_1 any_2))
         ... 
         (t_1 x_1 (subst x_1 any_1 any_*))
         (t_3 x_3 (subst x_1 any_1 any_3))
         ...) 
     e ...)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (let ((t_2 x_2 any_2) ... ) any_b ...))
   (let ((t_2 x_new (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_2))) ...)
     (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_b)) ...)
   (where (x_new ...)
          ,(variables-not-in
            (term (x_1 any_1 any_2 ... any_b ...)) 
            (term (x_2 ...))))]
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
  (test-equal (term (subst-n (x 1) (* x 2))) (term (* 1 2)) #:equiv e-=α)
  
  (test-equal (term (subst-n (x 1) (let ((Object y 3)) (* x 2))))
              (term (let ((Object y 3)) (* 1 2)))
              #:equiv e-=α)
  
  (test-equal
   (term (subst-n (x 1) (let ((Object y (let ((Object x 4)) x))) (* x 2))))
   (term (let ((Object y (let ((Object x 4)) x))) (* 1 2)))
   #:equiv e-=α)
  
  (test-equal
   (term (subst-n (x 1) (let ((Object y (let ((Object w 4)) x))) (* x 2))))
   (term (let ((Object y (let ((Object w 4)) 1))) (* 1 2)))
   #:equiv e-=α)
  
  (test-equal 
   (term 
    (subst-n (x 1) (let ((Object y (let ((Object w 4)) (+ x w)))) (* x 2))))
   (term (let ((Object y (let ((Object w 4)) (+ 1 w)))) (* 1 2)))
   #:equiv e-=α))

;; -----------------------------------------------------------------------------
;; SEMANTICS 

;; extend the language with run-time values and evaluation contexts 
(define-extended-language CBOO-dynamic CBOO 
  (E ::= ;; expression contexts 
     hole 
     (+ v ... E e ...)
     (* v ... E e ...)
     (new cname v ... E e ...)
     (send E mname e ...)
     (send v mname v ... E e ...)
     (let ((t x v) ... (t x E) (t x e) ...) e))
  (v ::= ;; values 
     this
     n
     x
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
  unload : p -> v or "run-time error"
  [(unload (c ... (let ((t x v) ...) v_p))) (subst-n (x v) ... v_p)]
  [(unload p) "run-time error"])

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
         (let ((t_1 x_1 v_1) ...) (in-hole E (new x_c v ..._c))))
        ;; --- reduce to ---
        (c_1 ... 
         (class x_c ((t field) ...) m ...) 
         c_2 ... 
         (let ((Object x_new (new x_c v ...))
               (t_1 x_1 v_1) ...) 
           (in-hole E x_new)))
        (where x_new ,(variable-not-in (term (x_1 ... E)) (term l)))
        new)
   (--> (c_1 ... 
         (class x_c ((t_1 field_1) ..._c (t field) (t_2 field_2) ...) m ...)
         c_2 ... 
         (let 
             ((t_3 x_3 v_3) ... 
              (t_new x_new (new x_c v_* ..._c v v_+ ...))
              (t_4 x_4 v_4) ...) 
           (in-hole E (get field x_new))))
        ;; --- reduce to ---
        (c_1 ... 
         (class x_c ((t_1 field_1) ... (t field) (t_2 field_2) ...) m ...)
         c_2 ... 
         (let
             ((t_3 x_3 v_3) ... 
              (t_new x_new (new x_c v_* ... v v_+ ...))
              (t_4 x_4 v_4) ...) 
           (in-hole E v)))
        get)
   (--> (c_1 ... 
         (class cname ((t field) ...) 
           m_1 ... (def mname ((t_p x_p) ..._c) e) m_2 ...)
         c_2 ...
         (let ((t_1 x_1 v_1) ...
               (t_x x (new cname v_x ...))
               (t_2 x_2 v_2) ...)
           (in-hole E (send x mname v ..._c))))
        ;; --- reduce to ---
        (c_1 ... 
         (class cname ((t field) ...) 
           m_1 ... (def mname ((t_p x_p) ...) e) m_2 ...)
         c_2 ...
         (let ((t_1 x_1 v_1) ... 
               (t_x x (new cname v_x ...))
               (t_2 x_2 v_2) ...)
           (in-hole E (subst-vars (this x) (subst-n (x_p v) ... e)))))
        send)
   (--> (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E (let ((t x v) ...) e))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E (subst-n (x v) ... e))))
        let)
   (--> (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E (+ n_1 n_2))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E n)))
        (where n ,(+ (term n_1) (term n_2)))
        +)
   (--> (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E (* n_1 n_2))))
        ;; --- reduce to ---
        (c_1 ... (let ((t_1 x_1 v_1) ...) (in-hole E n)))
        (where n ,(* (term n_1) (term n_2)))
        *)))

(module+ test
  (test-equal (term (evaluate ,p1)) 60000)
  
  ;; is it weird to have  'free' class names in results?
  (test-equal (term (evaluate ,p2)) (term (new main 1)))
  
  (test-equal (term (evaluate ,e1-new-bad-class)) "run-time error")
  (test-equal (term (evaluate ,e2-object-without-class)) "run-time error")
  (test-equal (term (evaluate ,e3-class-without-method)) "run-time error")
  (test-equal (term (evaluate ,e4-bad-*)) "run-time error")
  (test-equal (term (evaluate ,e5-bad-+)) "run-time error")
  
  (test-results))
