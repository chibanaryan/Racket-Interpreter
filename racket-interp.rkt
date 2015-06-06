#|
#lang racket
(require "parenthec.rkt")
(require "pmatch.rkt")
|#

;; Ryan Chibana

(define-registers *expr *env *k *v *c *a *num)
(define-program-counter *pc)

(define-union exp
  (const n)
  (var v)
  (if test conseq alt)
  (mult rand1 rand2)
  (sub1 rand)
  (zero rand)
  (capture body)
  (return vexp kexp)
  (let vexp body)
  (lambda body)
  (app rator rand))
 
;treat apply-env and apply-closure as serious, closure and extend as simple.
(define-label value-of ; *expr *env *k
    (union-case *expr exp
      [(const n) (begin ; (apply-k *k n)
		   (set! *k *k)
		   (set! *expr *expr)
		   (set! *env *env)
		   (set! *v n)
		   (set! *pc apply-k))]
      [(var v) (begin ; (apply-k *k (apply-env *env v))
	       	  (set! *k *k)
		  (set! *expr *expr)
		  (set! *env *env)
		  (set! *num v)
		  (set! *pc apply-env))]
      [(if test conseq alt) ; (value-of test *env (cont_if conseq alt *env *k))
       (begin
	 (set! *k (cont_if conseq alt *env *k))
	 (set! *expr test)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(mult rand1 rand2) ; (value-of rand1 *env (cont_mult rand2 *env *k))
       (begin
	 (set! *k (cont_mult rand2 *env *k))
	 (set! *expr rand1)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(sub1 rand) ; (value-of rand *env (cont_sub1 *k))
       (begin
	 (set! *k (cont_sub1 *k))
	 (set! *expr rand)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(zero rand) ; (value-of rand *env (cont_zero k))
       (begin
	 (set! *k (cont_zero *k))
	 (set! *expr rand)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(capture body) ; (value-of body (envr_extend *k *env) *k))))
	(begin
	 (set! *k *k)
	 (set! *expr body)
	 (set! *env (envr_extend *k *env))
	 (set! *v *v)
	 (set! *pc value-of))]
      [(return vexp kexp) ; (value-of kexp *env (cont_return vexp *env *k))
       (begin
	 (set! *k (cont_return vexp *env *k))
	 (set! *expr kexp)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(let vexp body) ; (value-of vexp env (cont_let body *env *k))
       (begin
	 (set! *k (cont_let body *env *k))
	 (set! *expr vexp)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]
      [(lambda body) ; (apply-k k (clos_closure body env))
	(begin
	 (set! *k *k)
	 (set! *expr *expr)
	 (set! *env *env)
	 (set! *v (clos_closure body *env))
	 (set! *pc apply-k))]
      [(app rator rand) ;(value-of rator *env (cont_app rand *env *k))
       (begin
	 (set! *k (cont_app rand *env *k))
	 (set! *expr rator)
	 (set! *env *env)
	 (set! *v *v)
	 (set! *pc value-of))]))

(define-union envr
  (empty)
  (extend arg env))
 
(define-label apply-env ; *env *num
    (union-case *env envr
      [(empty) (error 'env "unbound variable")]
      [(extend arg env)
       (if (zero? *num)
	   (begin
	     (set! *v arg)
	     (set! *pc apply-k))
	   (begin
	     (set! *env env)
	     (set! *num (sub1 *num))
	     (set! *pc apply-env)))]))
 
(define-union clos
  (closure code env))
 
(define-label apply-closure ; *c *a *k
    (union-case *c clos
      [(closure code env) ; (value-of code (envr_extend a env) k)
       (begin
	 (set! *k *k)
	 (set! *expr code)
	 (set! *env (envr_extend *a env))
	 (set! *v *v)
	 (set! *pc value-of))]))

(define-union cont
  (empty j)
  (if conseq alt env k)
  (sub1 k)
  (zero k)
  (inner-mult k c)
  (mult rand2 env k)
  (inner-return k rt)
  (return vexp env k)
  (let body env k)
  (inner-app rt k)
  (app rand env k))

(define-label apply-k ; *k *v
    (union-case *k cont
	[(empty j) (j *v)]
	[(if conseq alt env k) ; ((lambda (t) (if t (value-of conseq env k) (value-of alt env k))) *v)
	 (if *v
	   (begin 
	     (set! *k k)
	     (set! *expr conseq)
	     (set! *env env)
	     (set! *v *v)
	     (set! *pc value-of))
	   (begin 
	     (set! *k k)
	     (set! *expr alt)
	     (set! *env env)
	     (set! *v *v)
	     (set! *pc value-of)))]
	[(sub1 k) ; ((lambda (v) (apply-k k (- v 1))) *v)
	 (begin
	   (set! *k k)
	   (set! *expr *expr)
	   (set! *env *env)
	   (set! *v (- *v 1))
	   (set! *pc apply-k))]
	[(zero k) ; ((lambda (v) (apply-k k (zero? v))) *v)
	 (begin
	   (set! *k k)
	   (set! *expr *expr)
	   (set! *env *env)
	   (set! *v (zero? *v))
	   (set! *pc apply-k))]
	[(mult rand2 env k) ; ((lambda (v) (value-of rand2 env (cont_inner-mult k v))) *v)
	 (begin
	   (set! *k (cont_inner-mult k *v))
	   (set! *expr rand2)
	   (set! *env env)
	   (set! *v *v)
	   (set! *pc value-of))]
	[(inner-mult k c) ; ((lambda (b) (apply-k k (* b c))) *v)
	 (begin
	   (set! *k k)
	   (set! *expr *expr)
	   (set! *env *env)
	   (set! *v (* *v c))
	   (set! *pc apply-k))]
	[(inner-return k rt) ; ((lambda (rn) (apply-k rt rn)) *v)
	 (begin
	   (set! *k rt)
	   (set! *expr *expr)
	   (set! *env *env)
	   (set! *v *v)
	   (set! *pc apply-k))]
	[(return vexp env k) ; ((lambda (rt) (value-of vexp env (cont_inner-return k rt))) *v)
	 (begin
	   (set! *k (cont_inner-return k *v))
	   (set! *expr vexp)
	   (set! *env env)
	   (set! *v *v)
	   (set! *pc value-of))]
	[(let body env k) ; ((lambda (v) (value-of body (envr_extend v env) k)) *v)
	 (begin
	   (set! *k k)
	   (set! *expr body)
	   (set! *env (envr_extend *v env))
	   (set! *v *v)
	   (set! *pc value-of))]
	[(inner-app rt k) ; ((lambda (rn) (apply-closure rt rn k)) *v)
	 (begin
	   (set! *k k)
	   (set! *expr *expr)
	   (set! *env *env)
	   (set! *v *v)
	   (set! *c rt)
	   (set! *a *v)
	   (set! *pc apply-closure))]
	[(app rand env k) ; ((lambda (rt) (value-of rand env (cont_inner-app rt k))) *v)
	 (begin
	   (set! *k (cont_inner-app *v k))
	   (set! *expr rand)
	   (set! *env env)
	   (set! *v *v)
	   (set! *pc value-of))]))

#|
(define-label main
    (begin                        
    	(set! *expr (exp_app
            (exp_app
             (exp_lambda (exp_lambda (exp_var 1)))
             (exp_const 5))
            (exp_const 6)))
    	(set! *env (envr_empty))
    	(set! *v 'hukarz)
    	(set! *pc value-of)
    	(mount-trampoline cont_empty *k *pc)
    	(printf "~s\n" *v) 
	(dismount-trampoline cont_empty)
				
    	(set! *expr (exp_app
	    (exp_lambda
	     (exp_app
	      (exp_app (exp_var 0) (exp_var 0))
	      (exp_const 5)))
	    (exp_lambda
	     (exp_lambda
	      (exp_if (exp_zero (exp_var 0))
		      (exp_const 1)
		      (exp_mult (exp_var 0)
				(exp_app
				 (exp_app (exp_var 1) (exp_var 1))
				 (exp_sub1 (exp_var 0)))))))))
	  (set! *env (envr_empty))
	  (set! *v 'hukarz)
    	  (set! *pc value-of)
    	  (mount-trampoline cont_empty *k *pc)
    	  (printf "~s\n" *v) 
	  (dismount-trampoline cont_empty)

   	 (set! *expr (exp_mult (exp_const 2)
	    (exp_capture
	     (exp_mult (exp_const 5)
		       (exp_return (exp_mult (exp_const 2) (exp_const 6))
                                   (exp_var 0))))))
   	 (set! *env (envr_empty))
   	 (set! *v 'hukarz)
   	 (set! *pc value-of)
   	 (mount-trampoline cont_empty *k *pc)
   	 (printf "~s\n" *v)  
	 (dismount-trampoline cont_empty)

   	 (set! *expr (exp_let
	    (exp_lambda
	     (exp_lambda
	      (exp_if
	       (exp_zero (exp_var 0))
	       (exp_const 1)
	       (exp_mult
		(exp_var 0)
		(exp_app
		 (exp_app (exp_var 1) (exp_var 1))
		 (exp_sub1 (exp_var 0)))))))
	    (exp_app (exp_app (exp_var 0) (exp_var 0)) (exp_const 5))))
   	 (set! *env (envr_empty))
   	 (set! *v 'hukarz)
   	 (set! *pc value-of)
   	 (mount-trampoline cont_empty *k *pc)
   	 (printf "~s\n" *v)))
	 ;(dismount-trampoline cont_empty)))
|#