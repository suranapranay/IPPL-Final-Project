#lang racket
(require redex)
(caching-enabled? #f)
(define-language pcf
  (e ::= ;; expressions 
     x
     z
     (e e)
     (s(e))
     (ifz(e e x e))
     (fun(x x e))
     (app(e e))
     l
     )
  (v ::=
     (fun(x x e))
     z
     (s(l))
     )
  (z 0)
  (mu ((l o) ...))
  (ro ((l o) ...))
  (nu ((l o) ...))
  (x ::= variable-not-otherwise-mentioned)
  (sig ::= store)
  (store ::= (mu ro nu))
  (l number)
  (r ::=
     (l ...))
  (n ::= number)
  (o ::= v
     (app(- e))
     (ifz(- e e))
     (s(-))
     (app (e -))
     (app (l -))
     (app (l l))
     n
  )
  (blksz 4)
  (cachesize 8)
)

;;blocksize = 2 , cachesize (ro or mu) = 4

(define-judgment-form pcf
  #:contract (evdy sig e r n sig l) 
  #:mode (evdy I I I O O O)

  
  [
   (aljud sig z r n sig_2 l)
  ------------------------------- tz
    (evdy sig z r n sig_2 l)
  ]

 [
  (aljud sig (fun(x_1 x_2 e)) r n sig_2 l)
  -------------------------------------- tfun
   (evdy sig (fun(x_1 x_2 e)) r n sig_2 l)
  ]



  [
   (aljud sig (s(-)) (mergemem (r (locs e))) n_1 sig_ss l_ss) ;; stackframe for successor
   (evdy sig_ss e (mergemem (r (l_ss))) n_se sig_se l_se) ;; the inner expr of s(e)
   (aljud sig_se (s(l_se)) r n_sl sig_sl l_sl)
   (where n ,(+ (term n_1) (term n_se) (term n_sl)))
  --------------------------------------------------------------------- tsucc
   (evdy sig (s(e)) r n sig_sl l_sl)
  ]
  
  )


(define-judgment-form pcf
  #:contract(rjud sig l sig n o)
  #:mode(rjud I I O O O)

  [
       ----------------------------- read_ro
       (rjud (name sig_1 (mu ((l_1 o) ... (l_i o_i) (l_2 o_2) ... ) nu)) l_i sig_1 0 o_i)
  ]


  [
   ----------------------------- read_nu
     (rjud (name sig_1 (mu ro ((l_1 o) ... (l_i o_i) (l_2 o_2) ... ))) l_i sig_1 0 o_i)                         
   ]


  [  (side-condition (notin ((l_k o_k) ...) (l_i)))
     (side-condition (notin nu (l_i)))
     (side-condition ,(< (term (getl ((l_k o_k) ...) 0)) 12))
     (where ((l_x o_x) ...) (nbhd mu_1 l_i))
   --------------------------------------------------------------------------------------- read_nu_1
     (rjud  ((name mu_1 ((l_1 o_1) ... (l_i o_i) (l_2 o_2) ...)) ((l_k o_k) ...) nu)
            l_i (mu_1 ((l_k o_k) ... (l_x o_x) ...) nu ) 1 o_i)                         
   ]

    
  #;[  (side-condition(notin ((l_k o_k) ...) (l_i)))
     (side-condition(notin nu (l_i)))
     (side-condition ,(< (term (getl ((l_k o_k) ...) 0)) 12))
     (where ((l_x o_x) ...) (nbhd mu_1 l_i))
   --------------------------------------------------------------------------------------- read_nu_2
     (rjud  ((name mu_1 ((l_1 o_1) ... (l_i o_i) (l_2 o_2) ...)) ((l_k o_k) ...) nu)
            l_i (mu_1 ((l_k o_k) ... (l_x o_x) ...) nu ) 1 o_i)                         
   ]



  [(side-condition(notin ((l_k o_k) (l_k2 o_k2) ...) (l_i)))
     (side-condition(notin nu (l_i)))
     (side-condition ,(> (term (getl ((l_k o_k) (l_k2 o_k2) ...) 0)) 12))
     (where ((l_x o_x) ...) (nbhd mu_1 l_i))  ;; get the block containing our location as l_x o_x
     (where ((l_y o_y) ...) (nbhd ((l_k o_k) (l_k2 o_k2) ...) l_k)) ;; removing the first block from the read cache
     (where mu_2 (mergemem (mu_1 ( (l_y o_y) ...)))) ;;;; the new mu after merging the first block of read cache
     (where (((l_z o_z) ...) () ) (evict ((l_k o_k) (l_k2 o_k2) ...) ((l_y o_y) ...)))  ;;;; the new memory without appending the block
     (where ro_2 ((l_z o_z) ... (l_x o_x) ...))
   --------------------------------------------------------------------------------------- read_nu_2_2
     (rjud  ((name mu_1 ((l_1 o_1) ... (l_i o_i) (l_2 o_2) ...)) ((l_k o_k) (l_k2 o_k2) ...) nu) l_i (mu_2 ro_2 nu) 1 o_i)                              
   ]    
  )





(define-judgment-form pcf
  #:contract(aljud sig o r n sig l)
  #:mode(aljud I I I O O O)


  ;; search the roots for transitively available locations in the memory (live object enumeration)
  ;; if the total number of live objects is less than 16, we can do an allocation!
  ;; else we move to the next condition.

  [
  ;(side-condition ,(<= (term (getl (mergemem ((mergemem(r (locsfilter (locs(o))))) (extractlocs nu))) 0)) 16) )
  ;(side-condition ,(<= (term (getl (transitivereach nu (mergemem (r (locsfilter (locs o)))) ()) 0)) 16) )
  (where r_x (mergemem (r (locsfilter (locs o)))))
  (where r_xx (transitivereach nu r_x ()))
  (side-condition ,(< (term (getl r_xx 0)) 16))
  (where l (lgen))
  (where nu_2 ((l_1 o_1) ... (l o)))
  ------------------------------------ allocation
   (aljud (name sig_1 (mu ro (name nu ((l_1 o_1) ...)))) o r 0 (mu ro nu_2) l)
  ]

[
  
  (where r_x (mergemem (r (locsfilter (locs o)))))
  (where r_xx (transitivereach nu r_x ()))
  (side-condition ,(>= (term (getl r_xx 0)) 16))
  (where l (lgen))
  (where ((l_n o_n) ...) (nbhd nu l_1))
  (where (((l_nevicted o_nevicted) ...) ()) (evict nu ((l_n o_n) ...))) ;;; evict oldest block from nu
  (where nu_2 ((l_nevicted o_nevicted) ... (l o))) ;;; allocate the new one.just add object to the newly evicted nu.
  (where mu_2 (mergemem (mu ((l_n o_n) ...))))
  ------------------------------------ allocation_with_eviction
   (aljud (name sig_1 (mu ro (name nu ((l_1 o_1) (l_11 o_11) ...)))) o r 1 (mu_2 ro nu_2) l)
  ]

  
  )

;(judgment-holds (aljud (((1 2) (3 4)) () ((3 4)(5 6))) 33 (3 5) n sig l) l)


(define-metafunction pcf
  locs : any -> (l ...)
  [(locs (l)) (l)]
  [(locs l) (l)]
  [(locs (s(l))) (l)]
  [(locs (s(e))) (locs e)]
  [(locs (s(-))) ()]
  [(locs (app(l -))) (l)]
  [(locs (app(- l)))(l)]
  [(locs (app(e_1 e_2))) (mergemem ( (locs e_1) (locs e_2)))]
  [(locs (fun(l_1 l_2 e))) (locs e)]
  [(locs (fun(x_1 x_2 e))) (mergemem((locs e) (locsfilter ((locs x_1) (locs x_2))) ))]
  [(locs e) ()] ;; if e is none of the above, it is will not have a location
)

(define-metafunction pcf
  locsfilter : (any ...) -> (any ...)
  [(locsfilter (any ...))(locsfilterh (any ...) ())])

(define-metafunction pcf
  locsfilterh : (any ...) (any ...) -> (any ...)
  [(locsfilterh (() any_2 ...) (any_3 ...))(locsfilterh (any_2 ...) (any_3 ...))]
  [(locsfilterh (any_1 any_2 ...) (any_3 ...)) (locsfilterh (any_2 ...) (any_3 ... any_1))]
  [(locsfilterh () (any_3 ...)) (any_3 ...)])
  
  
(define-metafunction pcf
  lgen : -> any
  [(lgen) ,(random 9999999)]
  )
  
;;; Function that checks if 
(define-metafunction pcf
  notin : (any ...) (any) -> #t or #f
  [(notin (any_1 ... (any any_3) any_2 ...) (any)) #f]
  [(notin (any_1 ...  any_2 ...) (any)) #t])

( define-metafunction pcf
  getl : (any ...) n  -> any
  [(getl () n) n]
  [(getl (any any_1 ...) n ) (getl (any_1 ...) ,(+ (term n) 1))]
  )


( define-metafunction pcf
  findpos : (any ...) any n  -> n
  [(findpos ((any_1 any_1x) any_2 ...) any_1 n) n]
  [(findpos ((any any_2) any_1 ...) any_x n ) (findpos (any_1 ...) any_x ,(+ (term n) 1))]
  )



;;;;;;;;;;; merge the memory that is evicted into the main ;;;;;;;;;;;;;;;; removing all dups
(define-metafunction pcf
  mergemem : ((any ...) (any ...)) -> ((any ...) (any ...)) or (any ...)
  [(mergemem ((any_1 ...)())) (any_1 ...)]
  [(mergemem ((any_1 ... any any_2 ...) (any any_3 ...))) (mergemem ((any_1 ... any any_2 ...) (any_3 ...)))
   ]
 [(mergemem ((any_1 ...) (any_2 any_3 ...))) ( mergemem ((any_1 ... any_2) (any_3 ...)))]
)


(define-metafunction pcf
  nbhd : (any ...) l -> (any ...)
  [(nbhd (any ...) l) (nbhdhlp (any ...) ,(* (floor (/ (term (findpos (any ...) l 0))  4)) 4))]
  )

(define-metafunction pcf
  nbhdhlp : (any ...) n -> (any ...)
  [(nbhdhlp (any ...) 0 ) (any_1 ...)
                          (where ((any_2 ...) (any_1 ...) n) (nbhdhlp1 (any ...) () 4))]
  [(nbhdhlp (any any_2 ...) n) (nbhdhlp (any_2 ...) ,(- (term n) 1))]
  
  )


(define-metafunction pcf
  nbhdhlp1 : (any ...) (any ...) n -> (any ...)
  
  [(nbhdhlp1 () (any ...) n) (() (any ...) n)]
  [(nbhdhlp1 (any_1 ...) (any_2 ...) 0) ((any_1 ...) (any_2 ...) 0)]
  [(nbhdhlp1 (any_1 any_2 ...) (any_3 ...) n) (nbhdhlp1 (any_2 ...) (any_3 ... any_1) ,(- (term n) 1))]

  )


;; helper to find the neighborhood for eviction and read.
(term (nbhd ( (12 13) (14 25) (11 222) (1 2) (3 4) (5 6) (7 8) (9 10) (8 9) (77 89)) 77))

(define-metafunction pcf
  evict : (any ...) (any ...)  -> (any ...) 
  [(evict (any ...) ()) ((any ...) ())]
  [(evict (any ... any_2 any_3 ...) (any_2 any_4 ...)) (evict (any ... any_3 ...) (any_4 ...))]
  )





;;extract locations from a nursery
(define-metafunction pcf
  extractlocs : (any ...) -> (any ...)
  [(extractlocs ( (any_1 any_2) ...)) (any_1 ...)]
  )



;;transitivereach (nu) (roots) () returns all possible values reached through the roots in the nursery.
;; example transitivereach ( (1 2) (2 3) (3 4)) (1) () --> will output (1 2 3 4), since from 1 we can reach all 1 2 3 4 locations.
;; This is function essentially finds out the  LIVE elements of the nursery.

(define-metafunction pcf
  transitivereach : (any ...) (any ...)(any ...) -> (any ...)
  [(transitivereach ((l_1 o_1) ... (l o) (l_2 o_2) ...) (l l_x ...) (l_z ...))
   (transitivereach ((l_1 o_1) ... (l_2 o_2) ...) (l_x ... l_new ...) (l_z ... l))
   (where (l_new ...) (locsfilter ( locs o)))]
  [(transitivereach ((l_1 o_1) ... ) (l l_x ...) (l_z ...))
   (transitivereach ((l_1 o_1) ...) (l_x ...) (l_z ... l))]
  [(transitivereach () (any ...) (any_2 ...)) (any_2 ...)]
  [(transitivereach (any ...) () (any_1 ...)) (any_1 ...)]
  )


;;
;; 
(test-equal (term(transitivereach ((1 (app(2 2))) (2 3) (3 4)) (1) ())) '(1 2 3 4))
;; example where the path is not complete
(test-equal (term(transitivereach ((1 (app(2 2))) (2 3) (3 4) (5 6) (8 9) (4 7)) (1) ())) '(1 2 3 4 7))
;; example with path complete
(test-equal (term(transitivereach ((1 (app(2 2))) (2 3) (3 4) (5 6) (8 9) (4 7) (7 5)) (1) ())) '(1 2 3 4 7 5 6))

;; test for reading from allocation cache (nursery)
(test-equal (judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11)) ((1 2))) 1 sig n o) o) '(2))
;(test-equal (judgment-holds (rjud (((2 3) (3 5) (5 6)) ((8 9) (9 10) (1 2)) ()) 1 sig n o) o) '(2))
(term (evict ((1 2) (2 3) (4 31) (32 33)) ((2 3))))
;; reading a block from main with eviction.
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15) (111 222) (333 444) (555 666) (777 888) (999 111) (123 345) (567 789) (910 911)) ((11 22))) 1 sig n o) sig)
;; witout eviction
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15)) ((11 22))) 1 sig n o) sig)
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15)) ((11 22))) 1 sig n o) o)


;; Allocation in action, we insert a new object ( 33 ) into the nu with roots (1 2 ...) .
;; Allocation number is randomly selected using a helper function getl.
;; Since it is random, we cannot write a test-equals? for this, thus we will just print it here.
;; our function "transitivereach" takes into account all the possible paths
;; and finds all "live" locations as described in the paper.
;; The following example allocates at 0 cost since the number of "live" objects is just 3 and well less than 16 (cachesize).
(judgment-holds (aljud (() () ((1 2)  (3 4) (4 5) (5 6) (6 7) (7 8)
                                     (8 9) (9 10) (10 11) (11 12) (13 14)
                                     (12 13) (14 15) (15 16) (16 17) (17 18) (18 19) (19 20))) 33
                                     (1 2) n sig l) sig)

;; Allocation with eviction. This time the number of transitively reacheable objects is greater than 16, thus we evict a block!.
;; the form is (aljud (mu ro nu) o r n (mu ro nu)_out l)
;; The RAM (mu) will appear populated with blocks (1 2) ... (4 5).
;; the same blocks will appear evicted from the nursery (nu).
;; the nursery will have a new random location added along with the object. This signifies allocation.

(judgment-holds (aljud
                 (((1 2)) () ((1 2) (2 3) (3 4) (4 5) (5 6) (6 7) (7 8) (8 9)
                 (9 10) (10 11) (11 12) (13 14) (12 13) (14 15)
                 (15 16) (16 17) (17 18) (18 19) (19 20))) 33 (1 2)
                 n sig l) sig)

;;Allocation 
(judgment-holds (evdy (((1 2)) () ((1 2) (2 3) (3 4) (4 5))) (fun(y x (s(99)))) (1 2) n sig l ) sig)

(test-results)