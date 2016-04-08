#lang racket
(require redex)
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
     n
  )
  (blksz 4)
  (cachesize 8)
)

;;blocksize = 2 , cachesize (ro or mu) = 4

#;(define-judgment-form pcf
  #:contract (evdy sig e r n sig l) 
  #:mode (evdy I I I O O O)

  
  [
   (aljud sig z r n sig_2 l)
  ------------------------------- tz
    (evdy sig z r n sig l)
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
     ;(rjud  ((name mu_1 ((l_1 o_1) ... (l_i o_i) (l_2 o_2) ...)) ((l_k o_k) (l_k2 o_k2) ...) nu) l_i (mu_2 ro_2 nu) 1 o_i)
     (rjud  ((name mu_1 ((l_1 o_1) ... (l_i o_i) (l_2 o_2) ...)) ((l_k o_k) (l_k2 o_k2) ...) nu) l_i (mu_2 ro_2 nu) 1 o_i)                              
   ]    
  )





#;(define-judgment-form pcf
  #:contract(aljud sig o r n sig l)
  #:mode(aljud I I I O O O)


  [
   
  ------------------------------------ allocation
   (aljud sig o r n sig l)                                       
  ]

  )




(define-metafunction pcf
  locs : any -> (l ...)
  [(locs l) (l)]
  [(locs s(l)) (l) ]
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


;; test for reading from allocation cache (nursery)
(test-equal (judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11)) ((1 2))) 1 sig n o) o) '(2))
;(test-equal (judgment-holds (rjud (((2 3) (3 5) (5 6)) ((8 9) (9 10) (1 2)) ()) 1 sig n o) o) '(2))
(term (evict ((1 2) (2 3) (4 31) (32 33)) ((2 3))))
;; reading a block from main with eviction.
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15) (111 222) (333 444) (555 666) (777 888) (999 111) (123 345) (567 789) (910 911)) ((11 22))) 1 sig n o) sig)
;; witout eviction
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15)) ((11 22))) 1 sig n o) sig)
(judgment-holds (rjud (((1 2) (2 3) (3 5) (5 6)) ((8 9) (9 10) (10 11) (6 9) (12 12) (11 11) (14 15)) ((11 22))) 1 sig n o) o)
(test-results)