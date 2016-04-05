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
  )
)

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


  [
   ----------------------------- read_nu_1
     (rjud (name sig_1 (mu ro ((l_1 o) ... (l_i o_i) (l_2 o_2) ... ))) l_i sig_1 0 o_i)                         
   ]

  
  )

(define-metafunction pcf
  mergemem : ((any ...) (any ...)) -> ((any ...) (any ...))
  [(mergemem ((any_1 ...)())) ((any_1 ...) ())]
  [(mergemem ((any_1 ... any any_2 ...) (any any_3 ...))) (mergemem ((any_1 ... any any_2 ...) (any_3 ...)))
   ]
 [(mergemem ((any_1 ...) (any_2 any_3 ...))) ( mergemem ((any_1 ... any_2) (any_3 ...)))]
)

#;(define-judgment-form pcf
  #:contract(aljud sig o r n sig l)
  #:mode(aljud I I I O O O)


  [
   
  ------------------------------------ allocation
   (aljud sig o r n sig l)                                       
  ]

  )