type 'v term = Var of 'v | App of 'v term * 'v term | 
      Lam of ('v incr) term 
     and 
     'v incr = Zero | Succ of 'v
;;
Lam(Lam(Lam(App(App(Var(Succ Zero),Var Zero),Var(Succ(Succ(Zero)))))));;
