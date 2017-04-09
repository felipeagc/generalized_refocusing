Require Import lam_cl_es_no
               abstract_machine_facts.




Module Sim := DetAbstractMachine_Sim Lam_ClES_NO_EAM.

Import Lam_ClES_NO_EAM.
Import Lam_ClES_NO_PreRefSem Lam_ClES_NO_Strategy.


Example t1 := Lam0 (App0 (Lam0 (Lam0 (Var0 1))) (Var0 0)).


Eval compute in
    Sim.n_steps
    ( load (t1 @ nil : term) )
    14.


Eval compute in 
    Sim.n_steps 
    ( load (Lam0 (App0  t1  (Var0 0) ) @ nil : term) )
    20.


Fixpoint nat_term0 n :=
    match n with
    | 0   => Lam0 (Lam0 (Var0 0))
    | S n => Lam0 (Lam0 (App0 (Var0 1) (App0 (App0 (nat_term0 n) (Var0 1)) (Var0 0))))
    end.


Definition add_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0 
        (App0 (App0 (Var0 3) 
            (Var0 1)) 
            (App0 (App0 (Var0 2) (Var0 1)) (Var0 0)))))).

Definition mul_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0
        (App0 (App0

        (App0 (App0 (Var0 2) 
            (Lam0 (App0 (App0 add_term0 (Var0 4)) (Var0 0)) ))
            (nat_term0 0))

        (Var0 1)) (Var0 0))))).


Eval compute in
    Sim.n_steps 
    ( load (App0 (App0 mul_term0 (nat_term0 3)) (nat_term0 4) @ nil : term) ) 
    672.

