Require Import Subset
               abstract_machine_facts
               lam_ses_no.

Module Example.

  Module Sim := DetAbstractMachine_Sim Lam_SES_NO_EAM.
  Import Lam_SES_NO_EAM Lam_SES_NO_PreRefSem.


  Definition t1 := Lam (App (Lam (Lam (Var 1))) (Var 0)).


  Eval compute in 
    Sim.n_steps 
    ( load t1 )
    17.


  Fixpoint nat_term n :=
    match n with
    | 0   => Lam (Lam (Var 0))
    | S n => Lam (Lam (App (Var 1) (App (App (nat_term n) (Var 1)) (Var 0))))
    end.


  Definition add_term := 
      Lam (Lam (Lam (Lam 
          (App (App (Var 3) 
              (Var 1)) 
              (App (App (Var 2) (Var 1)) (Var 0)))))).


  Eval compute in
      Sim.n_steps 
      ( load (App (App add_term (nat_term 3)) (nat_term 4)) ) 
      1890.

End Example.
