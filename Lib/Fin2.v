Require Export Fin.


Fixpoint fin_lift1 {n} (m : Fin.t n) : Fin.t (S n) := 
    match m with
    | @Fin.F1 n => @Fin.F1 (S n)
    |  Fin.FS m => Fin.FS (fin_lift1 m)
    end.

Fixpoint fin_to_nat {n} (m : Fin.t n) : nat :=
    match m with
    | Fin.F1   => 0
    | Fin.FS m => S (fin_to_nat m)
    end.

Coercion fin_lift1  : Fin.t >-> Fin.t.
Coercion fin_to_nat : Fin.t >-> nat.