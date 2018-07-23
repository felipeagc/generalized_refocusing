Require Import Relations.



Class REWRITING_SYSTEM (configuration : Type) :=
{
    transition : configuration -> configuration -> Prop
}.


Notation "`( rw ) c1 → c2"  := (@transition _ rw c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "`( rw ) c1 →+ c2" := (clos_trans_1n _ (@transition _ rw) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "`( rw ) c1 →* c2" := (clos_refl_trans_1n _ (@transition _ rw) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).

Notation "c1 → c2"  := (transition c1 c2)                (no associativity, at level 70).
Notation "c1 →+ c2" := (clos_trans_1n _ transition c1 c2)
                                                         (no associativity, at level 70).
Notation "c1 →* c2" := (clos_refl_trans_1n _ transition c1 c2)
                                                         (no associativity, at level 70).



Class LABELED_REWRITING_SYSTEM (label configuration : Type) :=
{
    ltransition : label -> configuration -> configuration -> Prop
}.


Notation "`( rw ) l |~ c1 → c2"  := (@ltransition _ _ rw l c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).
Notation "`( rw ) l |~ c1 →+ c2" := (clos_trans_1n _ (@ltransition _ _ rw l) c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).
Notation "`( rw ) l |~ c1 →* c2" := (clos_refl_trans_1n _ (@ltransition _ _ rw l) c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).

Notation "l |~ c1 → c2"  := (ltransition l c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "l |~ c1 →+ c2" := (clos_trans_1n _ (ltransition l) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "l |~ c1 →* c2" := (clos_refl_trans_1n _ (ltransition l) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).



Instance RWS_is_LRWS                                                               {conf}
    `(REWRITING_SYSTEM conf) : LABELED_REWRITING_SYSTEM unit conf :=
{
    ltransition := fun (_ : unit) => transition
}.




Module Paths.

  Require Import Program.
  Require Export Fin2 Vector2.
  Open Local Scope vector.


Section RWS.

  Context {conf : Type}.
  Context `(REWRITING_SYSTEM conf).


  Definition path_in                                                                  {n}
      (cs : Vector.t conf n) : Prop :=

      match cs with
      | []          => False
      | @cons _ c n cs => forall m : Fin.t n, (c::cs)[@m] → cs[@m]
      end.


  Lemma path_in_snoc :                           forall {n} (cs : Vector.t conf (S n)) c,
      path_in cs -> (last cs) → c -> path_in (cs ++ [c]).

  Proof.
    intros n cs c H0 H1.
    dependent destruction cs.
    revert h H0 H1.
    induction cs; 
        intros c0 H0 H1 m.
    - dependent destruction m.
      + auto.
      + inversion m.
    - dependent destruction m.
      + apply (H0 Fin.F1).
      + apply IHcs.
        * intro m0; apply (H0 (Fin.FS m0)).
        * auto.
  Qed.

End RWS.


Section LRWS.

  Context {label : Set} {conf : Type}.
  Context `(LABELED_REWRITING_SYSTEM label conf).

  Definition lpath_in                                                                 {n}
      (cs : Vector.t conf (S n)) (ls : Vector.t label n) : Prop :=

      match cs in Vector.t _ n return Vector.t label (pred n) -> Prop with
      | []          => fun _  => False
      | @cons _ c n cs => fun ls => forall m : Fin.t n, ls[@m] |~ (c::cs)[@m] → cs[@m]
      end ls.


  Lemma lpath_in_snoc :                             forall {n} (cs : Vector.t conf (S n))
                                                             (ls : Vector.t label n) l c,
      lpath_in cs ls  ->  l |~ (last cs) → c  ->  lpath_in (cs ++ [c]) (ls ++ [l]).

  Proof.
    intros n cs ls l c H0 H1.
    dependent destruction cs.
    revert h H0 H1.
    induction cs; 
        intros c0 H0 H1 m;
        dependent destruction ls.
    - dependent destruction m.
      + auto.
      + inversion m.
    - dependent destruction m.
      + apply (H0 Fin.F1).
      + apply IHcs.
        * intro m0; apply (H0 (Fin.FS m0)).
        * auto.
  Qed.

End LRWS.


  Definition path  := @path_in.   Arguments path  {conf}         {rws}  {n} _   : rename.
  Definition lpath := @lpath_in.  Arguments lpath {label} {conf} {lrws} {n} _ _ : rename.
  Definition path_snoc := @path_in_snoc.   Arguments path_snoc 
                                                       {conf} {rws} {n} _ _ _ _ : rename.
  Definition lpath_snoc := @lpath_in_snoc. Arguments lpath_snoc 
                                                {conf} {lrws} {m} _ _ _ _ _ _ _ : rename.

End Paths.
