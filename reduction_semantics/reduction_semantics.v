
Require Import Relations
               Program.
Require Export rewriting_system.




(* Signature for languages with reduction semantics. *)

Module Type RED_SEM.

  Parameters
  (term          : Set)
  (ckind         : Set)
  (elem_context_kinded : ckind -> ckind -> Set)
  (elem_plug     : forall {k0 k1}, term -> elem_context_kinded k0 k1 -> term)
  (redex         : ckind -> Set)
  (value         : ckind -> Set)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term)
  (init_ckind    : ckind)
  (contract      : forall {k}, redex k -> option term).

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons :                                                                forall {k2 k3}
            (ec : elem_context_kinded k2 k3), context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1} {k2} {k3} _ _.
  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).

  Definition immediate_ec {k0 k1} (ec : elem_context_kinded k0 k1) t := 
      exists t', ec:[t'] = t.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
      t = d.

  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].

  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }.

  Instance rws : REWRITING_SYSTEM term :=
  { transition := reduce init_ckind }.


  Axioms

  (value_to_term_injective :                                 forall {k} (v v' : value k),
       value_to_term v = value_to_term v' -> v = v')

  (redex_to_term_injective :                                 forall {k} (r r' : redex k),
       redex_to_term r = redex_to_term r' -> r = r')

  (elem_plug_injective1 :          forall {k1 k2} (ec : elem_context_kinded k1 k2) t1 t2,
       ec:[t1] = ec:[t2] -> t1 = t2)

  (value_trivial1 :                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v  ->  exists (v' : value k2), t = v')

  (value_redex :                                                              forall {k},
       forall (v : value k) (r : redex k), value_to_term v <> redex_to_term r)

  (decompose_total :                                                          forall k t,
       exists d : decomp k, dec t k d).


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  {
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End RED_SEM.




Module Type RED_SEM_DET (R : RED_SEM).

  Import R.

  Axiom dec_is_det :                                      forall {k} t (d d0 : decomp k),
      dec t k d -> dec t k d0 -> d = d0.

End RED_SEM_DET.
