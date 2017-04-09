
Require Import Relations
               Program.
Require Export rewriting_system.




(* Signature for languages with reduction semantics. *)

Module Type RED_SEM.

  Parameters 
  (term         : Set)
  (ckind        : Set)
  (elem_context : Set)
  (elem_context_kinded : ckind -> ckind -> Set)
 (*  (ckind_trans  : ckind -> elem_context -> ckind)*)
  (elem_plug     : term -> elem_context -> term)
  (redex         : ckind -> Set)
  (value         : ckind -> Set)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term)
  (erase_kinds : forall {k1 k2} (ec : elem_context_kinded k1 k2), elem_context)
  (init_ckind    : ckind)
(*  (dead_ckind    : ckind -> Prop)*)
.

(*  Infix "+>"           := ckind_trans (at level 50, left associativity).*)
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall {k2 k3} {ec : elem_context_kinded k2 k3}, context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1} {k2} {k3} _ _.
  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} :
                       context k3 k1 -> context k3 k2:=
fun c1 =>
match c0 with
| @empty _=> c1
| ec0 =: c2 => ec0 =: compose c2 c1
end.

(*

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
*)

  Infix "~+" := compose (at level 60, right associativity).

  Coercion erase_kinds : elem_context_kinded >-> elem_context.
  
  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).

  Definition immediate_ec ec t := exists t', ec:[t'] = t.

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


  Parameter contract : forall {k}, redex k -> forall {k'}, context k' k -> option term.

  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r c = Some t /\ t2 = c[t].

  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }.

  Instance rws : REWRITING_SYSTEM term :=
  { transition := reduce init_ckind }.


  Axioms

  (value_to_term_injective :                                 forall {k} (v v' : value k),
       value_to_term v = value_to_term v' -> v = v')

  (redex_to_term_injective :                                 forall {k} (r r' : redex k),
       redex_to_term r = redex_to_term r' -> r = r')

  (elem_plug_injective1 :                                                forall ec t0 t1,
       ec:[t0] = ec:[t1] -> t0 = t1)

  (value_trivial1 :                                                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v -> 
           exists (v' : value k2), t = v')

  (value_redex :                                                              forall {k},
       forall (v : value k) (r : redex k), value_to_term v <> redex_to_term r)

  (decompose_total :                                                                forall t k,
       exists d : decomp k, dec t k d).


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End RED_SEM.




Module Type RED_SEM_DET (R : RED_SEM). Import R.

  Axiom dec_is_det :                                      forall {t k} {d d0 : decomp k},
      dec t k d -> dec t k d0 -> d = d0.

End RED_SEM_DET.
