
Module Type RED_STRATEGY_LANG.

 Parameters 
  (term         : Type)
  (ckind        : Type)
  (elem_context_kinded : ckind -> ckind -> Type)
  (elem_plug     : forall {k0 k1}, term -> elem_context_kinded k0 k1 -> term)
  (redex         : ckind -> Type)
  (value         : ckind -> Type)
  (init_ckind : ckind)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term).

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.


  Inductive context (k1 : ckind) : ckind -> Type :=
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

  Inductive decomp k : Type :=
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
       forall (v : value k) (r : redex k), value_to_term v <> redex_to_term r).

End RED_STRATEGY_LANG.



Module Type RED_STRATEGY_STEP (R : RED_STRATEGY_LANG).

  Import R.


  Inductive elem_dec k : Type :=
  | ed_red : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val : value k -> elem_dec k.

  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.

  (* dec_term t k          - one step of decomposition of t considered in the hole of
                             the kind k if we have no information about subterms of t.
                             Proper domain:  term * { k : ckind | k is not dead }
     dec_context k k' ec v - one step of decomposition of a term ec[v] considered in
                             the hole of the kind k after finding out that v is a value.
  *)
  Parameters
  (dec_term    : term -> forall k, elem_dec k)
  (dec_context :                                                           forall {k k'},
                 elem_context_kinded k k' -> value k' -> elem_dec k).


  Axioms
  (dec_term_correct :
       forall t k, match dec_term t k with
       | ed_red r      => t = r
       | ed_val v      => t = v
       | ed_dec _ t' ec => t = ec:[t']
       end)

   (dec_context_correct :                forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r      => ec:[v] = r
      | ed_val v'     => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
       end).

End RED_STRATEGY_STEP.



Module Type RED_STRATEGY (R : RED_STRATEGY_LANG).

  Import R.

  Include RED_STRATEGY_STEP R.


  Inductive elem_context_in k : Type := 
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.

  Parameter search_order : 
      forall k : ckind, term -> elem_context_in k -> elem_context_in k -> Prop.

  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
                                (at level 70, t, ec1, ec2 at level 50, no associativity).

  Definition so_maximal {k} (ec : elem_context_in k) t :=
       forall (ec' : elem_context_in k), ~ t |~ ec << ec'.
  Definition so_minimal {k} (ec : elem_context_in k) t :=
       forall (ec' : elem_context_in k), ~ t |~ ec' << ec.
  Definition so_predecessor                                                           {k}
      (ec0 : elem_context_in k) (ec1 : elem_context_in k) t :=

      (*1*) t |~ ec0 << ec1 /\
      (*2*)                                              forall (ec : elem_context_in k),
            t |~ ec << ec1  ->  ~ t |~ ec0 << ec.
  Hint Unfold so_maximal so_minimal so_predecessor.


  Axioms
  (dec_term_term_top :                                                 forall {k k'} t t'
                                                         (ec : elem_context_kinded k k'),

          dec_term t k = ed_dec _ t' ec -> so_maximal ec t)


  (dec_context_red_bot :                       forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),

          dec_context ec v = ed_red r -> so_minimal ec ec:[v])


  (dec_context_val_bot :                      forall {k k'} (v : value k') {v' : value k}
                                                         (ec : elem_context_kinded k k'),

      dec_context ec v = ed_val v' -> so_minimal ec ec:[v])


  (dec_context_term_next :                            forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v])


  (elem_context_det :               forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v]).

End RED_STRATEGY.