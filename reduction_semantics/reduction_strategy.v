Require Import path
               reduction_semantics.

Module RED_STRATEGY_STEP_Notions (Import R : RED_SEM_BASE).

  (* Up arrow and down arrow functions return that the input term is *)
  (* either a redex (ed_red) or a value (ed_val) or that we have to  *)
  (* continue searching inside a subterm (ed_dec) *)
  Inductive elem_dec k : Type :=
  | ed_red : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val : value k -> elem_dec k.

  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.

  Definition elem_rec {k} (d : elem_dec k) : term :=
    match d with
    | ed_red r       => redex_to_term r
    | ed_val v       => value_to_term v
    | ed_dec _ t' ec => elem_plug t' ec
    end.

End RED_STRATEGY_STEP_Notions.

Module Type RED_STRATEGY_LANG.

  Include RED_SEM_BASE.

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.

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

Module Type RED_STRATEGY_STEP (Import R : RED_STRATEGY_LANG).

  Include RED_STRATEGY_STEP_Notions R.

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
  (dec_term_correct : forall t k, t = elem_rec (dec_term t k))

  (dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v)).

End RED_STRATEGY_STEP.



Module Type RED_STRATEGY (Import R : RED_STRATEGY_LANG).

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