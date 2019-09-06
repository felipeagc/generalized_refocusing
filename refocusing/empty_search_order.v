Require Import RelationClasses
               Program
               refocusing_semantics.

Module Empty_search_order
  (Import R : PRE_RED_SEM)
  (Import RF: RED_STRATEGY_STEP_FUNCTIONS R).

  Inductive elem_context_in k : Type := 
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.

  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop := False.

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

  Lemma dec_term_term_top : forall {k k'} t t' (ec : elem_context_kinded k k'),
          dec_term t k = ed_dec _ t' ec -> so_maximal ec t.
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma dec_context_val_bot : forall {k k'} (v : value k') {v' : value k}
      (ec : elem_context_kinded k k'),
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma elem_context_det :         forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].
  Proof. intros ? ? ? t ec0 ec1 []. Qed.

  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. intros ? ? ?. apply Acc_intro. intros _ []. Qed.

  Lemma search_order_trans : forall k t, Transitive (search_order k t).
  Proof. intros ? ? ? ? ? []. Qed.

  Lemma search_order_comp_fi :
      forall t k k' k'' (ec0 : elem_context_kinded k k')
                        (ec1 : elem_context_kinded k k''),
          k, t |~ ec0 << ec1 ->
              immediate_ec ec0 t /\ immediate_ec ec1 t.
  Proof. intros ? ? ? ? ? ? []. Qed.

End Empty_search_order.