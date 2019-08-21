Require Import Util.
Require Import Program.
Require Import rewriting_system refocusing_semantics.
Require Import reduction_languages_facts.



Require Import EqdepFacts.

Module RED_REF_SEM_Facts (Import R' : RED_REF_SEM).

  Lemma refocus_in_is_pfunction :             forall t {k1 k2} (c : context k1 k2) d0 d1,
      refocus_in t c d0 -> refocus_in t c d1 -> d0 = d1.

  Proof.
    intros t k1 k2 c d0 d1 DE0 DE1. revert d1 DE1.


    induction DE0 using refocus_in_Ind with 
    (P  := fun _ t c d _ => forall d1, refocus_in  t c d1    -> d = d1)
    (P0 := fun _ v c d _ => forall d1, refocus_out v c d1 -> d = d1);

    intros;
    (* automated cases *)
    match goal with

    | [ RD : (refocus_in ?t ?c ?d), DT1 : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                 rewrite DT2 in DT1; inversion DT1 end

    | [ RC : (refocus_out ?v (?ec=:?c) ?d), DC1 : (dec_context ?ec ?v = _) |- _ ] => 
             dependent_destruction2 RC; (*inversion_pcons x2;*) dep_subst;
             match goal with DC2 : (dec_context ?ec' ?v' = _) |- _ => 
                 rewrite DC2 in DC1; inversion DC1 end

    | [ RC : (refocus_out ?v [.] ?d) |- _] => 
             dependent_destruction2 RC

    end;

    subst; 
try solve 
[ eauto 
|  
eapply IHDE0; 
match goal with
| [ H : existT _ _ ?ec = existT _ _ ?e, 
     H0 : refocus_in ?t (?ec =: ?c) ?d |- refocus_in ?t (?e =: ?c) ?d ] => dependent rewrite H in H0; auto
     end ].
     
  Qed.



  Lemma dec_is_det :                                   forall t {k} (d0 d1 : decomp k),
      dec t k d0 -> dec t k d1 -> d0 = d1.

  Proof with auto.
    intros t k d0 d1 H H0.
    rewrite <- (plug_empty t k) in H, H0.
    apply refocus_in_eqv_dec in H...
    apply refocus_in_eqv_dec in H0...
    eauto 10 using refocus_in_is_pfunction.
  Qed.


End RED_REF_SEM_Facts.