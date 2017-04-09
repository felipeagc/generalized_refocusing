Require Import Util
               Entropy.
Require Export rewriting_system.




Module Type ABSTRACT_MACHINE.

  Parameters 
  (term          : Set)
  (configuration : Set)
  (value         : Set)

  (load          : term -> configuration)
  (final         : configuration -> option value)
  (transition    : configuration -> configuration -> Prop)
  (next_conf     : entropy -> configuration -> option configuration).

  Definition is_final c := exists v, final c = Some v.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2).



  Class SafeRegion (P : configuration -> Prop) :=
  {
      preservation :                                                        forall c1 c2,
          P c1  ->  c1 → c2  ->  P c2;
      progress :                                                               forall c1,
          P c1  ->  (is_final c1) \/ (exists c2, c1 → c2)
  }.

End ABSTRACT_MACHINE.




Module Type DET_ABSTRACT_MACHINE.

  Include ABSTRACT_MACHINE.

  Parameter dnext_conf : configuration -> option configuration.
  Axiom dnext_is_next  : forall e c, next_conf e c = dnext_conf c.

End DET_ABSTRACT_MACHINE.

