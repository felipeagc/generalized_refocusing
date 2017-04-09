Require Import Fin.

Parameters 
(entropy  : Set)
(draw_fin : entropy -> forall n, Fin.t n).

Axioms
(draw_fin_correct : forall n m, exists e, draw_fin e n = m)
(entropy_exists   : exists (_ : entropy), True).
