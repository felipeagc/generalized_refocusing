
Require Import Relations
               Program
               rewriting_system.
Require Export path.

Module Type RED_MINI_LANG.
  Parameters
  (term          : Type) (* the language *)
  (ckind         : Type) (* the set of reduction/context kinds *)
  (elem_context_kinded : ckind -> ckind -> Type)
                        (* for each k1 k2, elem_context_kinded k1 k2 defines *)
                        (* the set of elementary contexts, ec, such that *)
                        (* k1 -> ec[k2] is an instance of a production in the *)
                        (* grammar of reduction contexts. Usually it should be *)
                        (* defined by an inductive type, where each constructor *)
                        (* corresponds to a production in the grammar and returns *)
                        (* its instances. Eventually a constructor can correspond *)
                        (* to a pattern of productions, e.g., if there is *)
                        (* a production k -> ec[k0] for each k : ckind, then *)
                        (* all this productions can be represented by a single *)
                        (* constructor that takes k as its parameter. *)
  (elem_plug     : forall {k0 k1}, term -> elem_context_kinded k0 k1 -> term)
                        (* the function that plugs a term into an elementary context *)
  (redex         : ckind -> Type)
                        (* the set of representations of potential redexes of a kind *)
  (value         : ckind -> Type)
                        (* the set of repressentations of values of a kind *)
  (redex_to_term : forall {k}, redex k -> term)
  (value_to_term : forall {k}, value k -> term).
                        (* coercions from represenations of redexes and values *)
                        (* into terms *)
End RED_MINI_LANG.

Module RED_MINI_LANG_Notions (Import R : RED_MINI_LANG).

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.


  (* Definition of contexts as stacks of productions *)
  (* The first parameter of the type is the nonterminal generating the whole *)
  (* context, the second is the kind of the hole. *)
  (* We use inside-out representation of contexts, so the topmost symbol on the stack *)
  (* is the elementary context that is closest to the hole. *)
  Definition context : ckind -> ckind -> Type := path elem_context_kinded.

  Notation "[.]( k )" := (@empty _ elem_context_kinded k).

  (* The function for plugging a term into an arbitrary context *)
  (* I.e., (ec1=:ec2=:..ecn)[t] = ecn[..ec2[ec1:[t]]..] *)
  Definition plug t {k1 k2} (c : context k1 k2) : term :=
    path_action (@elem_plug) t c.
  Notation "c [ t ]" := (plug t c) (at level 0).

  Definition plug_empty : forall t k, [.](k)[t] = t :=
    @action_empty _ _ _ (@elem_plug).

  Definition plug_compose : forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t,
          (c0 ~+ c1)[t] = c1[c0[t]] :=
    @action_compose _ _ _ (@elem_plug).

  (* Here we define what it means that an elementary context ec is a prefix of *)
  (* a term t. *) 
  Definition immediate_ec {k0 k1} (ec : elem_context_kinded k0 k1) t := 
      exists t', ec:[t'] = t.

  (* The same for immediate subterms *)
  Definition immediate_subterm t0 t := exists k1 k2 (ec : elem_context_kinded k1 k2),
      t = ec:[t0].

  (* Subterm order is the transitive closure of the immediate_subterm relation. *)
  Definition subterm_order          := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2"  := (subterm_order t1 t2)      (no associativity, at level 70).

  (* Decomposition of a term is a pair consisting of a reduction context and *)
  (* a potential redex. Values have no decomposition; we just report that *)
  (* the term is a value. *)
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


  (* Syntactic sugar: term t decomposes to decomposition d *)
  Definition dec (t : term) k (d : decomp k) : Prop := 
      t = d.

End RED_MINI_LANG_Notions.

Module Type RED_SEM_BASE.
  Include RED_MINI_LANG.
  Parameters
  (init_ckind    : ckind)
                        (* the starting nonterminal in the grammar of reduction *)
                        (* contexts *)
  (contract      : forall {k}, redex k -> option term).
                        (* the contraction relations per each reduction kind *)
End RED_SEM_BASE.

Module RED_SEM_BASE_Notions (Import R : RED_SEM_BASE).
  Include RED_MINI_LANG_Notions R.

  (* Here we define the reduction relation. Term t1 reduces to t2 wrt. k-strategy *)
  (* if t1 decomposes to r : redex k' and c : context k k', and r rewrites (wrt. *)
  (* k'-contraction) to t and t2 = c[t]. *)
  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  (* Reduction relation gives an instance of a rewriting system *) 
  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }.
  Instance rws : REWRITING_SYSTEM term :=
  { transition := reduce init_ckind }.

  (* Again some technicalities *)
  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  {
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End RED_SEM_BASE_Notions.

(* A signature that formalizes a reduction semantics *)

Module Type PRE_RED_SEM.

  Include RED_SEM_BASE.
  Include RED_SEM_BASE_Notions.

  Axioms

  (* Some technicalities: the two coercions are injective *)
  (value_to_term_injective :                                 forall {k} (v v' : value k),
       value_to_term v = value_to_term v' -> v = v')

  (redex_to_term_injective :                                 forall {k} (r r' : redex k),
       redex_to_term r = redex_to_term r' -> r = r')


  (* Again a technicality: the plug function is injective wrt. a plugged term. *)
  (elem_plug_injective1 :          forall {k1 k2} (ec : elem_context_kinded k1 k2) t1 t2,
       ec:[t1] = ec:[t2] -> t1 = t2)


  (* Decomposition of a value cannot give a potential redex, it must give a value. *)
  (value_trivial1 :                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v  ->  exists (v' : value k2), t = v')


  (* A value is not a redex. *)
  (value_redex :                                                              forall {k},
       forall (v : value k) (r : redex k), value_to_term v <> redex_to_term r)

  (redex_trivial1 :        forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v)

  (wf_immediate_subterm : well_founded immediate_subterm)

  (wf_subterm_order     : well_founded subterm_order).

End PRE_RED_SEM.

Module Type RED_SEM.
  Include PRE_RED_SEM.

  (* Each term (t) can be decomposed wrt. to each substrategy (k) *)
  Axiom decompose_total : forall k t, exists d : decomp k, dec t k d.
End RED_SEM.


(* A signature that formalizes a deterministic reduction semantics *)

Module Type RED_SEM_DET (Import R : RED_SEM).

  Axiom dec_is_det :                                      forall {k} t (d d0 : decomp k),
      dec t k d -> dec t k d0 -> d = d0.
End RED_SEM_DET.
