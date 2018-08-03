
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type 'a sumor =
| Inleft of 'a
| Inright

(** val add : int -> int -> int **)

let rec add = ( + )

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

type 'configuration rEWRITING_SYSTEM =
| Build_REWRITING_SYSTEM

type ('label, 'configuration) lABELED_REWRITING_SYSTEM =
| Build_LABELED_REWRITING_SYSTEM

module type RED_MINI_LANG =
 sig
  type term

  type ckind

  type elem_context_kinded

  val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term

  type redex

  type value

  val value_to_term : ckind -> value -> term

  val redex_to_term : ckind -> redex -> term

  type context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  val context_rect :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val context_rec :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val compose : ckind -> ckind -> context -> ckind -> context -> context

  val plug : term -> ckind -> ckind -> context -> term
 end

module RED_LANG_Facts =
 functor (R:RED_MINI_LANG) ->
 struct
 end

module type RED_MINI_LANG_WD =
 sig
  type term

  type ckind

  type elem_context_kinded

  val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term

  type redex

  type value

  val value_to_term : ckind -> value -> term

  val redex_to_term : ckind -> redex -> term

  type context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  val context_rect :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val context_rec :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val compose : ckind -> ckind -> context -> ckind -> context -> context

  val plug : term -> ckind -> ckind -> context -> term

  type decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  val decomp_rect :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_rec :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_to_term : ckind -> decomp -> term
 end

module RedDecProcEqvDec =
 functor (R:RED_MINI_LANG_WD) ->
 struct
  module RF = RED_LANG_Facts(R)
 end

module type RED_SEM =
 sig
  type term

  type ckind

  type elem_context_kinded

  val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term

  type redex

  type value

  val redex_to_term : ckind -> redex -> term

  val value_to_term : ckind -> value -> term

  val init_ckind : ckind

  val contract : ckind -> redex -> term option

  type context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  val context_rect :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val context_rec :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val plug : term -> ckind -> ckind -> context -> term

  val compose : ckind -> ckind -> context -> ckind -> context -> context

  type decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  val decomp_rect :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_rec :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_to_term : ckind -> decomp -> term

  val lrws : (ckind, term) lABELED_REWRITING_SYSTEM

  val rws : term rEWRITING_SYSTEM
 end

module type PRE_REF_SEM =
 sig
  type term

  type ckind

  type elem_context_kinded

  val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term

  type redex

  type value

  val init_ckind : ckind

  val value_to_term : ckind -> value -> term

  val redex_to_term : ckind -> redex -> term

  type context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  val context_rect :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val context_rec :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val compose : ckind -> ckind -> context -> ckind -> context -> context

  val plug : term -> ckind -> ckind -> context -> term

  type decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  val decomp_rect :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_rec :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_to_term : ckind -> decomp -> term

  val contract : ckind -> redex -> term option

  val lrws : (ckind, term) lABELED_REWRITING_SYSTEM

  val rws : term rEWRITING_SYSTEM
 end

module type RED_REF_SEM =
 sig
  module R :
   RED_SEM

  module ST :
   sig
    type elem_dec =
    | Coq_ed_red of R.redex
    | Coq_ed_dec of R.ckind * R.term * R.elem_context_kinded
    | Coq_ed_val of R.value

    val elem_dec_rect :
      R.ckind -> (R.redex -> 'a1) -> (R.ckind -> R.term -> R.elem_context_kinded ->
      'a1) -> (R.value -> 'a1) -> elem_dec -> 'a1

    val elem_dec_rec :
      R.ckind -> (R.redex -> 'a1) -> (R.ckind -> R.term -> R.elem_context_kinded ->
      'a1) -> (R.value -> 'a1) -> elem_dec -> 'a1

    val dec_term : R.term -> R.ckind -> elem_dec

    val dec_context :
      R.ckind -> R.ckind -> R.elem_context_kinded -> R.value -> elem_dec
   end

  type term = R.term

  type ckind = R.ckind

  type elem_context_kinded = R.elem_context_kinded

  val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term

  type redex = R.redex

  type value = R.value

  val redex_to_term : ckind -> redex -> term

  val value_to_term : ckind -> value -> term

  val init_ckind : ckind

  val contract : ckind -> redex -> term option

  type context = R.context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  val context_rect :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val context_rec :
    ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 -> 'a1)
    -> ckind -> context -> 'a1

  val plug : term -> ckind -> ckind -> context -> term

  val compose : ckind -> ckind -> context -> ckind -> context -> context

  type decomp = R.decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  val decomp_rect :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_rec :
    ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1

  val decomp_to_term : ckind -> decomp -> term

  val lrws : (ckind, term) lABELED_REWRITING_SYSTEM

  val rws : term rEWRITING_SYSTEM
 end

module RedRefSem =
 functor (PR:PRE_REF_SEM) ->
 functor (ST:sig
  type elem_dec =
  | Coq_ed_red of PR.redex
  | Coq_ed_dec of PR.ckind * PR.term * PR.elem_context_kinded
  | Coq_ed_val of PR.value

  val elem_dec_rect :
    PR.ckind -> (PR.redex -> 'a1) -> (PR.ckind -> PR.term -> PR.elem_context_kinded
    -> 'a1) -> (PR.value -> 'a1) -> elem_dec -> 'a1

  val elem_dec_rec :
    PR.ckind -> (PR.redex -> 'a1) -> (PR.ckind -> PR.term -> PR.elem_context_kinded
    -> 'a1) -> (PR.value -> 'a1) -> elem_dec -> 'a1

  val dec_term : PR.term -> PR.ckind -> elem_dec

  val dec_context :
    PR.ckind -> PR.ckind -> PR.elem_context_kinded -> PR.value -> elem_dec

  type elem_context_in =
  | Coq_ec_in of PR.ckind * PR.elem_context_kinded

  val elem_context_in_rect :
    PR.ckind -> (PR.ckind -> PR.elem_context_kinded -> 'a1) -> elem_context_in -> 'a1

  val elem_context_in_rec :
    PR.ckind -> (PR.ckind -> PR.elem_context_kinded -> 'a1) -> elem_context_in -> 'a1

  val ec_kinded_to_in :
    PR.ckind -> PR.ckind -> PR.elem_context_kinded -> elem_context_in
 end) ->
 struct
  module RLF = RED_LANG_Facts(PR)

  module ST = ST

  module R =
   struct
    type term = PR.term

    type ckind = PR.ckind

    type elem_context_kinded = PR.elem_context_kinded

    (** val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term **)

    let elem_plug =
      PR.elem_plug

    type redex = PR.redex

    type value = PR.value

    (** val init_ckind : ckind **)

    let init_ckind =
      PR.init_ckind

    (** val value_to_term : ckind -> value -> term **)

    let value_to_term =
      PR.value_to_term

    (** val redex_to_term : ckind -> redex -> term **)

    let redex_to_term =
      PR.redex_to_term

    type context = PR.context =
    | Coq_empty
    | Coq_ccons of ckind * ckind * elem_context_kinded * context

    (** val context_rect :
        ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
        'a1) -> ckind -> context -> 'a1 **)

    let rec context_rect k1 f f0 _ = function
    | Coq_empty -> f
    | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rect k1 f f0 k2 c0)

    (** val context_rec :
        ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
        'a1) -> ckind -> context -> 'a1 **)

    let rec context_rec k1 f f0 _ = function
    | Coq_empty -> f
    | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rec k1 f f0 k2 c0)

    (** val compose : ckind -> ckind -> context -> ckind -> context -> context **)

    let rec compose k1 _ c0 k3 c1 =
      match c0 with
      | Coq_empty -> c1
      | Coq_ccons (k2, k4, ec, c0') ->
        Coq_ccons (k2, k4, ec, (compose k1 k2 c0' k3 c1))

    (** val plug : term -> ckind -> ckind -> context -> term **)

    let rec plug t k1 _ = function
    | Coq_empty -> t
    | Coq_ccons (k2, k3, ec, c') -> plug (elem_plug k2 k3 t ec) k1 k2 c'

    type decomp = PR.decomp =
    | Coq_d_red of ckind * redex * context
    | Coq_d_val of value

    (** val decomp_rect :
        ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp ->
        'a1 **)

    let decomp_rect _ f f0 = function
    | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
    | Coq_d_val x0 -> f0 x0

    (** val decomp_rec :
        ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp ->
        'a1 **)

    let decomp_rec _ f f0 = function
    | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
    | Coq_d_val x0 -> f0 x0

    (** val decomp_to_term : ckind -> decomp -> term **)

    let decomp_to_term k = function
    | Coq_d_red (k', r, c) -> plug (redex_to_term k' r) k k' c
    | Coq_d_val v -> value_to_term k v

    (** val contract : ckind -> redex -> term option **)

    let contract =
      PR.contract

    (** val lrws : (ckind, term) lABELED_REWRITING_SYSTEM **)

    let lrws =
      Build_LABELED_REWRITING_SYSTEM

    (** val rws : term rEWRITING_SYSTEM **)

    let rws =
      Build_REWRITING_SYSTEM
   end

  type term = PR.term

  type ckind = PR.ckind

  type elem_context_kinded = PR.elem_context_kinded

  (** val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term **)

  let elem_plug =
    PR.elem_plug

  type redex = PR.redex

  type value = PR.value

  (** val init_ckind : ckind **)

  let init_ckind =
    PR.init_ckind

  (** val value_to_term : ckind -> value -> term **)

  let value_to_term =
    PR.value_to_term

  (** val redex_to_term : ckind -> redex -> term **)

  let redex_to_term =
    PR.redex_to_term

  type context = PR.context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  (** val context_rect :
      ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
      'a1) -> ckind -> context -> 'a1 **)

  let rec context_rect k1 f f0 _ = function
  | Coq_empty -> f
  | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rect k1 f f0 k2 c0)

  (** val context_rec :
      ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
      'a1) -> ckind -> context -> 'a1 **)

  let rec context_rec k1 f f0 _ = function
  | Coq_empty -> f
  | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rec k1 f f0 k2 c0)

  (** val compose : ckind -> ckind -> context -> ckind -> context -> context **)

  let rec compose k1 _ c0 k3 c1 =
    match c0 with
    | Coq_empty -> c1
    | Coq_ccons (k2, k4, ec, c0') ->
      Coq_ccons (k2, k4, ec, (compose k1 k2 c0' k3 c1))

  (** val plug : term -> ckind -> ckind -> context -> term **)

  let rec plug t k1 _ = function
  | Coq_empty -> t
  | Coq_ccons (k2, k3, ec, c') -> plug (elem_plug k2 k3 t ec) k1 k2 c'

  type decomp = PR.decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  (** val decomp_rect :
      ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1 **)

  let decomp_rect _ f f0 = function
  | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
  | Coq_d_val x0 -> f0 x0

  (** val decomp_rec :
      ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1 **)

  let decomp_rec _ f f0 = function
  | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
  | Coq_d_val x0 -> f0 x0

  (** val decomp_to_term : ckind -> decomp -> term **)

  let decomp_to_term k = function
  | Coq_d_red (k', r, c) -> plug (redex_to_term k' r) k k' c
  | Coq_d_val v -> value_to_term k v

  (** val contract : ckind -> redex -> term option **)

  let contract =
    PR.contract

  (** val lrws : (ckind, term) lABELED_REWRITING_SYSTEM **)

  let lrws =
    Build_LABELED_REWRITING_SYSTEM

  (** val rws : term rEWRITING_SYSTEM **)

  let rws =
    Build_REWRITING_SYSTEM

  module DPT = RedDecProcEqvDec(R)
 end

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a::[]
| a1::x1 -> if aeq_dec a a1 then a1::x1 else a1::(set_add aeq_dec a x1)

(** val set_remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_remove aeq_dec a = function
| [] -> empty_set
| a1::x1 -> if aeq_dec a a1 then x1 else a1::(set_remove aeq_dec a x1)

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x0 = function
| [] -> x0
| a1::y1 -> set_add aeq_dec a1 (set_union aeq_dec x0 y1)

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

(** val in_split_aux :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> (('a1 set*'a1 set), __) sum **)

let rec in_split_aux eq_A x0 = function
| [] -> Inr __
| y::l0 ->
  let s = in_split_aux eq_A x0 l0 in
  (match s with
   | Inl s0 -> let x1,x2 = s0 in Inl ((y::x1),x2)
   | Inr _ ->
     if eq_A y x0
     then internal_eq_rew_r_dep y x0 (fun _ _ _ -> Inl ([],l0)) __ __ __
     else Inr __)

(** val in_split :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> ('a1 set, ('a1 set, __) sigT) sigT
    sumor **)

let in_split eq_A x0 l =
  let hh = in_split_aux eq_A x0 l in
  (match hh with
   | Inl s -> let s0,s1 = s in Inleft (ExistT (s0, (ExistT (s1, __))))
   | Inr _ -> Inright)

type entropy (* AXIOM TO BE REALIZED *)

module type DET_ABSTRACT_MACHINE =
 sig
  type term

  type configuration

  type value

  val load : term -> configuration

  val final : configuration -> value option

  val next_conf : entropy -> configuration -> configuration option

  val rws : configuration rEWRITING_SYSTEM

  val dnext_conf : configuration -> configuration option
 end

module RefEvalApplyMachine =
 functor (R:RED_REF_SEM) ->
 struct
  module RF = RED_LANG_Facts(R)

  type term = R.term

  type value = R.value

  (** val value_to_term : value -> term **)

  let value_to_term v =
    R.value_to_term R.init_ckind v

  type conf =
  | Coq_c_eval of term * R.ckind * R.context
  | Coq_c_apply of R.ckind * R.context * R.value

  (** val conf_rect :
      (term -> R.ckind -> R.context -> 'a1) -> (R.ckind -> R.context -> R.value ->
      'a1) -> conf -> 'a1 **)

  let conf_rect f f0 = function
  | Coq_c_eval (x0, x1, x2) -> f x0 x1 x2
  | Coq_c_apply (x0, x1, x2) -> f0 x0 x1 x2

  (** val conf_rec :
      (term -> R.ckind -> R.context -> 'a1) -> (R.ckind -> R.context -> R.value ->
      'a1) -> conf -> 'a1 **)

  let conf_rec f f0 = function
  | Coq_c_eval (x0, x1, x2) -> f x0 x1 x2
  | Coq_c_apply (x0, x1, x2) -> f0 x0 x1 x2

  type configuration = conf

  (** val load : term -> configuration **)

  let load t =
    Coq_c_eval (t, R.init_ckind, R.Coq_empty)

  (** val value_to_conf : value -> configuration **)

  let value_to_conf v =
    Coq_c_apply (R.init_ckind, R.Coq_empty, v)

  (** val final : configuration -> value option **)

  let final = function
  | Coq_c_eval (_, _, _) -> None
  | Coq_c_apply (_, c0, v) ->
    (match c0 with
     | R.Coq_empty -> Some v
     | R.Coq_ccons (_, _, _, _) -> None)

  (** val decompile : configuration -> term **)

  let decompile = function
  | Coq_c_eval (t, k, c0) -> R.plug t R.init_ckind k c0
  | Coq_c_apply (k, c0, v) -> R.plug (R.value_to_term k v) R.init_ckind k c0

  (** val dnext_conf : configuration -> configuration option **)

  let dnext_conf = function
  | Coq_c_eval (t, k, c) ->
    (match R.ST.dec_term t k with
     | R.ST.Coq_ed_red r ->
       option_map (fun t' -> Coq_c_eval (t', k, c)) (R.contract k r)
     | R.ST.Coq_ed_dec (k', t0, ec) ->
       Some (Coq_c_eval (t0, k', (R.Coq_ccons (k, k', ec, c))))
     | R.ST.Coq_ed_val v -> Some (Coq_c_apply (k, c, v)))
  | Coq_c_apply (_, c0, v) ->
    (match c0 with
     | R.Coq_empty -> None
     | R.Coq_ccons (k2, k3, ec, c) ->
       (match R.ST.dec_context k2 k3 ec v with
        | R.ST.Coq_ed_red r ->
          option_map (fun t' -> Coq_c_eval (t', k2, c)) (R.contract k2 r)
        | R.ST.Coq_ed_dec (k', t, ec0) ->
          Some (Coq_c_eval (t, k', (R.Coq_ccons (k2, k', ec0, c))))
        | R.ST.Coq_ed_val v0 -> Some (Coq_c_apply (k2, c, v0))))

  (** val next_conf : entropy -> configuration -> configuration option **)

  let next_conf _ =
    dnext_conf

  (** val rws : configuration rEWRITING_SYSTEM **)

  let rws =
    Build_REWRITING_SYSTEM
 end

module DET_ABSTRACT_MACHINE_Facts =
 functor (AM:DET_ABSTRACT_MACHINE) ->
 struct
 end

module DetAbstractMachine_Sim =
 functor (AM:DET_ABSTRACT_MACHINE) ->
 struct
  module AMF = DET_ABSTRACT_MACHINE_Facts(AM)

  (** val n_steps : AM.configuration -> int -> AM.configuration option **)

  let rec n_steps c n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some c)
      (fun n0 -> match AM.dnext_conf c with
                 | Some c' -> n_steps c' n0
                 | None -> None)
      n
 end

module Lam_cbnd_PreRefSem =
 struct
  type id = int
    (* singleton inductive, whose constructor was Id *)

  (** val id_rect : (int -> 'a1) -> id -> 'a1 **)

  let id_rect f =
    f

  (** val id_rec : (int -> 'a1) -> id -> 'a1 **)

  let id_rec f =
    f

  type var = id

  (** val eq_var : var -> var -> bool **)

  let rec eq_var n y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        y)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> eq_var n0 m')
        y)
      n

  type vars = var set

  type ck =
  | E
  | C

  (** val ck_rect : 'a1 -> 'a1 -> ck -> 'a1 **)

  let ck_rect f f0 = function
  | E -> f
  | C -> f0

  (** val ck_rec : 'a1 -> 'a1 -> ck -> 'a1 **)

  let ck_rec f f0 = function
  | E -> f
  | C -> f0

  type ckvars =
  | Coq_ckv of ck * vars

  (** val ckvars_rect : (ck -> vars -> __ -> 'a1) -> ckvars -> 'a1 **)

  let ckvars_rect f = function
  | Coq_ckv (x0, x1) -> f x0 x1 __

  (** val ckvars_rec : (ck -> vars -> __ -> 'a1) -> ckvars -> 'a1 **)

  let ckvars_rec f = function
  | Coq_ckv (x0, x1) -> f x0 x1 __

  type ckind = ckvars

  (** val fresh_for : vars -> var **)

  let fresh_for xs =
    add (succ 0) (fold_right add 0 (map (fun y -> y) xs))

  type expr =
  | App of expr * expr
  | Var of var
  | Lam of var * expr
  | Let of var * expr * expr
  | LetNd of var * expr * expr

  (** val expr_rect :
      (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (var -> 'a1) -> (var -> expr -> 'a1 ->
      'a1) -> (var -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (var -> expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> expr -> 'a1 **)

  let rec expr_rect f f0 f1 f2 f3 = function
  | App (e0, e1) -> f e0 (expr_rect f f0 f1 f2 f3 e0) e1 (expr_rect f f0 f1 f2 f3 e1)
  | Var v -> f0 v
  | Lam (v, e0) -> f1 v e0 (expr_rect f f0 f1 f2 f3 e0)
  | Let (v, e0, e1) ->
    f2 v e0 (expr_rect f f0 f1 f2 f3 e0) e1 (expr_rect f f0 f1 f2 f3 e1)
  | LetNd (v, e0, e1) ->
    f3 v e0 (expr_rect f f0 f1 f2 f3 e0) e1 (expr_rect f f0 f1 f2 f3 e1)

  (** val expr_rec :
      (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (var -> 'a1) -> (var -> expr -> 'a1 ->
      'a1) -> (var -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (var -> expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> expr -> 'a1 **)

  let rec expr_rec f f0 f1 f2 f3 = function
  | App (e0, e1) -> f e0 (expr_rec f f0 f1 f2 f3 e0) e1 (expr_rec f f0 f1 f2 f3 e1)
  | Var v -> f0 v
  | Lam (v, e0) -> f1 v e0 (expr_rec f f0 f1 f2 f3 e0)
  | Let (v, e0, e1) ->
    f2 v e0 (expr_rec f f0 f1 f2 f3 e0) e1 (expr_rec f f0 f1 f2 f3 e1)
  | LetNd (v, e0, e1) ->
    f3 v e0 (expr_rec f f0 f1 f2 f3 e0) e1 (expr_rec f f0 f1 f2 f3 e1)

  type term = expr

  type in_ctx =
  | Coq_inctxVar of ck * var
  | Coq_inctxApp_l of ck * var * var list * in_ctx * expr
  | Coq_inctxApp_r of ck * var * var list * var list * coq_struct * in_ctx
  | Coq_inctxLam of var * var * vars * in_ctx
  | Coq_inctxSub of ck * var * var * var list * in_ctx * expr
  | Coq_inctxNdSub of ck * var * var * var list * vars * coq_struct * in_ctx
  | Coq_inctxNdSub2 of ck * var * vars * var * in_ctx * expr
  and coq_struct =
  | Coq_sVar of var
  | Coq_sApp of vars * vars * coq_struct * normal
  | Coq_sSub of var * var list * expr * coq_struct
  | Coq_sNdSub of var * var set * vars * var set * coq_struct * coq_struct
  and lambda_normal =
  | Coq_lnfLam of var * vars * normal
  | Coq_lnfSub of var * var list * expr * lambda_normal
  | Coq_lnfNdSub of var * var set * vars * var set * coq_struct * lambda_normal
  and normal =
  | Coq_nf_struct of vars * coq_struct
  | Coq_nf_lam_in_ctx of vars * lambda_normal

  (** val in_ctx_rect :
      (ck -> var -> 'a1) -> (ck -> var -> var list -> __ -> in_ctx -> 'a1 -> expr ->
      'a1) -> (ck -> var -> var list -> var list -> __ -> coq_struct -> in_ctx ->
      'a1 -> 'a1) -> (var -> var -> vars -> __ -> in_ctx -> 'a1 -> 'a1) -> (ck ->
      var -> var -> var list -> __ -> __ -> in_ctx -> 'a1 -> expr -> 'a1) -> (ck ->
      var -> var -> var list -> vars -> __ -> __ -> coq_struct -> in_ctx -> 'a1 ->
      'a1) -> (ck -> var -> vars -> var -> in_ctx -> 'a1 -> expr -> 'a1) -> ck ->
      var -> vars -> in_ctx -> 'a1 **)

  let rec in_ctx_rect f f0 f1 f2 f3 f4 f5 _ _ _ = function
  | Coq_inctxVar (k, x0) -> f k x0
  | Coq_inctxApp_l (k, x0, xs, i0, e) ->
    f0 k x0 xs __ i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 E x0 xs i0) e
  | Coq_inctxApp_r (k, x0, xs, ys, s, i0) ->
    f1 k x0 xs ys __ s i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 C x0 xs i0)
  | Coq_inctxLam (x0, y, xs, i0) ->
    f2 x0 y xs __ i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 C y xs i0)
  | Coq_inctxSub (k, x0, y, xs, i0, e) ->
    f3 k x0 y xs __ __ i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 k y xs i0) e
  | Coq_inctxNdSub (k, x0, y, xs, zs, s, i0) ->
    f4 k x0 y xs zs __ __ s i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 k y zs i0)
  | Coq_inctxNdSub2 (k, y, xs, v, i0, e) ->
    f5 k y xs v i0 (in_ctx_rect f f0 f1 f2 f3 f4 f5 E y xs i0) e

  (** val in_ctx_rec :
      (ck -> var -> 'a1) -> (ck -> var -> var list -> __ -> in_ctx -> 'a1 -> expr ->
      'a1) -> (ck -> var -> var list -> var list -> __ -> coq_struct -> in_ctx ->
      'a1 -> 'a1) -> (var -> var -> vars -> __ -> in_ctx -> 'a1 -> 'a1) -> (ck ->
      var -> var -> var list -> __ -> __ -> in_ctx -> 'a1 -> expr -> 'a1) -> (ck ->
      var -> var -> var list -> vars -> __ -> __ -> coq_struct -> in_ctx -> 'a1 ->
      'a1) -> (ck -> var -> vars -> var -> in_ctx -> 'a1 -> expr -> 'a1) -> ck ->
      var -> vars -> in_ctx -> 'a1 **)

  let rec in_ctx_rec f f0 f1 f2 f3 f4 f5 _ _ _ = function
  | Coq_inctxVar (k, x0) -> f k x0
  | Coq_inctxApp_l (k, x0, xs, i0, e) ->
    f0 k x0 xs __ i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 E x0 xs i0) e
  | Coq_inctxApp_r (k, x0, xs, ys, s, i0) ->
    f1 k x0 xs ys __ s i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 C x0 xs i0)
  | Coq_inctxLam (x0, y, xs, i0) ->
    f2 x0 y xs __ i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 C y xs i0)
  | Coq_inctxSub (k, x0, y, xs, i0, e) ->
    f3 k x0 y xs __ __ i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 k y xs i0) e
  | Coq_inctxNdSub (k, x0, y, xs, zs, s, i0) ->
    f4 k x0 y xs zs __ __ s i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 k y zs i0)
  | Coq_inctxNdSub2 (k, y, xs, v, i0, e) ->
    f5 k y xs v i0 (in_ctx_rec f f0 f1 f2 f3 f4 f5 E y xs i0) e

  (** val struct_rect :
      (var -> 'a1) -> (vars -> vars -> coq_struct -> 'a1 -> normal -> 'a1) -> (var
      -> var list -> __ -> expr -> coq_struct -> 'a1 -> 'a1) -> (var -> var set ->
      vars -> var set -> __ -> __ -> __ -> coq_struct -> 'a1 -> coq_struct -> 'a1 ->
      'a1) -> vars -> coq_struct -> 'a1 **)

  let rec struct_rect f f0 f1 f2 _ = function
  | Coq_sVar x0 -> f x0
  | Coq_sApp (xs, ys, s0, n) -> f0 xs ys s0 (struct_rect f f0 f1 f2 xs s0) n
  | Coq_sSub (x0, ys, e, s0) -> f1 x0 ys __ e s0 (struct_rect f f0 f1 f2 ys s0)
  | Coq_sNdSub (x0, ys, zs, xs, s0, s1) ->
    f2 x0 ys zs xs __ __ __ s0 (struct_rect f f0 f1 f2 zs s0) s1
      (struct_rect f f0 f1 f2 xs s1)

  (** val struct_rec :
      (var -> 'a1) -> (vars -> vars -> coq_struct -> 'a1 -> normal -> 'a1) -> (var
      -> var list -> __ -> expr -> coq_struct -> 'a1 -> 'a1) -> (var -> var set ->
      vars -> var set -> __ -> __ -> __ -> coq_struct -> 'a1 -> coq_struct -> 'a1 ->
      'a1) -> vars -> coq_struct -> 'a1 **)

  let rec struct_rec f f0 f1 f2 _ = function
  | Coq_sVar x0 -> f x0
  | Coq_sApp (xs, ys, s0, n) -> f0 xs ys s0 (struct_rec f f0 f1 f2 xs s0) n
  | Coq_sSub (x0, ys, e, s0) -> f1 x0 ys __ e s0 (struct_rec f f0 f1 f2 ys s0)
  | Coq_sNdSub (x0, ys, zs, xs, s0, s1) ->
    f2 x0 ys zs xs __ __ __ s0 (struct_rec f f0 f1 f2 zs s0) s1
      (struct_rec f f0 f1 f2 xs s1)

  (** val lambda_normal_rect :
      (var -> vars -> normal -> 'a1) -> (var -> var list -> __ -> expr ->
      lambda_normal -> 'a1 -> 'a1) -> (var -> var set -> vars -> var set -> __ -> __
      -> __ -> coq_struct -> lambda_normal -> 'a1 -> 'a1) -> vars -> lambda_normal
      -> 'a1 **)

  let rec lambda_normal_rect f f0 f1 _ = function
  | Coq_lnfLam (x0, xs, n) -> f x0 xs n
  | Coq_lnfSub (x0, ys, e, l0) -> f0 x0 ys __ e l0 (lambda_normal_rect f f0 f1 ys l0)
  | Coq_lnfNdSub (x0, ys, zs, xs, s, l0) ->
    f1 x0 ys zs xs __ __ __ s l0 (lambda_normal_rect f f0 f1 xs l0)

  (** val lambda_normal_rec :
      (var -> vars -> normal -> 'a1) -> (var -> var list -> __ -> expr ->
      lambda_normal -> 'a1 -> 'a1) -> (var -> var set -> vars -> var set -> __ -> __
      -> __ -> coq_struct -> lambda_normal -> 'a1 -> 'a1) -> vars -> lambda_normal
      -> 'a1 **)

  let rec lambda_normal_rec f f0 f1 _ = function
  | Coq_lnfLam (x0, xs, n) -> f x0 xs n
  | Coq_lnfSub (x0, ys, e, l0) -> f0 x0 ys __ e l0 (lambda_normal_rec f f0 f1 ys l0)
  | Coq_lnfNdSub (x0, ys, zs, xs, s, l0) ->
    f1 x0 ys zs xs __ __ __ s l0 (lambda_normal_rec f f0 f1 xs l0)

  (** val normal_rect :
      (vars -> coq_struct -> 'a1) -> (vars -> lambda_normal -> 'a1) -> vars ->
      normal -> 'a1 **)

  let normal_rect f f0 _ = function
  | Coq_nf_struct (x0, x1) -> f x0 x1
  | Coq_nf_lam_in_ctx (x0, x1) -> f0 x0 x1

  (** val normal_rec :
      (vars -> coq_struct -> 'a1) -> (vars -> lambda_normal -> 'a1) -> vars ->
      normal -> 'a1 **)

  let normal_rec f f0 _ = function
  | Coq_nf_struct (x0, x1) -> f x0 x1
  | Coq_nf_lam_in_ctx (x0, x1) -> f0 x0 x1

  type sub =
  | Coq_subMt
  | Coq_subCons of var * expr * sub

  (** val sub_rect : 'a1 -> (var -> expr -> sub -> 'a1 -> 'a1) -> sub -> 'a1 **)

  let rec sub_rect f f0 = function
  | Coq_subMt -> f
  | Coq_subCons (v, e, s0) -> f0 v e s0 (sub_rect f f0 s0)

  (** val sub_rec : 'a1 -> (var -> expr -> sub -> 'a1 -> 'a1) -> sub -> 'a1 **)

  let rec sub_rec f f0 = function
  | Coq_subMt -> f
  | Coq_subCons (v, e, s0) -> f0 v e s0 (sub_rec f f0 s0)

  type sub_ext =
  | Coq_subSimple of sub
  | Coq_subNd of var * expr * sub_ext

  (** val sub_ext_rect :
      (sub -> 'a1) -> (var -> expr -> sub_ext -> 'a1 -> 'a1) -> sub_ext -> 'a1 **)

  let rec sub_ext_rect f f0 = function
  | Coq_subSimple s0 -> f s0
  | Coq_subNd (v, e, s0) -> f0 v e s0 (sub_ext_rect f f0 s0)

  (** val sub_ext_rec :
      (sub -> 'a1) -> (var -> expr -> sub_ext -> 'a1 -> 'a1) -> sub_ext -> 'a1 **)

  let rec sub_ext_rec f f0 = function
  | Coq_subSimple s0 -> f s0
  | Coq_subNd (v, e, s0) -> f0 v e s0 (sub_ext_rec f f0 s0)

  (** val sub_to_term : sub -> term -> term **)

  let rec sub_to_term s t =
    match s with
    | Coq_subMt -> t
    | Coq_subCons (x0, r, s') -> Let (x0, r, (sub_to_term s' t))

  (** val sub_ext_to_term : sub_ext -> term -> term **)

  let rec sub_ext_to_term s t =
    match s with
    | Coq_subSimple s0 -> sub_to_term s0 t
    | Coq_subNd (x0, r, s') -> LetNd (x0, r, (sub_ext_to_term s' t))

  (** val struct_to_term : vars -> coq_struct -> term **)

  let rec struct_to_term _ = function
  | Coq_sVar x0 -> Var x0
  | Coq_sApp (xs, ys, s0, n) -> App ((struct_to_term xs s0), (normal_to_term ys n))
  | Coq_sSub (x0, ys, e, s0) -> Let (x0, e, (struct_to_term ys s0))
  | Coq_sNdSub (x0, _, zs, xs, s0, sx) ->
    LetNd (x0, (struct_to_term zs s0), (struct_to_term xs sx))

  (** val lambda_normal_to_term : vars -> lambda_normal -> term **)

  and lambda_normal_to_term _ = function
  | Coq_lnfLam (x0, xs, n0) -> Lam (x0, (normal_to_term xs n0))
  | Coq_lnfSub (x0, ys, e, n0) -> Let (x0, e, (lambda_normal_to_term ys n0))
  | Coq_lnfNdSub (x0, _, zs, xs, s, n0) ->
    LetNd (x0, (struct_to_term zs s), (lambda_normal_to_term xs n0))

  (** val normal_to_term : vars -> normal -> term **)

  and normal_to_term _ = function
  | Coq_nf_struct (xs, s) -> struct_to_term xs s
  | Coq_nf_lam_in_ctx (xs, ln) -> lambda_normal_to_term xs ln

  (** val nf_to_term : ck -> var -> vars -> in_ctx -> term **)

  let rec nf_to_term _ _ _ = function
  | Coq_inctxVar (_, x0) -> Var x0
  | Coq_inctxApp_l (_, x0, xs, n, e) -> App ((nf_to_term E x0 xs n), e)
  | Coq_inctxApp_r (_, x0, xs, ys, s, neu') ->
    App ((struct_to_term ys s), (nf_to_term C x0 xs neu'))
  | Coq_inctxLam (x0, y, xs, neu') -> Lam (x0, (nf_to_term C y xs neu'))
  | Coq_inctxSub (k, x0, y, xs, n, e) -> Let (x0, e, (nf_to_term k y xs n))
  | Coq_inctxNdSub (k, x0, y, xs, zs, s, n) ->
    LetNd (x0, (struct_to_term xs s), (nf_to_term k y zs n))
  | Coq_inctxNdSub2 (_, y, xs, x0, ny, nx) -> LetNd (x0, (nf_to_term E y xs ny), nx)

  (** val struct_to_normal : vars -> coq_struct -> normal **)

  let struct_to_normal xs s =
    Coq_nf_struct (xs, s)

  type coq_val =
  | Coq_vCLam of var set * var list * lambda_normal
  | Coq_vStruct of ck * var set * var list * coq_struct
  | Coq_vNeu of ck * var set * var * var list * in_ctx
  | Coq_vELam of var list * var * term * sub

  (** val val_rect :
      (var set -> var list -> __ -> __ -> lambda_normal -> 'a1) -> (ck -> var set ->
      var list -> __ -> __ -> coq_struct -> 'a1) -> (ck -> var set -> var -> var
      list -> __ -> __ -> __ -> in_ctx -> 'a1) -> (var list -> __ -> var -> term ->
      sub -> 'a1) -> ckind -> coq_val -> 'a1 **)

  let val_rect f f0 f1 f2 _ = function
  | Coq_vCLam (x0, x1, x2) -> f x0 x1 __ __ x2
  | Coq_vStruct (x0, x1, x2, x3) -> f0 x0 x1 x2 __ __ x3
  | Coq_vNeu (x0, x1, x2, x3, x4) -> f1 x0 x1 x2 x3 __ __ __ x4
  | Coq_vELam (x0, x1, x2, x3) -> f2 x0 __ x1 x2 x3

  (** val val_rec :
      (var set -> var list -> __ -> __ -> lambda_normal -> 'a1) -> (ck -> var set ->
      var list -> __ -> __ -> coq_struct -> 'a1) -> (ck -> var set -> var -> var
      list -> __ -> __ -> __ -> in_ctx -> 'a1) -> (var list -> __ -> var -> term ->
      sub -> 'a1) -> ckind -> coq_val -> 'a1 **)

  let val_rec f f0 f1 f2 _ = function
  | Coq_vCLam (x0, x1, x2) -> f x0 x1 __ __ x2
  | Coq_vStruct (x0, x1, x2, x3) -> f0 x0 x1 x2 __ __ x3
  | Coq_vNeu (x0, x1, x2, x3, x4) -> f1 x0 x1 x2 x3 __ __ __ x4
  | Coq_vELam (x0, x1, x2, x3) -> f2 x0 __ x1 x2 x3

  type value = coq_val

  (** val val_to_term : ckind -> coq_val -> term **)

  let rec val_to_term _ = function
  | Coq_vCLam (xs, _, n) -> lambda_normal_to_term xs n
  | Coq_vStruct (_, xs, _, s) -> struct_to_term xs s
  | Coq_vNeu (k, xs, x0, _, n) -> nf_to_term k x0 xs n
  | Coq_vELam (_, x0, t, s) -> sub_to_term s (Lam (x0, t))

  (** val value_to_term : ckind -> coq_val -> term **)

  let value_to_term =
    val_to_term

  type red =
  | Coq_rApp of ck * var list * var * term * sub * term
  | Coq_rSub of ck * var * var list * term * var * term * sub
  | Coq_rSubNd of ck * var * var set * var list * in_ctx * term
  | Coq_rSubWrong of ck * var * var set * var list * var set * coq_struct
     * coq_struct
  | Coq_rSubWrong2 of var * var set * var list * var set * coq_struct * lambda_normal
  | Coq_rSubNdE of var * var set * var list * coq_struct * var * term * sub

  (** val red_rect :
      (ck -> var list -> __ -> var -> term -> sub -> term -> 'a1) -> (ck -> var ->
      var list -> __ -> term -> var -> term -> sub -> 'a1) -> (ck -> var -> var set
      -> var list -> __ -> __ -> in_ctx -> term -> 'a1) -> (ck -> var -> var set ->
      var list -> var set -> __ -> __ -> __ -> __ -> coq_struct -> coq_struct ->
      'a1) -> (var -> var set -> var list -> var set -> __ -> __ -> __ -> __ ->
      coq_struct -> lambda_normal -> 'a1) -> (var -> var set -> var list -> __ -> __
      -> coq_struct -> var -> term -> sub -> 'a1) -> ckind -> red -> 'a1 **)

  let red_rect f f0 f1 f2 f3 f4 _ = function
  | Coq_rApp (x0, x1, x2, x3, x4, x5) -> f x0 x1 __ x2 x3 x4 x5
  | Coq_rSub (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 __ x3 x4 x5 x6
  | Coq_rSubNd (x0, x1, x2, x3, x4, x5) -> f1 x0 x1 x2 x3 __ __ x4 x5
  | Coq_rSubWrong (x0, x1, x2, x3, x4, x5, x6) -> f2 x0 x1 x2 x3 x4 __ __ __ __ x5 x6
  | Coq_rSubWrong2 (x0, x1, x2, x3, x4, x5) -> f3 x0 x1 x2 x3 __ __ __ __ x4 x5
  | Coq_rSubNdE (x0, x1, x2, x3, x4, x5, x6) -> f4 x0 x1 x2 __ __ x3 x4 x5 x6

  (** val red_rec :
      (ck -> var list -> __ -> var -> term -> sub -> term -> 'a1) -> (ck -> var ->
      var list -> __ -> term -> var -> term -> sub -> 'a1) -> (ck -> var -> var set
      -> var list -> __ -> __ -> in_ctx -> term -> 'a1) -> (ck -> var -> var set ->
      var list -> var set -> __ -> __ -> __ -> __ -> coq_struct -> coq_struct ->
      'a1) -> (var -> var set -> var list -> var set -> __ -> __ -> __ -> __ ->
      coq_struct -> lambda_normal -> 'a1) -> (var -> var set -> var list -> __ -> __
      -> coq_struct -> var -> term -> sub -> 'a1) -> ckind -> red -> 'a1 **)

  let red_rec f f0 f1 f2 f3 f4 _ = function
  | Coq_rApp (x0, x1, x2, x3, x4, x5) -> f x0 x1 __ x2 x3 x4 x5
  | Coq_rSub (x0, x1, x2, x3, x4, x5, x6) -> f0 x0 x1 x2 __ x3 x4 x5 x6
  | Coq_rSubNd (x0, x1, x2, x3, x4, x5) -> f1 x0 x1 x2 x3 __ __ x4 x5
  | Coq_rSubWrong (x0, x1, x2, x3, x4, x5, x6) -> f2 x0 x1 x2 x3 x4 __ __ __ __ x5 x6
  | Coq_rSubWrong2 (x0, x1, x2, x3, x4, x5) -> f3 x0 x1 x2 x3 __ __ __ __ x4 x5
  | Coq_rSubNdE (x0, x1, x2, x3, x4, x5, x6) -> f4 x0 x1 x2 __ __ x3 x4 x5 x6

  type redex = red

  (** val redex_to_term : ckind -> redex -> term **)

  let redex_to_term _ = function
  | Coq_rApp (_, _, x0, t, s, t') -> App ((sub_to_term s (Lam (x0, t))), t')
  | Coq_rSub (_, x0, _, n, y, t, s) -> LetNd (x0, (sub_to_term s (Lam (y, t))), n)
  | Coq_rSubNd (k, x0, xs, _, n, t) -> Let (x0, t, (nf_to_term k x0 xs n))
  | Coq_rSubWrong (_, x0, xs, _, zs, s, s1) ->
    LetNd (x0, (normal_to_term xs (struct_to_normal xs s)),
      (normal_to_term zs (struct_to_normal zs s1)))
  | Coq_rSubWrong2 (x0, xs, _, zs, s, s1) ->
    LetNd (x0, (normal_to_term xs (struct_to_normal xs s)),
      (lambda_normal_to_term zs s1))
  | Coq_rSubNdE (x0, xs, _, s, y, t, s0) ->
    LetNd (x0, (normal_to_term xs (struct_to_normal xs s)),
      (sub_to_term s0 (Lam (y, t))))

  (** val subst : var -> term -> term -> term **)

  let rec subst x0 s t = match t with
  | App (t1, t2) -> App ((subst x0 s t1), (subst x0 s t2))
  | Var x' -> if eq_var x0 x' then s else t
  | Lam (x', t1) -> Lam (x', (if eq_var x0 x' then t1 else subst x0 s t1))
  | Let (x', r, u) ->
    Let (x', (subst x0 s r), (if eq_var x0 x' then u else subst x0 s u))
  | LetNd (x1, r, n) ->
    LetNd (x1, (subst x0 s r), (if eq_var x0 x1 then n else subst x0 s n))

  type eck =
  | Coq_k_lam_c of var list * var
  | Coq_k_ap_r of var list * ck * term
  | Coq_k_ap_l_E of ck * var list * var set * coq_struct
  | Coq_in_let of ck * var list * var * term
  | Coq_let_var of ck * var list * var * expr
  | Coq_let_var2 of ck * var * var set * var list * coq_struct

  (** val eck_rect :
      (var list -> var -> __ -> __ -> 'a1) -> (var list -> ck -> __ -> term -> 'a1)
      -> (ck -> var list -> var set -> __ -> __ -> coq_struct -> 'a1) -> (ck -> var
      list -> var -> __ -> __ -> term -> 'a1) -> (ck -> var list -> var -> __ ->
      expr -> 'a1) -> (ck -> var -> var set -> var list -> __ -> __ -> __ ->
      coq_struct -> 'a1) -> ckind -> ckind -> eck -> 'a1 **)

  let eck_rect f f0 f1 f2 f3 f4 _ _ = function
  | Coq_k_lam_c (x0, x1) -> f x0 x1 __ __
  | Coq_k_ap_r (x0, x1, x2) -> f0 x0 x1 __ x2
  | Coq_k_ap_l_E (x0, x1, x2, x3) -> f1 x0 x1 x2 __ __ x3
  | Coq_in_let (x0, x1, x2, x3) -> f2 x0 x1 x2 __ __ x3
  | Coq_let_var (x0, x1, x2, x3) -> f3 x0 x1 x2 __ x3
  | Coq_let_var2 (x0, x1, x2, x3, x4) -> f4 x0 x1 x2 x3 __ __ __ x4

  (** val eck_rec :
      (var list -> var -> __ -> __ -> 'a1) -> (var list -> ck -> __ -> term -> 'a1)
      -> (ck -> var list -> var set -> __ -> __ -> coq_struct -> 'a1) -> (ck -> var
      list -> var -> __ -> __ -> term -> 'a1) -> (ck -> var list -> var -> __ ->
      expr -> 'a1) -> (ck -> var -> var set -> var list -> __ -> __ -> __ ->
      coq_struct -> 'a1) -> ckind -> ckind -> eck -> 'a1 **)

  let eck_rec f f0 f1 f2 f3 f4 _ _ = function
  | Coq_k_lam_c (x0, x1) -> f x0 x1 __ __
  | Coq_k_ap_r (x0, x1, x2) -> f0 x0 x1 __ x2
  | Coq_k_ap_l_E (x0, x1, x2, x3) -> f1 x0 x1 x2 __ __ x3
  | Coq_in_let (x0, x1, x2, x3) -> f2 x0 x1 x2 __ __ x3
  | Coq_let_var (x0, x1, x2, x3) -> f3 x0 x1 x2 __ x3
  | Coq_let_var2 (x0, x1, x2, x3, x4) -> f4 x0 x1 x2 x3 __ __ __ x4

  type elem_context_kinded = eck

  (** val init_ckind : ckind **)

  let init_ckind =
    Coq_ckv (C, [])

  (** val elem_plug : ckind -> ckind -> term -> elem_context_kinded -> term **)

  let elem_plug _ _ t = function
  | Coq_k_lam_c (_, x0) -> Lam (x0, t)
  | Coq_k_ap_r (_, _, tr) -> App (t, tr)
  | Coq_k_ap_l_E (_, _, ys, s) ->
    App ((normal_to_term ys (struct_to_normal ys s)), t)
  | Coq_in_let (_, _, x0, s) -> Let (x0, s, t)
  | Coq_let_var (_, _, x0, s) -> LetNd (x0, t, s)
  | Coq_let_var2 (_, x0, xs, _, s) ->
    LetNd (x0, (normal_to_term xs (struct_to_normal xs s)), t)

  type context =
  | Coq_empty
  | Coq_ccons of ckind * ckind * elem_context_kinded * context

  (** val context_rect :
      ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
      'a1) -> ckind -> context -> 'a1 **)

  let rec context_rect k1 f f0 _ = function
  | Coq_empty -> f
  | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rect k1 f f0 k2 c0)

  (** val context_rec :
      ckind -> 'a1 -> (ckind -> ckind -> elem_context_kinded -> context -> 'a1 ->
      'a1) -> ckind -> context -> 'a1 **)

  let rec context_rec k1 f f0 _ = function
  | Coq_empty -> f
  | Coq_ccons (k2, k3, ec, c0) -> f0 k2 k3 ec c0 (context_rec k1 f f0 k2 c0)

  (** val compose : ckind -> ckind -> context -> ckind -> context -> context **)

  let rec compose k1 _ c0 k3 c1 =
    match c0 with
    | Coq_empty -> c1
    | Coq_ccons (k2, k4, ec, c0') ->
      Coq_ccons (k2, k4, ec, (compose k1 k2 c0' k3 c1))

  (** val plug : term -> ckind -> ckind -> context -> term **)

  let rec plug t k1 _ = function
  | Coq_empty -> t
  | Coq_ccons (k2, k3, ec, c') -> plug (elem_plug k2 k3 t ec) k1 k2 c'

  (** val contract : ckind -> redex -> term option **)

  let contract _ = function
  | Coq_rApp (_, _, x0, r0, s, t) -> Some (sub_to_term s (Let (x0, t, r0)))
  | Coq_rSub (_, x0, _, n, y, t, s) -> Some (subst x0 (sub_to_term s (Lam (y, t))) n)
  | Coq_rSubNd (k, x0, xs, _, n, e) -> Some (LetNd (x0, e, (nf_to_term k x0 xs n)))
  | Coq_rSubNdE (x0, xs, _, s, y, t, s0) ->
    Some (Let (x0, (normal_to_term xs (struct_to_normal xs s)),
      (sub_to_term s0 (Lam (y, t)))))
  | _ -> None

  type decomp =
  | Coq_d_red of ckind * redex * context
  | Coq_d_val of value

  (** val decomp_rect :
      ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1 **)

  let decomp_rect _ f f0 = function
  | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
  | Coq_d_val x0 -> f0 x0

  (** val decomp_rec :
      ckind -> (ckind -> redex -> context -> 'a1) -> (value -> 'a1) -> decomp -> 'a1 **)

  let decomp_rec _ f f0 = function
  | Coq_d_red (x0, x1, x2) -> f x0 x1 x2
  | Coq_d_val x0 -> f0 x0

  (** val decomp_to_term : ckind -> decomp -> term **)

  let decomp_to_term k = function
  | Coq_d_red (k', r, c) -> plug (redex_to_term k' r) k k' c
  | Coq_d_val v -> value_to_term k v

  (** val lrws : (ckind, term) lABELED_REWRITING_SYSTEM **)

  let lrws =
    Build_LABELED_REWRITING_SYSTEM

  (** val rws : term rEWRITING_SYSTEM **)

  let rws =
    Build_REWRITING_SYSTEM
 end

module Lam_cbn_Strategy =
 struct
  type elem_dec =
  | Coq_ed_red of Lam_cbnd_PreRefSem.redex
  | Coq_ed_dec of Lam_cbnd_PreRefSem.ckind * Lam_cbnd_PreRefSem.term
     * Lam_cbnd_PreRefSem.elem_context_kinded
  | Coq_ed_val of Lam_cbnd_PreRefSem.value

  (** val elem_dec_rect :
      Lam_cbnd_PreRefSem.ckind -> (Lam_cbnd_PreRefSem.redex -> 'a1) ->
      (Lam_cbnd_PreRefSem.ckind -> Lam_cbnd_PreRefSem.term ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> 'a1) -> (Lam_cbnd_PreRefSem.value ->
      'a1) -> elem_dec -> 'a1 **)

  let elem_dec_rect _ f f0 f1 = function
  | Coq_ed_red x0 -> f x0
  | Coq_ed_dec (x0, x1, x2) -> f0 x0 x1 x2
  | Coq_ed_val x0 -> f1 x0

  (** val elem_dec_rec :
      Lam_cbnd_PreRefSem.ckind -> (Lam_cbnd_PreRefSem.redex -> 'a1) ->
      (Lam_cbnd_PreRefSem.ckind -> Lam_cbnd_PreRefSem.term ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> 'a1) -> (Lam_cbnd_PreRefSem.value ->
      'a1) -> elem_dec -> 'a1 **)

  let elem_dec_rec _ f f0 f1 = function
  | Coq_ed_red x0 -> f x0
  | Coq_ed_dec (x0, x1, x2) -> f0 x0 x1 x2
  | Coq_ed_val x0 -> f1 x0

  (** val dec_term :
      Lam_cbnd_PreRefSem.term -> Lam_cbnd_PreRefSem.ckind -> elem_dec **)

  let dec_term t = function
  | Lam_cbnd_PreRefSem.Coq_ckv (c, xs) ->
    (match c with
     | Lam_cbnd_PreRefSem.E ->
       (match t with
        | Lam_cbnd_PreRefSem.App (t1, t2) ->
          Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)), t1,
            (Lam_cbnd_PreRefSem.Coq_k_ap_r (xs, Lam_cbnd_PreRefSem.E, t2)))
        | Lam_cbnd_PreRefSem.Var x0 ->
          if in_dec Lam_cbnd_PreRefSem.eq_var x0 xs
          then Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.E,
                 (set_add Lam_cbnd_PreRefSem.eq_var x0 empty_set), xs,
                 (Lam_cbnd_PreRefSem.Coq_sVar x0)))
          else Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.E,
                 empty_set, x0, xs, (Lam_cbnd_PreRefSem.Coq_inctxVar
                 (Lam_cbnd_PreRefSem.E, x0))))
        | Lam_cbnd_PreRefSem.Lam (x0, t1) ->
          Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vELam (xs, x0, t1,
            Lam_cbnd_PreRefSem.Coq_subMt))
        | Lam_cbnd_PreRefSem.Let (x0, t1, t2) ->
          if in_dec Lam_cbnd_PreRefSem.eq_var x0 xs
          then let f = Lam_cbnd_PreRefSem.fresh_for xs in
               Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)),
               (Lam_cbnd_PreRefSem.subst x0 (Lam_cbnd_PreRefSem.Var f) t2),
               (Lam_cbnd_PreRefSem.Coq_in_let (Lam_cbnd_PreRefSem.E, xs, f, t1)))
          else Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)),
                 t2, (Lam_cbnd_PreRefSem.Coq_in_let (Lam_cbnd_PreRefSem.E, xs, x0,
                 t1)))
        | Lam_cbnd_PreRefSem.LetNd (x0, t0, n) ->
          Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)), t0,
            (Lam_cbnd_PreRefSem.Coq_let_var (Lam_cbnd_PreRefSem.E, xs, x0, n))))
     | Lam_cbnd_PreRefSem.C ->
       (match t with
        | Lam_cbnd_PreRefSem.App (t1, t2) ->
          Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)), t1,
            (Lam_cbnd_PreRefSem.Coq_k_ap_r (xs, Lam_cbnd_PreRefSem.C, t2)))
        | Lam_cbnd_PreRefSem.Var x0 ->
          if in_dec Lam_cbnd_PreRefSem.eq_var x0 xs
          then Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.C,
                 (set_add Lam_cbnd_PreRefSem.eq_var x0 empty_set), xs,
                 (Lam_cbnd_PreRefSem.Coq_sVar x0)))
          else Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.C,
                 empty_set, x0, xs, (Lam_cbnd_PreRefSem.Coq_inctxVar
                 (Lam_cbnd_PreRefSem.C, x0))))
        | Lam_cbnd_PreRefSem.Lam (x0, t1) ->
          if in_dec Lam_cbnd_PreRefSem.eq_var x0 xs
          then let f = Lam_cbnd_PreRefSem.fresh_for xs in
               Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C,
               (f::xs))),
               (Lam_cbnd_PreRefSem.subst x0 (Lam_cbnd_PreRefSem.Var f) t1),
               (Lam_cbnd_PreRefSem.Coq_k_lam_c (xs, f)))
          else Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C,
                 (x0::xs))), t1, (Lam_cbnd_PreRefSem.Coq_k_lam_c (xs, x0)))
        | Lam_cbnd_PreRefSem.Let (x0, t1, t2) ->
          if in_dec Lam_cbnd_PreRefSem.eq_var x0 xs
          then let f = Lam_cbnd_PreRefSem.fresh_for xs in
               Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C, xs)),
               (Lam_cbnd_PreRefSem.subst x0 (Lam_cbnd_PreRefSem.Var f) t2),
               (Lam_cbnd_PreRefSem.Coq_in_let (Lam_cbnd_PreRefSem.C, xs, f, t1)))
          else Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C, xs)),
                 t2, (Lam_cbnd_PreRefSem.Coq_in_let (Lam_cbnd_PreRefSem.C, xs, x0,
                 t1)))
        | Lam_cbnd_PreRefSem.LetNd (x0, t0, n) ->
          Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.E, xs)), t0,
            (Lam_cbnd_PreRefSem.Coq_let_var (Lam_cbnd_PreRefSem.C, xs, x0, n)))))

  (** val dec_context :
      Lam_cbnd_PreRefSem.ckind -> Lam_cbnd_PreRefSem.ckind ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> Lam_cbnd_PreRefSem.value -> elem_dec **)

  let dec_context _ _ ec v =
    match ec with
    | Lam_cbnd_PreRefSem.Coq_k_lam_c (xs, x0) ->
      (match v with
       | Lam_cbnd_PreRefSem.Coq_vCLam (xs0, _, l) ->
         Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vCLam
           ((set_remove Lam_cbnd_PreRefSem.eq_var x0 xs0), xs,
           (Lam_cbnd_PreRefSem.Coq_lnfLam (x0, xs0,
           (Lam_cbnd_PreRefSem.Coq_nf_lam_in_ctx (xs0, l))))))
       | Lam_cbnd_PreRefSem.Coq_vStruct (k0, xs0, _, s) ->
         (match k0 with
          | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.C ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vCLam
              ((set_remove Lam_cbnd_PreRefSem.eq_var x0 xs0), xs,
              (Lam_cbnd_PreRefSem.Coq_lnfLam (x0, xs0,
              (Lam_cbnd_PreRefSem.Coq_nf_struct (xs0, s)))))))
       | Lam_cbnd_PreRefSem.Coq_vNeu (k0, xs0, y, _, c) ->
         (match k0 with
          | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.C ->
            if Lam_cbnd_PreRefSem.eq_var x0 y
            then Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C,
                   (x0::xs))),
                   (Lam_cbnd_PreRefSem.nf_to_term Lam_cbnd_PreRefSem.C y xs0 c),
                   (Lam_cbnd_PreRefSem.Coq_k_lam_c (xs, x0)))
            else Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.C,
                   (set_remove Lam_cbnd_PreRefSem.eq_var x0 xs0), y, xs,
                   (Lam_cbnd_PreRefSem.Coq_inctxLam (x0, y, xs0, c)))))
       | Lam_cbnd_PreRefSem.Coq_vELam (_, _, _, _) -> assert false (* absurd case *))
    | Lam_cbnd_PreRefSem.Coq_k_ap_r (xs, k0, t) ->
      (match v with
       | Lam_cbnd_PreRefSem.Coq_vCLam (_, _, _) -> assert false (* absurd case *)
       | Lam_cbnd_PreRefSem.Coq_vStruct (k1, xs0, _, s) ->
         (match k1 with
          | Lam_cbnd_PreRefSem.E ->
            Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (Lam_cbnd_PreRefSem.C, xs)), t,
              (Lam_cbnd_PreRefSem.Coq_k_ap_l_E (k0, xs, xs0, s)))
          | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
       | Lam_cbnd_PreRefSem.Coq_vNeu (k1, xs0, x0, _, c) ->
         (match k1 with
          | Lam_cbnd_PreRefSem.E ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (k0, xs0, x0, xs,
              (Lam_cbnd_PreRefSem.Coq_inctxApp_l (k0, x0, xs0, c, t))))
          | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
       | Lam_cbnd_PreRefSem.Coq_vELam (_, x0, t0, s) ->
         Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rApp (k0, xs, x0, t0, s, t)))
    | Lam_cbnd_PreRefSem.Coq_k_ap_l_E (k0, xs, ys, s) ->
      (match v with
       | Lam_cbnd_PreRefSem.Coq_vCLam (xs0, _, l) ->
         Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (k0,
           (set_union Lam_cbnd_PreRefSem.eq_var ys xs0), xs,
           (Lam_cbnd_PreRefSem.Coq_sApp (ys, xs0, s,
           (Lam_cbnd_PreRefSem.Coq_nf_lam_in_ctx (xs0, l))))))
       | Lam_cbnd_PreRefSem.Coq_vStruct (k1, xs0, _, s1) ->
         (match k1 with
          | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.C ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (k0,
              (set_union Lam_cbnd_PreRefSem.eq_var ys xs0), xs,
              (Lam_cbnd_PreRefSem.Coq_sApp (ys, xs0, s,
              (Lam_cbnd_PreRefSem.struct_to_normal xs0 s1))))))
       | Lam_cbnd_PreRefSem.Coq_vNeu (k1, xs0, x0, _, c) ->
         (match k1 with
          | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.C ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (k0,
              (set_union Lam_cbnd_PreRefSem.eq_var ys xs0), x0, xs,
              (Lam_cbnd_PreRefSem.Coq_inctxApp_r (k0, x0, xs0, ys, s, c)))))
       | Lam_cbnd_PreRefSem.Coq_vELam (_, _, _, _) -> assert false (* absurd case *))
    | Lam_cbnd_PreRefSem.Coq_in_let (k0, xs, x0, t) ->
      (match k0 with
       | Lam_cbnd_PreRefSem.E ->
         (match v with
          | Lam_cbnd_PreRefSem.Coq_vCLam (_, _, _) -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.Coq_vStruct (k1, xs0, _, s) ->
            (match k1 with
             | Lam_cbnd_PreRefSem.E ->
               Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.E,
                 xs0, xs, (Lam_cbnd_PreRefSem.Coq_sSub (x0, xs0, t, s))))
             | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
          | Lam_cbnd_PreRefSem.Coq_vNeu (_, xs0, y, _, c) ->
            if Lam_cbnd_PreRefSem.eq_var x0 y
            then Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubNd (Lam_cbnd_PreRefSem.E, y,
                   xs0, xs, c, t))
            else Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.E, xs0,
                   y, xs, (Lam_cbnd_PreRefSem.Coq_inctxSub (Lam_cbnd_PreRefSem.E,
                   x0, y, xs0, c, t))))
          | Lam_cbnd_PreRefSem.Coq_vELam (_, y, r, s) ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vELam (xs, y, r,
              (Lam_cbnd_PreRefSem.Coq_subCons (x0, t, s)))))
       | Lam_cbnd_PreRefSem.C ->
         (match v with
          | Lam_cbnd_PreRefSem.Coq_vCLam (xs0, _, ln) ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vCLam (xs0, xs,
              (Lam_cbnd_PreRefSem.Coq_lnfSub (x0, xs0, t, ln))))
          | Lam_cbnd_PreRefSem.Coq_vStruct (k1, xs0, _, s) ->
            (match k1 with
             | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
             | Lam_cbnd_PreRefSem.C ->
               Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.C,
                 xs0, xs, (Lam_cbnd_PreRefSem.Coq_sSub (x0, xs0, t, s)))))
          | Lam_cbnd_PreRefSem.Coq_vNeu (_, xs0, y, _, c) ->
            if Lam_cbnd_PreRefSem.eq_var x0 y
            then Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubNd (Lam_cbnd_PreRefSem.C, y,
                   xs0, xs, c, t))
            else Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.C, xs0,
                   y, xs, (Lam_cbnd_PreRefSem.Coq_inctxSub (Lam_cbnd_PreRefSem.C,
                   x0, y, xs0, c, t))))
          | Lam_cbnd_PreRefSem.Coq_vELam (_, _, _, _) ->
            assert false (* absurd case *)))
    | Lam_cbnd_PreRefSem.Coq_let_var (k, xs, x0, t) ->
      (match v with
       | Lam_cbnd_PreRefSem.Coq_vCLam (_, _, _) -> assert false (* absurd case *)
       | Lam_cbnd_PreRefSem.Coq_vStruct (k0, xs0, _, s) ->
         (match k0 with
          | Lam_cbnd_PreRefSem.E ->
            (match in_split Lam_cbnd_PreRefSem.eq_var x0 xs with
             | Inleft s2 ->
               let ExistT (x1, s3) = s2 in
               let ExistT (x2, _) = s3 in
               let f = Lam_cbnd_PreRefSem.fresh_for (app x1 (x0::x2)) in
               Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (k, (f::(app x1 (x0::x2))))),
               (Lam_cbnd_PreRefSem.subst x0 (Lam_cbnd_PreRefSem.Var f) t),
               (Lam_cbnd_PreRefSem.Coq_let_var2 (k, f, xs0, (app x1 (x0::x2)), s)))
             | Inright ->
               Coq_ed_dec ((Lam_cbnd_PreRefSem.Coq_ckv (k, (x0::xs))), t,
                 (Lam_cbnd_PreRefSem.Coq_let_var2 (k, x0, xs0, xs, s))))
          | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
       | Lam_cbnd_PreRefSem.Coq_vNeu (k0, xs0, y, _, c) ->
         (match k0 with
          | Lam_cbnd_PreRefSem.E ->
            Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vNeu (k, xs0, y, xs,
              (Lam_cbnd_PreRefSem.Coq_inctxNdSub2 (k, y, xs0, x0, c, t))))
          | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
       | Lam_cbnd_PreRefSem.Coq_vELam (_, y, r, s) ->
         Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSub (k, x0, xs, t, y, r, s)))
    | Lam_cbnd_PreRefSem.Coq_let_var2 (k0, x0, xs, ys, s1) ->
      (match k0 with
       | Lam_cbnd_PreRefSem.E ->
         (match v with
          | Lam_cbnd_PreRefSem.Coq_vCLam (_, _, _) -> assert false (* absurd case *)
          | Lam_cbnd_PreRefSem.Coq_vStruct (k1, xs0, _, s) ->
            (match k1 with
             | Lam_cbnd_PreRefSem.E ->
               let hh = in_split Lam_cbnd_PreRefSem.eq_var x0 xs0 in
               (match hh with
                | Inleft s5 ->
                  let ExistT (x1, s6) = s5 in
                  let ExistT (x2, _) = s6 in
                  Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.E,
                  (set_union Lam_cbnd_PreRefSem.eq_var xs (app x1 x2)), ys,
                  (Lam_cbnd_PreRefSem.Coq_sNdSub (x0, (app x1 x2), xs,
                  (app x1 (x0::x2)), s1, s))))
                | Inright ->
                  Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubWrong
                    (Lam_cbnd_PreRefSem.E, x0, xs, ys, xs0, s1, s)))
             | Lam_cbnd_PreRefSem.C -> assert false (* absurd case *))
          | Lam_cbnd_PreRefSem.Coq_vNeu (_, l, y, _, c) ->
            Coq_ed_val
              (let val0 = Lam_cbnd_PreRefSem.Coq_inctxNdSub (Lam_cbnd_PreRefSem.E,
                 x0, y, xs, l, s1, c)
               in
               Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.E,
               (set_union Lam_cbnd_PreRefSem.eq_var xs
                 (set_remove Lam_cbnd_PreRefSem.eq_var x0 l)), y, ys, val0))
          | Lam_cbnd_PreRefSem.Coq_vELam (_, y, r, s) ->
            Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubNdE (x0, xs, ys, s1, y, r, s)))
       | Lam_cbnd_PreRefSem.C ->
         (match v with
          | Lam_cbnd_PreRefSem.Coq_vCLam (xs0, _, nl) ->
            let s4 = in_split Lam_cbnd_PreRefSem.eq_var x0 xs0 in
            (match s4 with
             | Inleft s5 ->
               let ExistT (x1, s6) = s5 in
               let ExistT (x2, _) = s6 in
               let vv = Lam_cbnd_PreRefSem.Coq_lnfNdSub (x0, (app x1 x2), xs,
                 (app x1 (x0::x2)), s1, nl)
               in
               Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vCLam
               ((set_union Lam_cbnd_PreRefSem.eq_var xs (app x1 x2)), ys, vv))
             | Inright ->
               Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubWrong2 (x0, xs, ys, xs0, s1,
                 nl)))
          | Lam_cbnd_PreRefSem.Coq_vStruct (k1, l, _, s) ->
            (match k1 with
             | Lam_cbnd_PreRefSem.E -> assert false (* absurd case *)
             | Lam_cbnd_PreRefSem.C ->
               (match in_split Lam_cbnd_PreRefSem.eq_var x0 l with
                | Inleft x1 ->
                  let ExistT (x2, s4) = x1 in
                  let ExistT (x3, _) = s4 in
                  Coq_ed_val (Lam_cbnd_PreRefSem.Coq_vStruct (Lam_cbnd_PreRefSem.C,
                  (set_union Lam_cbnd_PreRefSem.eq_var xs (app x2 x3)), ys,
                  (Lam_cbnd_PreRefSem.Coq_sNdSub (x0, (app x2 x3), xs,
                  (app x2 (x0::x3)), s1, s))))
                | Inright ->
                  Coq_ed_red (Lam_cbnd_PreRefSem.Coq_rSubWrong
                    (Lam_cbnd_PreRefSem.C, x0, xs, ys, l, s1, s))))
          | Lam_cbnd_PreRefSem.Coq_vNeu (_, xs0, y, _, c) ->
            Coq_ed_val
              (let val0 = Lam_cbnd_PreRefSem.Coq_inctxNdSub (Lam_cbnd_PreRefSem.C,
                 x0, y, xs, xs0, s1, c)
               in
               Lam_cbnd_PreRefSem.Coq_vNeu (Lam_cbnd_PreRefSem.C,
               (set_union Lam_cbnd_PreRefSem.eq_var xs
                 (set_remove Lam_cbnd_PreRefSem.eq_var x0 xs0)), y, ys, val0))
          | Lam_cbnd_PreRefSem.Coq_vELam (_, _, _, _) ->
            assert false (* absurd case *)))

  type elem_context_in =
  | Coq_ec_in of Lam_cbnd_PreRefSem.ckind * Lam_cbnd_PreRefSem.elem_context_kinded

  (** val elem_context_in_rect :
      Lam_cbnd_PreRefSem.ckind -> (Lam_cbnd_PreRefSem.ckind ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> 'a1) -> elem_context_in -> 'a1 **)

  let elem_context_in_rect _ f = function
  | Coq_ec_in (x0, x1) -> f x0 x1

  (** val elem_context_in_rec :
      Lam_cbnd_PreRefSem.ckind -> (Lam_cbnd_PreRefSem.ckind ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> 'a1) -> elem_context_in -> 'a1 **)

  let elem_context_in_rec _ f = function
  | Coq_ec_in (x0, x1) -> f x0 x1

  (** val ec_kinded_to_in :
      Lam_cbnd_PreRefSem.ckind -> Lam_cbnd_PreRefSem.ckind ->
      Lam_cbnd_PreRefSem.elem_context_kinded -> elem_context_in **)

  let ec_kinded_to_in _ k2 ec =
    Coq_ec_in (k2, ec)
 end

module Lam_cbn_RefSem = RedRefSem(Lam_cbnd_PreRefSem)(Lam_cbn_Strategy)

module Lam_cbn_EAM = RefEvalApplyMachine(Lam_cbn_RefSem)

module Lam_cbn_sim = DetAbstractMachine_Sim(Lam_cbn_EAM)

(** val x : Lam_cbnd_PreRefSem.id **)

let x =
  succ 0

(** val id0 : Lam_cbnd_PreRefSem.expr **)

let id0 =
  Lam_cbnd_PreRefSem.Lam (x, (Lam_cbnd_PreRefSem.Var x))

(** val list_configs :
    Lam_cbn_EAM.configuration option -> int -> int ->
    (int*Lam_cbn_EAM.configuration) list **)

let rec list_configs c n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' ->
    match c with
    | Some c' -> (i,c')::(list_configs (Lam_cbn_sim.n_steps c' (succ 0)) n' (succ i))
    | None -> [])
    n

(** val list_configurations :
    Lam_cbn_EAM.term -> int -> (int*Lam_cbn_EAM.configuration) list **)

let rec list_configurations t n =
  list_configs (Some (Lam_cbn_EAM.load t)) n (succ 0)

(** val test1 : (int*Lam_cbn_EAM.configuration) list **)

let test1 =
  list_configurations id0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ 0))))))))))))))))))))))))))))))))))))))))))))))))))
