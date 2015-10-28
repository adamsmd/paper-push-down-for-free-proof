Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import Lists.List.
Require Import Logic.FunctionalExtensionality.
Require Import Arith.
Require Import Program.
Require Import Setoid.
Require Import Coq.Logic.ClassicalFacts.

Set Printing Implicit.

(*

??? TODO: rewrite to make an "(x y)" work.

Temporarily set "in H" as default.
*Do a rewrite under a "forall"? Ltac under exists?
*Short alias for "rewrite"
Always have "done" and "auto" running in the background?
Find where I made the choice that caused this subterm to be "X".
Need "tacktics modulo equalities"
*Way to suggest name for "move => ?".


H a : X a = Y a.
forall a. X a = forall a. Y a

A way to say "eval this" 
*Way to do "exists ?" then refine "?" later

is "apply: H" different than "apply/H"?

TODO: proving about equalities between Prop

relf_True

*)

(*****************)
(*** Utilities ***)
(*****************)

(** Pairs **)
Ltac pairs :=
repeat match goal with
| [ |- context[fst(?X,?Y)]] => rewrite /(fst (X, Y))
| [ |- context[snd(?X,?Y)]] => rewrite /(snd (X, Y))
| [ |- context[fst(?X,?Y) _]] => rewrite /(fst (X, Y))
| [ |- context[snd(?X,?Y) _]] => rewrite /(snd (X, Y))
| [ |- context[fst(?X,?Y) _ _]] => rewrite /(fst (X, Y))
| [ |- context[snd(?X,?Y) _ _]] => rewrite /(snd (X, Y))
| [ |- context[let: (_, _) := ?Z in _]] => rewrite (surjective_pairing Z)
end ;
repeat match goal with
| [ |- context[(fst ?X, snd ?X)]] => rewrite -(surjective_pairing X)
end.


(** Equality **)
Definition eq_dec A := forall x y : A, {x = y} + {x <> y}.
Definition eq_bool {A : Set} (e : eq_dec A) (x : A) (y : A) : bool :=
match e x y with
| left _ => true
| right _ => false
end.
Lemma eq_bool_correct_true {A : Set} {e} {x y : A} :
  eq_bool e x y = true <-> x = y.
Proof with try pairs; solve [done].
rewrite /eq_bool; by case: (e x y)...
Qed.
Lemma eq_bool_correct_false {A : Set} {e} {x y : A} :
  eq_bool e x y = false <-> x <> y.
Proof.
rewrite /eq_bool; by case: (e x y).
Qed.
Lemma eq_bool_correct {A : Set} {e} {x y : A} :
  (eq_bool e x y = true <-> x = y) /\ (eq_bool e x y = false <-> x <> y).
Proof.
split.
apply: eq_bool_correct_true.
apply: eq_bool_correct_false.
Qed.

(** Sets **)
Definition set s := s -> Prop.
Definition set_union {A:Set} (s : set A) (t : set A) : set A := fun x => s x \/ t x.

(* We need this because of how we formalize sets.  Eventually we should use setoids for sets, then we won't need this. *)
Axiom eq_Prop: prop_extensionality.

Definition subseteq {A : Set} (s : set A) (t : set A) : Prop := forall x, s x -> t x.

Notation "∀ x ∈ y , z" := (forall x, y x -> z) (at level 70, right associativity).
Notation "∃ x ∈ y , z" := (exists x, y x /\ z) (at level 70, right associativity).
Notation "x ⊆ y" := (subseteq x y) (at level 70, right associativity).

Lemma set_trans {A : Set} {s1 : set A} {s2 : set A} {s3 : set A}:
  s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
Proof.
by rewrite /subseteq; auto.
Qed.


(** Stores **)

Definition store A B := A -> set B.
Definition substore {A B : Set} (s s' : store A B) := forall a, subseteq (s a) (s' a).

Notation "∀ w ↦ x ∈ y , z" := (forall w x, y w x -> z) (at level 70, right associativity).
Notation "∃ w ↦ x ∈ y , z" := (exists w x, y w x /\ z) (at level 70, right associativity).
Notation "x ⊑ y" := (substore x y) (at level 70, right associativity).

Lemma store_trans {A B : Set} {s1 : store A B} {s2 : store A B} {s3 : store A B}:
  s1 ⊑ s2 -> s2 ⊑ s3 -> s1 ⊑ s3.
Proof.
by rewrite /substore /subseteq; auto.
Qed.


(*******************)
(*** Expressions ***)
(*******************)

Definition Var := nat % type.

Definition eq_Var_dec : eq_dec Var := eq_nat_dec.
Definition eq_Var := eq_bool eq_Var_dec.

Inductive AExp : Set := Ref : Var -> AExp | Lam : Var -> Exp -> AExp
     with Exp : Set := Let : Var -> AExp -> AExp -> Exp -> Exp | Ret : AExp -> Exp.
(* TODO: add tail calls *)

Parameter e_0 : Exp.

Implicit Types x x_hat x_til : Var.
Implicit Types e e_hat e_til b b_hat b_til : Exp.
Implicit Types ae ae_hat ae_til f f_hat f_til: AExp.

Definition ρ_extend {A : Set} (ρ : Var -> A) (x : Var) (a : A) : Var -> A :=
  fun x' => if eq_Var x x' then a else ρ x.

Definition σ_extend {Addr Clo : Set} (eq_Addr : Addr -> Addr -> bool)
  (σ : store Addr Clo) (a : Addr) (d : set Clo) : store Addr Clo :=
  fun a' => if eq_Addr a a' then d else fun _ => False.

Lemma σ_extend_ind {T P : Set} eq σ σ' (a : T) (v : set P):
  σ_extend eq σ a v = σ_extend eq σ' a v.
Proof.
by rewrite /σ_extend.
Qed.


(*****************)
(*** Hat forms ***)
(*****************)

Parameter Addr_hat : Set.
Parameter eq_Addr_hat_dec : eq_dec Addr_hat.
Definition eq_Addr_hat := eq_bool eq_Addr_hat_dec.

Definition Env_hat := Var -> Addr_hat. (* Total as we assume it is only applied when the variable is in scope *)

Definition Clo_hat := (Var * Exp * Env_hat) % type.
Definition D_hat := set Clo_hat.
Definition Store_hat := Addr_hat -> D_hat.

Definition Frame_hat := (Var * Exp * Env_hat) % type.
Definition Kont_hat := list Frame_hat.
Definition K_hat := set Kont_hat.

Definition C_hat := (Exp * Env_hat * Kont_hat) % type.
Definition Σ_hat := (Exp * Env_hat * Kont_hat * Store_hat) % type. (* We put Store_hat at the end to make combining a C_hat with a Store_hat easier *)

Definition R_hat := set C_hat.
Definition Ξ_hat := (R_hat * Store_hat) % type.

Parameter alloc_hat : Var -> Σ_hat -> Addr_hat.

Implicit Types a_hat a'_hat : Addr_hat.
Implicit Types ρ_hat ρ'_hat ρ_λ_hat ρ_κ_hat : Env_hat.
Implicit Types clo_hat clo'_hat : Clo_hat.
Implicit Types d_hat d'_hat : D_hat.
Implicit Types σ_hat σ'_hat σ''_hat : Store_hat.
Implicit Types φ_hat φ'_hat : Frame_hat.
Implicit Types κ_hat κ'_hat : Kont_hat.
Implicit Types k_hat k'_hat : K_hat.
Implicit Types ϛ_hat ϛ'_hat : Σ_hat.
Implicit Types c_hat c'_hat : C_hat.
Implicit Types r_hat r'_hat : R_hat.
Implicit Types ξ_hat ξ'_hat : Ξ_hat.


(*******************)
(*** Tilde forms ***)
(*******************)

Parameter Addr_til : Set.
Parameter eq_Addr_til_dec : eq_dec Addr_til.
Definition eq_Addr_til := eq_bool eq_Addr_til_dec.

Parameter KAddr_til : Set.
Parameter eq_KAddr_til_dec : eq_dec KAddr_til.
Definition eq_KAddr_til := eq_bool eq_KAddr_til_dec.

Definition Env_til := Var -> Addr_til. (* Total as we assume it is only applied when the variable is in scope *)

Definition Clo_til := (Var * Exp * Env_til) % type.
Definition D_til := set Clo_til.
Definition Store_til := Addr_til -> D_til.

Definition Frame_til := (Var * Exp * Env_til) % type.
Definition Kont_til := (Frame_til * KAddr_til) % type.
Definition K_til := set Kont_til.
Definition KStore_til := KAddr_til -> K_til.

Definition C_til := (Exp * Env_til * KAddr_til) % type.
Definition Σ_til := (Exp * Env_til * KAddr_til * (Store_til * KStore_til)) % type.  (* We put Store_til and KStore_til at the end to make combining a C_til with a Store_til and KStore_til easier *)

Definition R_til := set C_til.
Definition Ξ_til := (R_til * (Store_til * KStore_til)) % type.

Parameter alloc_til : Var -> Σ_til -> Addr_til.
(* TODO: why these arguments? A: b/c it is the ϛ_til and ϛ'_til minus σ'_κ_til and a'_κ_til, which depend on alloc_κ_til. *)
Parameter alloc_κ_til : Σ_til -> Exp -> Env_til -> Store_til -> KAddr_til.

Implicit Types a_til a'_til : Addr_til.
Implicit Types a_κ_til a'_κ_til : KAddr_til.
Implicit Types ρ_til ρ'_til ρ_λ_til ρ_κ_til : Env_til.
Implicit Types clo_til clo'_til : Clo_til.
Implicit Types d_til d'_til : D_til.
Implicit Types σ_til σ'_til σ''_til : Store_til.
Implicit Types φ_til φ'_til : Frame_til.
Implicit Types κ_til κ'_til : Kont_til.
Implicit Types k_til k'_til : K_til.
Implicit Types σ_κ_til σ'_κ_til σ''_κ_til : KStore_til.
Implicit Types ϛ_til ϛ'_til : Σ_til.
Implicit Types c_til c'_til : C_til.
Implicit Types r_til r'_til : R_til.
Implicit Types ξ_til ξ'_til : Ξ_til.

(**************************************)
(*** Bijections between hat and til ***)
(**************************************)

Parameter Addr_til_hat : Addr_til -> Addr_hat.
Parameter Addr_hat_til : Addr_hat -> Addr_til.
Definition Env_til_hat ρ_til : Env_hat := fun x => Addr_til_hat (ρ_til x).
Definition Env_hat_til ρ_hat : Env_til := fun x => Addr_hat_til (ρ_hat x).

Definition Clo_til_hat clo_til : Clo_hat := (clo_til.1.1, clo_til.1.2, Env_til_hat clo_til.2).
Definition Clo_hat_til clo_hat : Clo_til := (clo_hat.1.1, clo_hat.1.2, Env_hat_til clo_hat.2).

Definition D_til_hat d_til : D_hat := fun clo_hat => d_til (Clo_hat_til clo_hat).
Definition D_hat_til d_hat : D_til := fun clo_til => d_hat (Clo_til_hat clo_til).

Definition Store_til_hat σ_til : Store_hat := fun a_hat => D_til_hat (σ_til (Addr_hat_til a_hat)).
Definition Store_hat_til σ_hat : Store_til := fun a_til => D_hat_til (σ_hat (Addr_til_hat a_til)).

Definition Frame_til_hat φ_til : Frame_hat := (φ_til.1.1, φ_til.1.2, Env_til_hat φ_til.2).
Definition Frame_hat_til φ_hat : Frame_til := (φ_hat.1.1, φ_hat.1.2, Env_hat_til φ_hat.2).

Definition Konts_til_hat : list Kont_til -> Kont_hat := map (Frame_til_hat ∘ fst).

Definition C_til_hat c_til κs_til : C_hat := (c_til.1.1, Env_til_hat c_til.1.2, Konts_til_hat κs_til).
Definition Σ_til_hat ϛ_til κs_til: Σ_hat := (C_til_hat ϛ_til.1 κs_til, Store_til_hat ϛ_til.2.1).


(** Conversions are bijections *)
Definition bij {rT aT} (f : aT -> rT) g := cancel f g /\ cancel g f.

Parameter Addr_bij : bij Addr_til_hat Addr_hat_til.

Lemma Env_bij : bij Env_til_hat Env_hat_til.
Proof.
by split => [a | a];
rewrite /Env_hat_til /Env_til_hat;
apply: functional_extensionality => x;
rewrite ?Addr_bij.1 ?Addr_bij.2.
Qed.

Lemma Clo_bij : bij Clo_til_hat Clo_hat_til.
Proof.
rewrite /Clo_til_hat /Clo_hat_til.
by split => [clo_til | clo_hat]; rewrite ?Env_bij.1 ?Env_bij.2; pairs.
Qed.

Lemma D_bij : bij D_til_hat D_hat_til.
Proof.
rewrite /D_hat_til /D_til_hat.
by split => [d_til | d_hat];
apply: functional_extensionality => clo_til;
rewrite ?Clo_bij.1 ?Clo_bij.2.
Qed.

Lemma Store_bij : bij Store_til_hat Store_hat_til.
Proof.
rewrite /Store_hat_til /Store_til_hat.
by split => [σ_til | σ_hat];
apply: functional_extensionality => a;
rewrite ?D_bij.1 ?D_bij.2 ?Addr_bij.1 ?Addr_bij.2.
Qed.

Lemma Frame_bij : bij Frame_til_hat Frame_hat_til.
Proof.
rewrite /Frame_hat_til /Frame_til_hat.
by split => [φ_til | φ_hat]; rewrite ?Env_bij.1 ?Env_bij.2; pairs.
Qed.


(**********************)
(*** Initial states ***)
(**********************)

Parameter ρ_0_hat: Env_hat.
Definition c_0_hat: C_hat := (e_0, ρ_0_hat, nil).
Definition σ_0_hat: Store_hat := fun _ _ => False.
Definition ϛ_0_hat: Σ_hat := (c_0_hat, σ_0_hat).
Definition ξ_0_hat: Ξ_hat := (fun c_hat => c_hat = c_0_hat, σ_0_hat).

Parameter a_κ_0_til: KAddr_til.
Definition ρ_0_til: Env_til := (Env_hat_til ρ_0_hat).
Definition c_0_til: C_til := (e_0, ρ_0_til, a_κ_0_til).
Definition σ_0_til: Store_til := fun _ _ => False.
Definition σ_κ_0_til: KStore_til := fun _ _ => False.
Definition ϛ_0_til: Σ_til := (c_0_til, (σ_0_til, σ_κ_0_til)).
Definition ξ_0_til: Ξ_til := (fun c_til => c_til = c_0_til, (σ_0_til, σ_κ_0_til)).

Lemma ρ_0_til_hat: ρ_0_hat = Env_til_hat ρ_0_til.
Proof. by rewrite /ρ_0_til Env_bij.2. Qed.

Lemma c_0_til_hat: c_0_hat = C_til_hat c_0_til nil.
Proof. by rewrite /C_til_hat /c_0_hat /c_0_til ρ_0_til_hat. Qed.

(*
Lemma σ_0_til_hat: σ_0_hat = Store_til_hat σ_0_til.
Definition c_0_til: C_til := (e_0, ρ_0_til, a_κ_0_til).
Definition σ_0_til: Store_til := fun _ _ => False.
Definition σ_κ_0_til: KStore_til := fun _ _ => False.
Definition ϛ_0_til: Σ_til := (c_0_til, (σ_0_til, σ_κ_0_til)).
Definition ξ_0_til: Ξ_til := (fun c_til => c_til = c_0_til, (σ_0_til, σ_κ_0_til)).
*)


(**************)
(*** Stacks ***)
(**************)

(** The stacks implied to exist by a_κ_til and σ_κ_til **)
Inductive stacks σ_κ_til a_κ_til : set (list Kont_til) :=
  stacks_null : a_κ_til = a_κ_0_til -> stacks σ_κ_til a_κ_til nil
| stacks_cons κ_til κs_til:
    a_κ_til <> a_κ_0_til ->
    stacks σ_κ_til κ_til.2 κs_til ->
    σ_κ_til a_κ_til κ_til ->
    stacks σ_κ_til a_κ_til (κ_til :: κs_til).

Lemma stacks_null_Addr {σ_κ_til a_κ_til}:
  stacks σ_κ_til a_κ_til nil ->
  a_κ_til = a_κ_0_til.
Proof.
move => H_stacks.
inversion H_stacks; try done.
Qed.

Lemma stacks_null_Konts {σ_κ_til κs_til}:
  stacks σ_κ_til a_κ_0_til κs_til ->
  κs_til = nil.
Proof.
move => H_stacks.
inversion H_stacks; try done.
Qed.

Lemma stacks_cons_Kont {σ_κ_til a_κ_til κ_til κs_til}:
  stacks σ_κ_til a_κ_til (κ_til :: κs_til) ->
  a_κ_til <> a_κ_0_til /\ stacks σ_κ_til κ_til.2 κs_til /\ σ_κ_til a_κ_til κ_til.
Proof.
move => H_stacks.
inversion H_stacks; try done.
Qed.

(**************************)
(*** Defining Precision ***)
(**************************)

Definition prec_Addr a_hat a_til := a_hat = Addr_til_hat a_til.
Definition prec_Env ρ_hat ρ_til := forall x, prec_Addr (ρ_hat x) (ρ_til x).
Definition prec_Clo clo_hat clo_til := (clo_hat.1 = clo_til.1) /\ prec_Env clo_hat.2 clo_til.2.
Definition prec_D d_hat d_til :=
  forall clo_hat clo_til, prec_Clo clo_hat clo_til -> d_til clo_til -> d_hat clo_hat.
(* TODO: note the changed def of prec_D *)
Definition prec_Store σ_hat σ_til :=
  forall a_hat a_til, prec_Addr a_hat a_til -> prec_D (σ_hat a_hat) (σ_til a_til).
Definition prec_Frame φ_hat φ_til :=
  φ_hat.1.1 = φ_til.1.1 /\ φ_hat.1.2 = φ_til.1.2 /\ prec_Env φ_hat.2 φ_til.2.

Definition prec_R ξ_hat ξ_til :=
  ∀c_til ∈ ξ_til.1,
  ∀κs_til ∈ stacks ξ_til.2.2 c_til.2,
    ξ_hat.1 (C_til_hat c_til κs_til).

Definition prec_Ξ ξ_hat ξ_til :=
  prec_R ξ_hat ξ_til /\
  prec_Store ξ_hat.2 ξ_til.2.1.

Notation "x ⊒_Addr y" := (prec_Addr x y) (at level 70, no associativity).
Notation "x ⊒_Env y" := (prec_Env x y) (at level 70, no associativity).
Notation "x ⊒_Clo y" := (prec_Clo x y) (at level 70, no associativity).
Notation "x ⊒_D y" := (prec_D x y) (at level 70, no associativity).
Notation "x ⊒_Store y" := (prec_Store x y) (at level 70, no associativity).
Notation "x ⊒_Frame y" := (prec_Frame x y) (at level 70, no associativity).
Notation "x ⊒_R y" := (prec_R x y) (at level 70, no associativity).
Notation "x ⊒_Ξ y" := (prec_Ξ x y) (at level 70, no associativity).

(** Conversions respect precision **)

Definition prec_bij {A B} (prec : A -> B -> Prop) (f : A -> B) (g : B -> A) :=
  (forall X, unique (prec X) (f X)) /\ (forall Y, unique (fun X => prec X Y) (g Y)).

(* Conversions of Store and D are non-unique but have a weakened bijection *)
Definition prec_bij_non_unique {A B} (prec : A -> B -> Prop) (f : A -> B) (g : B -> A) :=
  (forall X, prec X (f X)) /\ (forall Y, prec (g Y) Y).

Lemma prec_Addr_bij : prec_bij prec_Addr Addr_hat_til Addr_til_hat.
Proof.
rewrite /prec_Addr.
split => [a | a]; split => [| x]; rewrite ?Addr_bij.1 ?Addr_bij.2; try done.
by move => H; rewrite H ?Addr_bij.1 ?Addr_bij.2.
Qed.

Lemma prec_Env_bij : prec_bij prec_Env Env_hat_til Env_til_hat.
Proof.
rewrite /prec_Env /Env_hat_til.
split => [ρ_1 | ρ_1]; split => [x | ρ_2 H].
by move: (Addr_bij.2 (ρ_1 x)).
apply: functional_extensionality => x.
by apply: ((prec_Addr_bij.1 (ρ_1 x)).2 (ρ_2 x)).
by move: (Addr_bij.1 (ρ_1 x)).
apply: functional_extensionality => x.
by apply: ((prec_Addr_bij.2 (ρ_1 x)).2 (ρ_2 x)).
Qed.

Lemma prec_Clo_bij : prec_bij prec_Clo Clo_hat_til Clo_til_hat.
Proof.
split => [clo_hat | clo_til]; split => [|clo_2]; rewrite /prec_Clo /Clo_hat_til /Clo_til_hat; pairs.
split; try done.
by apply prec_Env_bij.1.
move: ((prec_Env_bij.1 clo_hat.2).2 clo_2.2).
by move => H [Ha Hb]; rewrite (H Hb) Ha; pairs.
by split.
move: ((prec_Env_bij.2 clo_til.2).2 clo_2.2).
by move => H [Ha Hb]; rewrite (H Hb) -Ha; pairs.
Qed.

Lemma prec_D_bij : prec_bij_non_unique prec_D D_hat_til D_til_hat.
Proof.
rewrite /D_hat_til /D_til_hat /prec_D.
split => [d_hat clo_hat clo_til H | d_til clo_hat clo_til H].
by rewrite ((prec_Clo_bij.2 clo_til).2 clo_hat H).
by rewrite ((prec_Clo_bij.1 clo_hat).2 clo_til H).
Qed.

Lemma prec_Store_bij : prec_bij_non_unique prec_Store Store_hat_til Store_til_hat.
Proof.
rewrite /prec_Store /Store_hat_til /Store_til_hat /prec_bij_non_unique.
split => [σ_hat a_hat a_til H | σ_til a_hat a_til H].
rewrite ((prec_Addr_bij.2 a_til).2 a_hat H).
by move: (prec_D_bij.1 (σ_hat a_hat)).
move: (prec_D_bij.2 (σ_til a_til)).
by rewrite ((prec_Addr_bij.1 a_hat).2 a_til H).
Qed.

Lemma prec_Frame_bij : prec_bij prec_Frame Frame_hat_til Frame_til_hat.
Proof.
rewrite /prec_Frame /Frame_hat_til /Frame_til_hat.
split => [φ_hat | φ_til]; split => [|φ].
by move: (prec_Env_bij.1 φ_hat.2).1.
move => [H1 [H2 H3]].
move: ((prec_Env_bij.1 φ_hat.2).2 φ.2 H3) => H4.
by rewrite H1 H2 H4; pairs.
pairs.
by move: ((prec_Env_bij.2 φ_til.2).2 (Env_til_hat φ_til.2) ((prec_Env_bij.2 φ_til.2).1)).
move => [H1 [H2 H3]].
move: ((prec_Env_bij.2 φ_til.2).2 φ.2 H3) => H4.
by rewrite -H1 -H2 H4; pairs.
Qed.


(******************************)
(*** Step Relations for Hat ***)
(******************************)

Definition A_hat ae ρ_hat σ_hat : D_hat :=
match ae with
| Ref x => σ_hat (ρ_hat x)
| Lam x e => fun clo => clo = (x, e, ρ_hat)
end.

Definition step_Σ_hat_Let_func x f ae b ρ_hat κ_hat σ_hat x' e' ρ_λ_hat : Σ_hat :=
 let ϛ_hat := (Let x f ae b, ρ_hat, κ_hat, σ_hat) in
 let a'_hat := alloc_hat x' ϛ_hat in
 let ρ'_hat := ρ_extend ρ_λ_hat x' a'_hat in
 let σ'_hat := σ_extend eq_Addr_hat σ_hat a'_hat (A_hat ae ρ_hat σ_hat) in
 let κ'_hat := (x, b, ρ_hat) :: κ_hat in
 (e', ρ'_hat, κ'_hat, σ'_hat).

Definition step_Σ_hat_Ret_func ae ρ_hat σ_hat x e' ρ_κ_hat κ'_hat : Σ_hat :=
 let ϛ_hat := (Ret ae, ρ_hat, cons (x, e', ρ_κ_hat) κ'_hat, σ_hat) in
 let a'_hat := alloc_hat x ϛ_hat in
 let ρ'_hat := ρ_extend ρ_κ_hat x a'_hat in
 let σ'_hat := σ_extend eq_Addr_hat σ_hat a'_hat (A_hat ae ρ_hat σ_hat) in
 (e', ρ'_hat, κ'_hat, σ'_hat).

Inductive step_Σ_hat : Σ_hat -> Σ_hat -> Prop :=
| step_Σ_hat_Let x f ae b ρ_hat κ_hat σ_hat x' e' ρ_λ_hat:
  A_hat f ρ_hat σ_hat (x', e', ρ_λ_hat) ->
  step_Σ_hat (Let x f ae b, ρ_hat, κ_hat, σ_hat)
    (step_Σ_hat_Let_func x f ae b ρ_hat κ_hat σ_hat  x' e' ρ_λ_hat)
| step_Σ_hat_Ret ae ρ_hat σ_hat x e' ρ_κ_hat κ'_hat:
  step_Σ_hat (Ret ae, ρ_hat, (x, e', ρ_κ_hat) :: κ'_hat, σ_hat)
    (step_Σ_hat_Ret_func ae ρ_hat σ_hat x e' ρ_κ_hat κ'_hat).

(* NOTE: since we only talk about "hat" at the fixed point,
         only the output is subsetted *)
Definition step_Σ_sub_hat ϛ_hat ϛ'_hat :=
  exists σ'_hat,
    σ'_hat ⊑ ϛ'_hat.2 /\
    step_Σ_hat ϛ_hat (ϛ'_hat.1, σ'_hat).

Definition step_Ξ_hat ξ_hat : Ξ_hat :=
  let: (r_hat, σ_hat) := ξ_hat in
  let: s_hat := fun ϛ_hat => ϛ_hat = ϛ_0_hat \/
    exists c_hat, r_hat c_hat /\ step_Σ_hat (c_hat, σ_hat) ϛ_hat in
  ((fun (c_hat : C_hat) => exists σ_hat, s_hat (c_hat, σ_hat)),
   (fun a_hat clo_hat => ∃ϛ_hat ∈ s_hat, ϛ_hat.2 a_hat clo_hat)).

Notation "x ⟶Σ^ y" := (step_Σ_hat x y) (at level 70, no associativity).
Notation "x ⟶Σ<^ y" := (step_Σ_sub_hat x y) (at level 70, no associativity).
Notation "x ⟶Ξ^ y" := (step_Ξ_hat x = y) (at level 70, no associativity).


(******************************)
(*** Step Relations for Til ***)
(******************************)

Definition A_til ae ρ_til σ_til : D_til :=
match ae with
| Ref x => σ_til (ρ_til x)
| Lam x e => fun clo => clo = (x, e, ρ_til)
end.

Definition step_Σ_til_Let_func x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til : Σ_til :=
  let ϛ_til := (Let x f ae b, ρ_til, a_κ_til, (σ_til, σ_κ_til)) in
  let a_til := alloc_til x' ϛ_til in
  let ρ'_til := ρ_extend ρ_λ_til x' a_til in
  let σ'_til := σ_extend eq_Addr_til σ_til a_til (A_til ae ρ_til σ_til) in
  let a'_κ_til := alloc_κ_til ϛ_til e' ρ'_til σ'_til in
  let σ'_κ_til := σ_extend eq_KAddr_til σ_κ_til a'_κ_til (fun z => z = ((x, b, ρ_til), a_κ_til)) in
  (e', ρ'_til, a'_κ_til, (σ'_til, σ'_κ_til)).

Definition step_Σ_til_Ret_func ae ρ_til a_κ_til σ_til σ_κ_til x e' ρ_κ_til a'_κ_til : Σ_til :=
  let ϛ_til := (Ret ae, ρ_til, a_κ_til, (σ_til, σ_κ_til)) in
  let a_til := alloc_til x ϛ_til in
  let ρ'_til := ρ_extend ρ_κ_til x a_til in
  let σ'_til := σ_extend eq_Addr_til σ_til a_til (A_til ae ρ_til σ_til) in
  (e', ρ'_til, a'_κ_til, (σ'_til, fun _ _ => False)).

(*
TODO:

Inductive step_Σ_til_Let : Σ_til -> Σ_til -> Prop :=
| Step_Σ_til_Let x f ae b ρ_til σ_til σ_κ_til a_κ_til x' e' ρ_λ_til:
  A_til f ρ_til σ_til (x', e', ρ_λ_til) ->
  step_Σ_til_Let (Let x f ae b, ρ_til, a_κ_til, (σ_til, σ_κ_til))
    (step_Σ_til_Let_func x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til).

Inductive step_Σ_til_Ret : Σ_til -> Σ_til -> Prop :=
| Step_Σ_til_Ret ae ρ_til σ_til σ_κ_til a_κ_til x e' ρ_κ_til a'_κ_til:
  σ_κ_til a_κ_til ((x, e', ρ_κ_til), a'_κ_til) ->
  step_Σ_til_Ret (Ret ae, ρ_til, a_κ_til, (σ_til, σ_κ_til))
    (step_Σ_til_Ret_func ae ρ_til a_κ_til σ_til σ_κ_til x e' ρ_κ_til a'_κ_til).
*)

Inductive step_Σ_til : Σ_til -> Σ_til -> Prop :=
| step_Σ_til_Let x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til:
  A_til f ρ_til σ_til (x', e', ρ_λ_til) ->
  step_Σ_til (Let x f ae b, ρ_til, a_κ_til, (σ_til, σ_κ_til))
    (step_Σ_til_Let_func x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til)

| step_Σ_til_Ret ae ρ_til a_κ_til σ_til σ_κ_til x e' ρ_κ_til a'_κ_til:
  σ_κ_til a_κ_til ((x, e', ρ_κ_til), a'_κ_til) ->
  step_Σ_til (Ret ae, ρ_til, a_κ_til, (σ_til, σ_κ_til))
    (step_Σ_til_Ret_func ae ρ_til a_κ_til σ_til σ_κ_til x e' ρ_κ_til a'_κ_til).

Definition step_Σ_sub_til ϛ_til ϛ'_til :=
  exists σ'_til σ'_κ_til,
    σ'_til ⊑ ϛ'_til.2.1 /\
    σ'_κ_til ⊑ ϛ'_til.2.2 /\
    step_Σ_til ϛ_til (ϛ'_til.1, (σ'_til, σ'_κ_til)).

(*
Definition step_Σ_sub_til ϛ_til ϛ'_til :=
  exists σ_til σ_κ_til σ'_til σ'_κ_til,
    σ_til ⊑ ϛ_til.2.1 /\
    σ_κ_til ⊑ ϛ_til.2.2 /\
    σ'_til ⊑ ϛ'_til.2.1 /\
    σ'_κ_til ⊑ ϛ'_til.2.2 /\
    step_Σ_til (ϛ_til.1, (σ_til, σ_κ_til)) (ϛ'_til.1, (σ'_til, σ'_κ_til)).
*)

Definition step_Σ_sub_clo_til a_til clo_til ϛ_til ϛ'_til :=
  exists σ'_til σ'_κ_til,
    σ'_til ⊑ ϛ'_til.2.1 /\
    σ'_κ_til ⊑ ϛ'_til.2.2 /\
    σ'_til a_til clo_til /\
    step_Σ_til ϛ_til (ϛ'_til.1, (σ'_til, σ'_κ_til)).

Definition step_Σ_sub_κ_til a_κ_til κ_til ϛ_til ϛ'_til :=
  exists σ'_til σ'_κ_til,
    σ'_til ⊑ ϛ'_til.2.1 /\
    σ'_κ_til ⊑ ϛ'_til.2.2 /\
    σ'_κ_til a_κ_til κ_til /\
    step_Σ_til ϛ_til (ϛ'_til.1, (σ'_til, σ'_κ_til)).

Definition step_Ξ_til ξ_til : Ξ_til :=
  let: (r_til, (σ_til, σ_κ_til)) := ξ_til in
  let: s_til := fun ϛ_til => ϛ_til = ϛ_0_til \/
    exists c_til, r_til c_til /\ step_Σ_til (c_til, (σ_til, σ_κ_til)) ϛ_til in
  ((fun (c_til : C_til) => exists σ_til σ_κ_til, s_til (c_til, (σ_til, σ_κ_til))),
  ((fun a_til clo_til => ∃ϛ_til ∈ s_til, ϛ_til.2.1 a_til clo_til),
   (fun a_κ_til κ_til => exists ϛ_til, (s_til ϛ_til /\ ϛ_til.2.2 a_κ_til κ_til)))).

Notation "x ⟶Σ~ y" := (step_Σ_til x y) (at level 70, no associativity).
Notation "x ⟶Σ<~ y" := (step_Σ_sub_til x y) (at level 70, no associativity).
Notation "x ⟶Σ<c~ y [ u ↦ v ]" := (step_Σ_sub_clo_til u v x y) (at level 70, no associativity).
Notation "x ⟶Σ<κ~ y [ u ↦ v ]" := (step_Σ_sub_κ_til u v x y) (at level 70, no associativity).
Notation "x ⟶Ξ~ y" := (step_Ξ_til x = y) (at level 70, no associativity).

Lemma step_Σ_sub_clo_til_weakening {a_til clo_til ϛ_til ϛ'_til}:
  step_Σ_sub_clo_til a_til clo_til ϛ_til ϛ'_til ->
  step_Σ_sub_til ϛ_til ϛ'_til.
Proof.
rewrite /step_Σ_sub_clo_til /step_Σ_sub_til.
move => [σ'_til] [σ'_κ_til] H.
exists σ'_til σ'_κ_til.
move: H.
do 3(case => ?).
by do ?split.
Qed.

Lemma step_Σ_sub_κ_til_weakening {a_κ_til κ_til ϛ_til ϛ'_til}:
  step_Σ_sub_κ_til a_κ_til κ_til ϛ_til ϛ'_til ->
  step_Σ_sub_til ϛ_til ϛ'_til.
Proof.
rewrite /step_Σ_sub_κ_til /step_Σ_sub_til.
move => [σ'_til] [σ'_κ_til] H.
exists σ'_til σ'_κ_til.
move: H.
do 3(case => ?).
by do ?split.
Qed.

(******************)
(*** Allocation ***)
(******************)

Parameter alloc_κ_0_til : forall ϛ_til e' ρ'_til σ'_til,
    alloc_κ_til ϛ_til e' ρ'_til σ'_til <> a_κ_0_til.

Parameter C_Addr_til: KAddr_til -> C_til.

Parameter C_Addr_til_Addr: forall a_κ_til,
  (C_Addr_til a_κ_til).2 = a_κ_til.

Parameter C_Addr_til_0: C_Addr_til a_κ_0_til = c_0_til.

Parameter C_Addr_til_inj: forall ϛ_til e' ρ'_til σ'_til,
  let: a_κ_til := alloc_κ_til ϛ_til e' ρ'_til σ'_til in
  C_Addr_til a_κ_til = (e', ρ'_til, a_κ_til).

Lemma C_Addr_til_inj' {x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til a'_κ_til κ_til}:
  let: ϛ_til := step_Σ_til_Let_func x f ae b ρ_til a_κ_til σ_til σ_κ_til x' e' ρ_λ_til in
  ϛ_til.2.2 a'_κ_til κ_til ->
  C_Addr_til a'_κ_til = ϛ_til.1.
Proof.
rewrite /step_Σ_til_Let_func /σ_extend /eq_KAddr_til //=.
case E: (eq_bool _ _); try done.
move => _.
rewrite -(eq_bool_correct_true.1 E).
by rewrite C_Addr_til_inj //=.
Qed.

Parameter prec_alloc: forall x ϛ_hat ϛ_til,
  ϛ_hat.1.1.1 = ϛ_til.1.1.1 ->
  prec_Env ϛ_hat.1.1.2 ϛ_til.1.1.2 ->
  (∃κs_til ∈ stacks ϛ_til.2.2 ϛ_til.1.2, Konts_til_hat κs_til = ϛ_hat.1.2) ->
  prec_Store ϛ_hat.2 ϛ_til.2.1 ->
  prec_Addr (alloc_hat x ϛ_hat) (alloc_til x ϛ_til).


(***********************************)
(*** Commutations of conversions ***)
(*** over other operators        ***)
(***********************************)

Lemma A_til_hat ae ρ_til σ_til:
  D_til_hat (A_til ae ρ_til σ_til) =
  A_hat ae (Env_til_hat ρ_til) (Store_til_hat σ_til).
Proof.
rewrite /A_hat /A_til.
case E: ae.
by rewrite /Store_til_hat /Env_til_hat Addr_bij.1.
apply functional_extensionality => clo_hat.
apply eq_Prop.
rewrite /D_til_hat.
split.
by rewrite -{2}(Clo_bij.2 clo_hat) /Clo_til_hat => ->.
move => ->.
by rewrite /Clo_hat_til Env_bij.1.
Qed.

(****)

Lemma A_hat_til ae ρ_hat σ_hat:
  D_hat_til (A_hat ae ρ_hat σ_hat) =
  A_til ae (Env_hat_til ρ_hat) (Store_hat_til σ_hat).
Proof.
rewrite /A_hat /A_til.
case E: ae.
by rewrite /Store_hat_til /Env_hat_til Addr_bij.2.
apply functional_extensionality => clo_til.
apply eq_Prop.
rewrite /D_hat_til.
split.
by rewrite -{2}(Clo_bij.1 clo_til) /Clo_hat_til => ->.
move => ->.
by rewrite /Clo_til_hat Env_bij.2.
Qed.


(***********************)
(*** Substore Lemmas ***)
(***********************)

Lemma substore_id {A B : Set} (σ : store A B): σ ⊑ σ.
Proof.
by rewrite /substore /subseteq.
Qed.

(* TODO *)

Lemma substore_A_hat {σ_sub_hat σ_hat} ae ρ_hat:
  σ_sub_hat ⊑ σ_hat ->
  A_hat ae ρ_hat σ_sub_hat ⊆ A_hat ae ρ_hat σ_hat.
Proof.
move => H.
rewrite /substore /subseteq in H *.
rewrite /A_hat => clo_hat.
case E: ae; auto.
Qed.

(****)

Lemma substore_A_til {σ_sub_til σ_til} ae ρ_til:
  σ_sub_til ⊑ σ_til ->
  A_til ae ρ_til σ_sub_til ⊆ A_til ae ρ_til σ_til.
Proof.
move => H_sub.
rewrite /A_til.
case E: ae => [v|].
rewrite /substore /subseteq in H_sub.
by move: (H_sub (ρ_til v)).
by [].
Qed.

(****)

(* TODO: lemma of prec_store? *)
Lemma substore_prec_Store {σ_hat σ_til}:
  prec_Store σ_hat σ_til ->
  σ_til ⊑ Store_hat_til σ_hat /\
  Store_til_hat σ_til ⊑ σ_hat.
Proof.
move => H.

split.

move => a_til clo_til.
by move: (H (Addr_til_hat a_til) a_til (prec_Addr_bij.2 a_til).1
            (Clo_til_hat clo_til) clo_til (prec_Clo_bij.2 clo_til).1).

move => a_hat clo_hat.
by move: (H a_hat (Addr_hat_til a_hat) (prec_Addr_bij.1 a_hat).1
            clo_hat (Clo_hat_til clo_hat) (prec_Clo_bij.1 clo_hat).1).

Qed.

(****)

Lemma trans_prec_Store_til {σ_hat σ_til σ'_til}:
  prec_Store σ_hat σ_til ->
  σ'_til ⊑ σ_til ->
  prec_Store σ_hat σ'_til.
Proof.
rewrite /prec_Store /substore /subseteq.
move => H1 H2 a_hat a_til H_a_hat clo_hat clo_til.
move: (H1 a_hat a_til H_a_hat clo_hat clo_til).
by auto.
Qed.

(****)

Lemma substore_A_til_hat {clo_hat clo_til σ_hat σ_til ae ρ_til}:
  prec_Clo clo_hat clo_til ->
  prec_Store σ_hat σ_til ->
  A_til ae ρ_til σ_til clo_til ->
  A_hat ae (Env_til_hat ρ_til) σ_hat clo_hat.
Proof.
move => H_prec_Clo H_prec_Store.
rewrite -(Store_bij.2 σ_hat).
rewrite -(A_til_hat).
rewrite /D_til_hat.
rewrite ((prec_Clo_bij.1 clo_hat).2 clo_til H_prec_Clo).
apply substore_A_til.
by apply substore_prec_Store.
Qed.

(****)

Lemma substore_σ_extend {Addr : Set} {A : Set} {eq_Addr σ0 σ1} {a : Addr} {s s' : set A}:
  s ⊆ s' ->
  σ_extend eq_Addr σ0 a s ⊑ σ_extend eq_Addr σ1 a s'.
Proof.
move => H a' v.
rewrite /σ_extend.
case E: (eq_Addr a a'); try auto.
Qed.

(****)

Lemma substore_σ_extend_til_hat {σ_hat σ_til σ_κ_til e ρ_til a_κ_til κs_til a_hat clo_hat a_til clo_til x' ae}:
  prec_Store σ_hat σ_til ->
  stacks σ_κ_til a_κ_til κs_til ->
  prec_Addr a_hat a_til ->
  prec_Clo clo_hat clo_til ->
  σ_extend eq_Addr_til σ_til
     (alloc_til x' (e, ρ_til, a_κ_til, (σ_til, σ_κ_til)))
     (A_til ae ρ_til σ_til) a_til clo_til ->
  σ_extend eq_Addr_hat σ_hat
     (alloc_hat x' (e, Env_til_hat ρ_til, Konts_til_hat κs_til, σ_hat))
     (A_hat ae (Env_til_hat ρ_til) σ_hat) a_hat clo_hat.
Proof.
move => H_Store H_stacks H_Addr H_Clo.
rewrite /σ_extend /eq_Addr_til /eq_Addr_hat.

case E: (eq_bool _ _ _); try done.
case F: (eq_bool _ _ _); try done.
by apply substore_A_til_hat.
move: (eq_bool_correct_false.1 F).
rewrite (prec_alloc x' (e, Env_til_hat ρ_til, Konts_til_hat κs_til, σ_hat)
                       (e, ρ_til, a_κ_til, (σ_til, σ_κ_til))); try done.
rewrite (eq_bool_correct_true.1 E).
by auto.
exists κs_til.
split; try done.
Qed.

(********************************)
(**** Paths and their lemmas ****)
(********************************)

Inductive path_hat ξ_hat c_hat : C_hat -> Prop :=
| path_hat_null : ξ_hat.1 c_hat -> path_hat ξ_hat c_hat c_hat
| path_hat_cons : forall c_mid_hat, ∀c'_hat ∈ ξ_hat.1,
    (path_hat ξ_hat c_hat c_mid_hat ->
    step_Σ_sub_hat (c_mid_hat, ξ_hat.2) (c'_hat, ξ_hat.2) ->
    path_hat ξ_hat c_hat c'_hat).

Inductive path_til ξ_til ξ'_til c_til κs_til : C_til -> list Kont_til -> Prop :=
| path_til_nil : ξ'_til.1 c_til ->
                 stacks ξ'_til.2.2 c_til.2 κs_til ->
                 path_til ξ_til ξ'_til c_til κs_til c_til κs_til
| path_til_Let x f ae b ρ_mid_til a_κ_mid_til: ∀c'_til ∈ ξ'_til.1, forall κs'_til,
    let c_mid_til := (Let x f ae b, ρ_mid_til, a_κ_mid_til) in
    let κ_til := (x, b, ρ_mid_til, a_κ_mid_til) in
    path_til ξ_til ξ'_til c_til κs_til c_mid_til κs'_til ->
    ξ_til.1 c_mid_til ->
    ξ'_til.2.2 c'_til.2 κ_til ->
    step_Σ_sub_til (c_mid_til, ξ_til.2) (c'_til, ξ'_til.2) ->
    path_til ξ_til ξ'_til c_til κs_til c'_til (κ_til :: κs'_til)
| path_til_Ret ae ρ_mid_til a_κ_mid_til: forall κ'_til κs'_til,
    let c_mid_til := (Ret ae, ρ_mid_til, a_κ_mid_til) in
    let x := κ'_til.1.1.1 in
    let e' := κ'_til.1.1.2 in
    let ρ_κ_til := κ'_til.1.2 in
    let a'_κ_til := κ'_til.2 in
    let c'_til := (e', ρ_extend ρ_κ_til x (alloc_til x (c_mid_til, ξ_til.2)), a'_κ_til) in
    ξ'_til.1 c'_til ->
    path_til ξ_til ξ'_til c_til κs_til c_mid_til (κ'_til :: κs'_til) ->
    ξ_til.1 c_mid_til ->
    ξ_til.2.2 a_κ_mid_til κ'_til ->
    step_Σ_sub_til (c_mid_til, ξ_til.2) (c'_til, ξ'_til.2) ->
    path_til ξ_til ξ'_til c_til κs_til c'_til κs'_til.

Notation "x ⟶^ y [ e ; e2 ]" := (path_hat e e2 x y) (at level 70, no associativity).
Notation "x / y ⟶~ z / w [ e ; e2 ]" := (path_til e e2 x y z w) (at level 70, no associativity).

Lemma path_start_hat {ξ_hat c_hat c'_hat}:
  path_hat ξ_hat c_hat c'_hat -> ξ_hat.1 c_hat.
Proof. by elim. Qed.

Lemma path_end_hat {ξ_hat c_hat c'_hat}:
  path_hat ξ_hat c_hat c'_hat -> ξ_hat.1 c'_hat.
Proof. by elim. Qed.

Lemma path_start_til {ξ_til ξ'_til c_til κs_til c'_til κs'_til}:
  path_til ξ_til ξ'_til c_til κs_til c'_til κs'_til -> ξ'_til.1 c_til.
Proof. by elim. Qed.

Lemma path_end_til {ξ_til ξ'_til c_til κs_til c'_til κs'_til}:
  path_til ξ_til ξ'_til c_til κs_til c'_til κs'_til -> ξ'_til.1 c'_til.
Proof. by elim. Qed.

Fixpoint κs_last_addr a_κ_til (κs_til : list Kont_til) := match κs_til with
| nil => a_κ_til
| cons (_, a_κ_til) κs_til => κs_last_addr a_κ_til κs_til
end.

Lemma path_append_til {ξ_til ξ'_til c_0_til κs0_til c_1_til κs1_til c_2_til κs2_til}:
  path_til ξ_til ξ'_til c_0_til κs0_til c_1_til κs1_til ->
  path_til ξ_til ξ'_til c_1_til κs1_til c_2_til κs2_til ->
  path_til ξ_til ξ'_til c_0_til κs0_til c_2_til κs2_til.
Proof.
move => H_path_1 H_path_2.
elim E: H_path_2 => [|x f ae b|].
by [].
move => H1 H2 H3 H4.
apply (path_til_Let _ _ _ _ x f ae b); try done.
move => //= H1 H2 H3 H4 H5.
apply (path_til_Ret); try done.
Qed.


(***********************)
(*** Well-formedness ***)
(***********************)

Inductive Ξ_til_wf {ξ_til ξ'_til} : Prop := mk_Ξ_til_wf {
  Ξ_til_wf_ξ: ξ_til = ξ_0_til /\ ξ'_til = ξ_0_til \/
              (exists ξ_pre_til, @Ξ_til_wf ξ_pre_til ξ_til) /\ step_Ξ_til ξ_til = ξ'_til;
  Ξ_til_wf_r_sub: ξ_til.1 ⊆ ξ'_til.1;
  Ξ_til_wf_σ_sub: ξ_til.2.1 ⊑ ξ'_til.2.1;
  Ξ_til_wf_σ_κ_sub: ξ_til.2.2 ⊑ ξ'_til.2.2;
  Ξ_til_wf_c_0: ξ'_til.1 c_0_til;
  Ξ_til_wf_a_κ_0 κ_til: ~ξ'_til.2.2 a_κ_0_til κ_til;
  Ξ_til_wf_r:
    ∀c_til ∈ ξ'_til.1,
    ∃κs_til ∈ stacks ξ'_til.2.2 c_til.2,
      path_til ξ_til ξ'_til c_0_til nil c_til κs_til;
  Ξ_til_wf_σ:
    ∀a_til ↦ clo_til ∈ ξ'_til.2.1,
      ∃c_til ∈ ξ_til.1,
      ∃c'_til ∈ ξ'_til.1,
        step_Σ_sub_clo_til a_til clo_til (c_til, ξ_til.2) (c'_til, ξ'_til.2);
  Ξ_til_wf_σ_κ:
    ∀a_κ_til ↦ κ_til ∈ ξ'_til.2.2,
      (ξ'_til.1 (C_Addr_til a_κ_til) /\
       exists f ae,
         let c_call_til := (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2) in
         ξ_til.1 c_call_til /\
         step_Σ_sub_κ_til a_κ_til κ_til (c_call_til, ξ_til.2) (C_Addr_til a_κ_til, ξ'_til.2))
}.

(****)

Lemma Ξ_til_wf_a_κ_0' {ξ_til ξ'_til a_κ_til κ_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  ξ'_til.2.2 a_κ_til κ_til ->
  a_κ_til <> a_κ_0_til.
Proof.
move => H_wf H_κ_til H_a_κ_til.
rewrite H_a_κ_til in H_κ_til.
by move: (Ξ_til_wf_a_κ_0 H_wf κ_til).
Qed.

(****)

Lemma Ξ_til_wf_C_Addr {ξ_til ξ'_til c_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  ξ'_til.1 c_til ->
  ξ'_til.1 (C_Addr_til c_til.2).
Proof.
move => H_wf H_c_til.
move: (Ξ_til_wf_r H_wf _ H_c_til) => [? [H_stacks H_path]].
inversion H_stacks.
rewrite H C_Addr_til_0.
by move: (Ξ_til_wf_c_0 H_wf).
by move: (Ξ_til_wf_σ_κ H_wf _ _ H1).1.
Qed.

(*******************************)
(**** Allocator consistency ****)
(*******************************)
Parameter alloc_til_ordering: forall {ξ_til ξ'_til x c_til c'_til σ'_til σ'_κ_til x},
  @Ξ_til_wf ξ_til ξ'_til ->
  step_Σ_til (c_til, ξ'_til.2) (c'_til, (σ'_til, σ'_κ_til)) ->
  ξ'_til.1 c_til ->
  c'_til.1.2 x = alloc_til x (c_til, ξ'_til.2) ->
  alloc_til x (c_til, ξ'_til.2) =
  alloc_til x (c_til, (step_Ξ_til ξ'_til).2).

Lemma alloc_til_ordering' {ξ_til ξ'_til c_til c'_til σ'_til σ'_κ_til x}:
  @Ξ_til_wf ξ_til ξ'_til ->
  step_Σ_til (c_til, ξ_til.2) (c'_til, (σ'_til, σ'_κ_til)) ->
  ξ_til.1 c_til ->
  c'_til.1.2 x = alloc_til x (c_til, ξ_til.2) ->
  alloc_til x (c_til, ξ_til.2) =
  alloc_til x (c_til, ξ'_til.2).
Proof.
move => H_wf H_step H_c_til H_eq.
case E: (Ξ_til_wf_ξ H_wf) => [H|[[ξ_pre_til H1] H2]].
by rewrite H.1 H.2.
rewrite -H2.
apply (alloc_til_ordering H1 H_step H_c_til H_eq (x:=x)).
Qed.

Parameter alloc_κ_til_ordering: forall {ξ_til ξ'_til c_til e' ρ'_til a'_κ_til a_til ae ρ_til σ'_til σ'_κ_til},
  @Ξ_til_wf ξ_til ξ'_til ->
  let old := alloc_κ_til (c_til, ξ'_til.2) e' ρ'_til
              (σ_extend eq_Addr_til ξ'_til.2.1 a_til (A_til ae ρ_til ξ'_til.2.1)) in
  let new := alloc_κ_til (c_til, (step_Ξ_til ξ'_til).2) e' ρ'_til
              (σ_extend eq_Addr_til (step_Ξ_til ξ'_til).2.1 a_til (A_til ae ρ_til (step_Ξ_til ξ'_til).2.1)) in
  step_Σ_til (c_til, ξ'_til.2) ((e', ρ'_til, a'_κ_til), (σ'_til, σ'_κ_til)) ->
  ξ'_til.1 c_til ->
  a'_κ_til = old ->
  old = new.

Lemma alloc_κ_til_ordering' {ξ_til ξ'_til c_til e' ρ'_til a'_κ_til a_til ae ρ_til σ'_til σ'_κ_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  let old := alloc_κ_til (c_til, ξ_til.2) e' ρ'_til
              (σ_extend eq_Addr_til ξ_til.2.1 a_til (A_til ae ρ_til ξ_til.2.1)) in
  let new := alloc_κ_til (c_til, ξ'_til.2) e' ρ'_til
              (σ_extend eq_Addr_til ξ'_til.2.1 a_til (A_til ae ρ_til ξ'_til.2.1)) in
  step_Σ_til (c_til, ξ_til.2) ((e', ρ'_til, a'_κ_til), (σ'_til, σ'_κ_til)) ->
  ξ_til.1 c_til ->
  a'_κ_til = old ->
  old = new.
Proof.
move => H_wf old new H_step H_c_til H_eq.

case E: (Ξ_til_wf_ξ H_wf) => [H|[[ξ_pre_til H1] H2]].

by rewrite /old /new H.1 H.2.

rewrite /old /new.
rewrite -H2.
by apply (alloc_κ_til_ordering H1 H_step H_c_til).
Qed.


(************************************)
(*** step_Ξ_til is monotonic for  ***)
(*** r, σ, σ_κ, stacks, and paths ***)
(************************************)

Lemma step_r_til {ξ_til ξ'_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.1 ⊆ (step_Ξ_til ξ'_til).1.
Proof.
move => c_til H_c_til.
move: (Ξ_til_wf_r H_wf c_til H_c_til) => [κs_til [H_stacks H_paths]].
inversion H_paths.

(*+ nil +*)
rewrite /step_Ξ_til; pairs.
exists σ_0_til σ_κ_0_til.
by left.

(*+ Let +*)
rewrite /step_Ξ_til; pairs.
move: H3 => [σ'_til [σ'_κ_til]] //= [H_σ'_til [H_σ'_κ_til H_step]].
inversion H_step.
set ϛ'_til := step_Σ_til_Let_func x f ae b ρ_mid_til a_κ_mid_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til.
exists ϛ'_til.2.1 ϛ'_til.2.2.
right.
exists c_mid_til.
split.
by move: (path_end_til H0).

(* have: A_til f ... *)
move: (substore_A_til f ρ_mid_til (Ξ_til_wf_σ_sub H_wf) (x', e', ρ_λ_til)).
rewrite -H12 //= H12 => HH.
move: {HH} (HH H6) => H_A_til.

(* have: step_Σ_til ... *)
rewrite /c_mid_til.

move: (step_Σ_til_Let x f ae b ρ_mid_til a_κ_mid_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til H_A_til).
rewrite /ϛ'_til /step_Σ_til_Let_func /c_mid_til; pairs.
rewrite H12 in H15.
rewrite -/c_mid_til.

rewrite -H13 in H_step.
rewrite -{3}H12.
have: σ_til = ξ_til.2.1 by rewrite -H12.
move => {3}->.
rewrite (alloc_κ_til_ordering' H_wf H_step); try done.

rewrite H12.
rewrite (alloc_til_ordering' H_wf H_step); try done.

move => //=.
by rewrite /ρ_extend /eq_Var (eq_bool_correct.1.2); try done; rewrite -H12.
rewrite H12.
have: σ_til = ξ_til.2.1 by rewrite -H12.
move => ->.
done.

(*+ Ret +*)
rewrite /step_Ξ_til; pairs.
set ϛ'_til := step_Σ_til_Ret_func ae ρ_mid_til a_κ_mid_til ξ'_til.2.1 ξ'_til.2.2 x e' ρ_κ_til a'_κ_til.
exists ϛ'_til.2.1 ϛ'_til.2.2.
right.
exists c_mid_til.
split.
by move: (path_end_til H0).

have: ξ'_til.2.2 a_κ_mid_til (x, e', ρ_κ_til, a'_κ_til).
rewrite /x /e' /ρ_κ_til /a'_κ_til; pairs.
by move: (Ξ_til_wf_σ_κ_sub H_wf a_κ_mid_til κ'_til H2).
move => H_κ_til.

move: (step_Σ_til_Ret ae ρ_mid_til a_κ_mid_til ξ'_til.2.1 ξ'_til.2.2 x e' ρ_κ_til a'_κ_til H_κ_til).
rewrite /ϛ'_til /step_Σ_til_Ret_func /c'_til /c_mid_til ; pairs.
suff: (alloc_til x (Ret ae, ρ_mid_til, a_κ_mid_til, ξ_til.2)) =
      (alloc_til x (Ret ae, ρ_mid_til, a_κ_mid_til, ξ'_til.2)) by move ->.
move: H3 => [σ_til [σ_κ_til [H_σ_til [H_σ_κ_til X]]]].
rewrite //= in X.
apply (alloc_til_ordering' H_wf X); try done.
by rewrite /c'_til //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
Qed.

(****)

Lemma step_σ_til {ξ_til ξ'_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.2.1 ⊑ (step_Ξ_til ξ'_til).2.1.
Proof.
move => a_til clo_til H_clo_til.
rewrite /step_Ξ_til; pairs.

move: (Ξ_til_wf_σ H_wf a_til clo_til H_clo_til) =>
      [c_til [H_c_til [c'_til [H_c'_til]]]]
      [σ'_til [σ'_κ_til]] //=
      [H_σ'_til [H_σ'_κ_til [H_clo_til' H_step]]].

inversion H_step.

(*+ Let +*)
set ϛ'_til := step_Σ_til_Let_func x f ae b ρ_til a_κ_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til.
exists ϛ'_til.
split.
right.
exists c_til.
split.

(*+= membership =+*)
by move: (Ξ_til_wf_r_sub H_wf c_til H_c_til).

(*+= step =+*)
move: (substore_A_til f ρ_til (Ξ_til_wf_σ_sub H_wf) (x', e', ρ_λ_til)).
rewrite -H1 //= => HH.
move: {HH} (HH H0) => H_A_til.

move: (step_Σ_til_Let x f ae b ρ_til a_κ_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til H_A_til).
by rewrite /ϛ'_til -H /step_Σ_til_Let_func //=; pairs.

(*+= membership =+*)
move: H_clo_til'.
rewrite -H3 //= /ϛ'_til //=.
rewrite H1; pairs; rewrite H -(alloc_til_ordering' H_wf H_step); try done.
move: (substore_A_til ae ρ_til (Ξ_til_wf_σ_sub H_wf)) => HH.
rewrite -H1 //= in HH.
by apply (substore_σ_extend HH a_til clo_til).

rewrite -H2 //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite -H -H1.

(*+ Ret +*)
set ϛ'_til := step_Σ_til_Ret_func ae ρ_til a_κ_til ξ'_til.2.1 ξ'_til.2.2 x e' ρ_κ_til a'_κ_til.
exists ϛ'_til.
split.
right.
exists c_til.
split.

(*+= membership =+*)
by move: (Ξ_til_wf_r_sub H_wf c_til H_c_til).

(*+= step =+*)
move: (Ξ_til_wf_σ_κ_sub H_wf a_κ_til (x, e', ρ_κ_til, a'_κ_til)).
rewrite -H1 //= => HH.
move: (step_Σ_til_Ret ae ρ_til a_κ_til ξ'_til.2.1 ξ'_til.2.2 x e' ρ_κ_til a'_κ_til (HH H0)).
by rewrite /ϛ'_til -H /step_Σ_til_Ret_func; pairs.

(*+= membership =+*)
move: H_clo_til'.
rewrite -H3 /ϛ'_til /step_Σ_til_Ret_func //=.

rewrite H1; pairs; rewrite H -(alloc_til_ordering' H_wf H_step); try done.
move: (substore_A_til ae ρ_til (Ξ_til_wf_σ_sub H_wf)) => HH.
rewrite -H1 //= in HH.
by apply (substore_σ_extend HH a_til clo_til).

rewrite -H2 //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite -H -H1.
Qed.

(****)

Lemma step_σ_κ_til {ξ_til ξ'_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.2.2 ⊑ (step_Ξ_til ξ'_til).2.2.
Proof.
move => a_κ_til κ_til H_κ_til.
rewrite /step_Ξ_til; pairs.

move: (Ξ_til_wf_σ_κ H_wf a_κ_til κ_til H_κ_til).2 => [f [ae [H_c_call_til]]].
move => [σ'_til [σ'_κ_til]] //=
        [H_σ'_til [H_σ'_κ_til [H_κ_til' H_step]]].
inversion H_step.
exists (step_Σ_til_Let_func κ_til.1.1.1 f ae κ_til.1.1.2 κ_til.1.2 κ_til.2 ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til).

(*+*)split.

(*+ step +*)
right.
exists (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2).
split.

by move: (Ξ_til_wf_r_sub H_wf (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2) H_c_call_til).

move: (substore_A_til f κ_til.1.2 (Ξ_til_wf_σ_sub H_wf) (x', e', ρ_λ_til)).
rewrite -H6 //= => HH.
move: {HH} (HH H0) => H_A_til.

move: (step_Σ_til_Let κ_til.1.1.1 f ae κ_til.1.1.2 κ_til.1.2 κ_til.2 ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til H_A_til).
by pairs.

(*+ membership +*)
rewrite /step_Σ_til_Let_func //=.
do [pairs] in H9 *.
rewrite -(alloc_til_ordering' H_wf H_step); try done.
rewrite -H7 in H_step.
rewrite -{1}H6.
rewrite -(alloc_κ_til_ordering' H_wf H_step); try done.
rewrite (σ_extend_ind eq_KAddr_til ξ'_til.2.2 σ_κ_til).
by rewrite -H6 //= H9.

by rewrite -H6.

rewrite -H7 //= /ρ_extend /eq_Var (eq_bool_correct.1.2); try done.
by rewrite -H6.
Qed.

(****)

Lemma step_til {ξ_til ξ'_til c_til c'_til σ'_til σ'_κ_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  step_Σ_til (c_til, ξ'_til.2) (c'_til, (σ'_til, σ'_κ_til)) ->
  ξ'_til.1 c_til ->
  (step_Ξ_til ξ'_til).1 c'_til /\
  σ'_til ⊑ (step_Ξ_til ξ'_til).2.1 /\ σ'_κ_til ⊑ (step_Ξ_til ξ'_til).2.2.
Proof.
move => H_step H_c_til.
rewrite /step_Ξ_til; pairs.

do ?split.

exists σ'_til σ'_κ_til.
right.
exists c_til.
split; try done.

move => a_til clo_til H_clo_til.
exists (c'_til, (σ'_til, σ'_κ_til)).
inversion H_step.

split.
right.
exists c_til.
split; try done.
by rewrite H4 H2 H3 H1.
by rewrite //= H3.

split.
right.
exists c_til.
split; try done.
by rewrite H4 H2 H3 H1.
by rewrite //= H3.

move => a_til clo_til H_clo_til.
exists (c'_til, (σ'_til, σ'_κ_til)).
inversion H_step.

split.
right.
exists c_til.
split; try done.
by rewrite H4 H2 H3 H1.
by rewrite //= H4.

split.
right.
exists c_til.
split; try done.
by rewrite H4 H2 H3 H1.
by rewrite H4 //=.
Qed.

(****)

Lemma step_stacks {ξ_til ξ'_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  stacks ξ'_til.2.2 ⊑ stacks (step_Ξ_til ξ'_til).2.2.
Proof.
move => a_κ_til κ_til H_stacks.
induction H_stacks.

(*+ null +*)
by constructor.

(*+ cons +*)
constructor; try done.
by move: (step_σ_κ_til H_wf a_κ_til κ_til H0).
Qed.

(****)

Lemma Ξ_til_wf_stacks_step {ξ_til ξ'_til} (H_wf: @Ξ_til_wf ξ_til ξ'_til):
  stacks ξ_til.2.2 ⊑ stacks ξ'_til.2.2.
Proof.

case: (Ξ_til_wf_ξ H_wf).
move => H.
by rewrite H.1 H.2 /substore /subseteq.

move => [[ξ_pre_til H_wf'] H_step].
rewrite -H_step.
by move: (step_stacks H_wf').
Qed.

(****)

Lemma step_path_til {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til) c_til κs_til:
  path_til ξ_til ξ'_til c_til κs_til ⊑ path_til ξ'_til (step_Ξ_til ξ'_til) c_til κs_til.
Proof.
move => c'_til κs'_til.
elim => [
  H_c_til H_stacks |
  x f ae b ρ_pre_til a_κ_pre_til c_pre_til H_c_pre_til κs_pre_til c_mid_til φ'_til
    IH_no_step IH_step H_c_mid_til H_φ'_til H_step |
  ae ρ_pre_til a_κ_pre_til κ'_til κs'_pre_til c_mid_til
     x e' ρ_κ_til a'_κ_til c_pre_til
     H_c_pre_til IH_no_step IH_step H_c_mid_til H_κ_til H_step
].
(*= nil =*)
constructor.
by apply: (step_r_til H_wf).
by apply: (step_stacks H_wf).

(*= Let =*)
apply (path_til_Let ξ'_til (step_Ξ_til ξ'_til) c_til κs_til x f ae b ρ_pre_til a_κ_pre_til c_pre_til).
by apply (step_r_til H_wf).
by [].
case: (Ξ_til_wf_ξ H_wf).
move => H.
by rewrite H.2 /ξ_0_til //= in H_φ'_til.
move => [[ξ_pre_til H_wf'] H_step'].
rewrite -H_step'.
move: H_c_mid_til.
by apply (step_r_til H_wf' (Let x f ae b, ρ_pre_til, a_κ_pre_til)).
by apply (step_σ_κ_til H_wf).
move: H_step => [σ'_til [σ'_κ_til]] //=
                [H_σ'_til [H_σ'_κ_til H_step]].
inversion H_step.
(*rewrite {H x0 H1 f0 H2 ae0 H3 b0 H4 ρ_til H5 a_κ_til} (H9).*)
set σ''_til := σ_extend eq_Addr_til σ_til
         (alloc_til x'
            (Let x f ae b, ρ_pre_til, a_κ_pre_til, (σ_til, σ_κ_til)))
         (A_til ae ρ_pre_til ξ'_til.2.1).
exists σ''_til σ'_κ_til.
do ?split.
rewrite //= /step_Ξ_til; pairs; rewrite /substore /subseteq.
move => a_til clo_til H_clo_til.
exists (c_pre_til, (σ_extend eq_Addr_til ξ'_til.2.1 (alloc_til x' (c_mid_til, ξ'_til.2))
           (A_til ae ρ_pre_til ξ'_til.2.1),
        σ_extend eq_KAddr_til ξ'_til.2.2
          (alloc_κ_til (c_mid_til, ξ'_til.2) e'
             (ρ_extend ρ_λ_til x' (alloc_til x' (c_mid_til, ξ'_til.2)))
             (σ_extend eq_Addr_til ξ'_til.2.1
                (alloc_til x' (c_mid_til, ξ'_til.2))
                (A_til ae ρ_pre_til ξ'_til.2.1)))
          (eq^~ (x, b, ρ_pre_til, a_κ_pre_til)))).
split.
right.
exists c_mid_til.
split.
by move: (Ξ_til_wf_r_sub H_wf _ H_c_mid_til).
move: (step_Σ_til_Let x f ae b ρ_pre_til a_κ_pre_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til).
rewrite /step_Σ_til_Let_func //= -/c_mid_til; pairs.
rewrite -H7.
rewrite -/c_mid_til.
rewrite H6.

have: σ_til = ξ_til.2.1 by rewrite -H6.
move => ->.

rewrite (surjective_pairing c_pre_til) (surjective_pairing c_pre_til.1) -H7 //= in H_step.
rewrite {13}/c_mid_til.
rewrite -{3}H6.
rewrite (alloc_κ_til_ordering' H_wf H_step).

rewrite H6.

suff: alloc_til x' (c_mid_til, ξ_til.2) = alloc_til x' (c_mid_til, ξ'_til.2).
move => ->.
apply.

have: σ_til = ξ_til.2.1 by rewrite -H6.
move => HH.

rewrite HH in H0.
by apply: (substore_A_til f ρ_pre_til (Ξ_til_wf_σ_sub H_wf) (x', e', ρ_λ_til)).

apply: (alloc_til_ordering' H_wf H_step); try done.

rewrite //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite H6.

by [].

by rewrite -H6 -/c_mid_til //=.

rewrite //=.

rewrite -(alloc_til_ordering' H_wf H_step).
rewrite -H6.

by rewrite /σ''_til /σ_extend //= in H_clo_til.

by [].

rewrite -H7 //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite -H6.

rewrite //=.

by move: (store_trans H_σ'_κ_til (step_σ_κ_til H_wf)).

move: (substore_A_til f ρ_pre_til (Ξ_til_wf_σ_sub H_wf) (x', e', ρ_λ_til)).
rewrite -H6 //= H6 => HH.
move: {HH} (HH H0) => H_A_til.
move: (step_Σ_til_Let x f ae b ρ_pre_til a_κ_pre_til ξ'_til.2.1 ξ'_til.2.2 x' e' ρ_λ_til H_A_til).
rewrite /step_Σ_til_Let_func /σ''_til -H9 -/c_mid_til; pairs.
rewrite -(alloc_til_ordering' H_wf H_step); try done.
rewrite (σ_extend_ind eq_KAddr_til ξ'_til.2.2 σ_κ_til).
rewrite (σ_extend_ind eq_Addr_til ξ'_til.2.1 σ_til).
rewrite -H7 -/c_mid_til in H_step.
rewrite -{2}H6.
have: σ_til = ξ_til.2.1 by rewrite -H6.
move => {2}->.
rewrite -(alloc_κ_til_ordering' H_wf H_step); try done.
rewrite -H6 //=.
rewrite -(alloc_κ_til_ordering' H_wf H_step); try done.
by rewrite -H6 //=.
by rewrite -H6 //=.
by rewrite -H6 //=.

rewrite -H7 //= /ρ_extend /eq_Var (eq_bool_correct.1.2); try done.
by rewrite /c_mid_til -H6.

(*= Ret =*)
move: H_step => [σ_til] [σ'_til] [H_σ_til] [H_σ'_til] //= H_step.
rewrite /c_pre_til /c_mid_til.
rewrite (alloc_til_ordering' H_wf H_step); try done.
(*        (alloc_til_ordering ξ'_til.2.1 ξ'_til.2.2 (step_Ξ_til ξ'_til).2.1 (step_Ξ_til ξ'_til).2.2); pairs; try done.*)
apply: path_til_Ret.
rewrite -/x -/e' -/ρ_κ_til -/a'_κ_til.
rewrite -(alloc_til_ordering' H_wf H_step); try done.
by move: (step_r_til H_wf c_pre_til H_c_pre_til).
by rewrite /c_pre_til //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by [].
by apply (Ξ_til_wf_r_sub H_wf).
by apply (Ξ_til_wf_σ_κ_sub H_wf).
rewrite /step_Σ_sub_til.
exists  (σ_extend eq_Addr_til ξ'_til.2.1
           (alloc_til κ'_til.1.1.1
              (Ret ae, ρ_pre_til, a_κ_pre_til, (ξ'_til.2.1, ξ'_til.2.2)))
           (A_til ae ρ_pre_til ξ'_til.2.1))
        (fun (_ : KAddr_til) (_ : Kont_til) => False).
do ?split.
rewrite //=.
rewrite /substore /subseteq /step_Ξ_til //=; pairs.
move => a_til clo_til HH.
exists (κ'_til.1.1.2,
        ρ_extend κ'_til.1.2 κ'_til.1.1.1
          (alloc_til κ'_til.1.1.1 (Ret ae, ρ_pre_til, a_κ_pre_til, ξ'_til.2)),
        κ'_til.2,
        (σ_extend eq_Addr_til ξ'_til.2.1
           (alloc_til κ'_til.1.1.1 (Ret ae, ρ_pre_til, a_κ_pre_til, ξ'_til.2))
           (A_til ae ρ_pre_til ξ'_til.2.1),
        fun (_ : KAddr_til) (_ : Kont_til) => False)).
split.
right.
exists c_mid_til.
split.
by move: (Ξ_til_wf_r_sub H_wf _ H_c_mid_til).
move: (step_Σ_til_Ret ae ρ_pre_til a_κ_pre_til ξ'_til.2.1 ξ'_til.2.2 κ'_til.1.1.1 κ'_til.1.1.2 κ'_til.1.2 κ'_til.2).
rewrite /step_Σ_til_Ret_func; pairs.
apply.
by move: (Ξ_til_wf_σ_κ_sub H_wf _ _ H_κ_til).
by rewrite //=.
by rewrite //= /substore /subseteq.
rewrite //=.
rewrite -/x -/e' -/ρ_κ_til -/a'_κ_til -/c_mid_til.
suff: (alloc_til x (c_mid_til, ξ'_til.2)) = (alloc_til x (c_mid_til, ξ_til.2)).
move => ->.
rewrite -/c_pre_til.
rewrite (surjective_pairing ξ'_til.2).
move: (step_Σ_til_Ret ae ρ_pre_til a_κ_pre_til ξ'_til.2.1 ξ'_til.2.2 κ'_til.1.1.1 κ'_til.1.1.2 κ'_til.1.2 κ'_til.2).
rewrite /step_Σ_til_Ret_func.
pairs.
rewrite -/c_mid_til.
rewrite -/x -/e' -/ρ_κ_til -/a'_κ_til -/c_mid_til.
suff: (alloc_til x (c_mid_til, ξ'_til.2)) = (alloc_til x (c_mid_til, ξ_til.2)).
move => ->.
rewrite -/c_pre_til.
apply.
by move: (Ξ_til_wf_σ_κ_sub H_wf _ _ H_κ_til).
rewrite (alloc_til_ordering' H_wf H_step); try done.
by rewrite /c_pre_til //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
rewrite (alloc_til_ordering' H_wf H_step); try done.
by rewrite /c_pre_til //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite /c_pre_til //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
Qed.


(***************************)
(***** Stacks vs paths *****)
(***************************)

Lemma paths_have_stacks {ξ_til ξ'_til c_til κs_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  path_til ξ_til ξ'_til c_0_til nil c_til κs_til ->
  stacks ξ'_til.2.2 c_til.2 κs_til.
Proof.
move => H_wf.
elim; try done.

(*+ Let +*)
move => *.
apply stacks_cons; try done.
apply: (Ξ_til_wf_a_κ_0' H_wf); try done.

(*+ Ret +*)
move => ? ? ? ? ? ? ? ? ? ? ? ? ? H_stacks ? ?.
by inversion H_stacks.
Qed.

(****)

Lemma path_from_entry {ξ_til ξ'_til c_til κs_til κs'_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  path_til ξ_til ξ'_til c_0_til nil c_til (κs'_til ++ κs_til) ->
  let a'_κ_til := κs_last_addr c_til.2 κs'_til in
  (∀κs''_til ∈ stacks ξ'_til.2.2 a'_κ_til,
     path_til ξ_til ξ'_til (C_Addr_til a'_κ_til) κs''_til c_til (κs'_til ++ κs''_til)).
Proof.
move => H_wf H.

(*+*) dependent induction H. (* HELP TODO: how to do in ssreflect ??? *)

(*+ path_til_nil +*)
move: x.
case E1: κs_til; case E2: κs'_til; try done.
rewrite C_Addr_til_0 //= in H H0 *.
move => _ κs''_til H_κs''_til.
by inversion H_κs''_til; try done; constructor.

(*+ path_til_Let +*)
rename x into E.
rename x0 into x.
rename c'_til into c_til.

(*+=*) case: κs'_til E.

(*+= κs'_til = nil =+*)
rewrite /κs_last_addr //=; pairs => E.
move: H3 => //= [σ'_til] [σ'_κ_til] [H_σ'_til] [H_σ'_κ_til] H3.
inversion H3.
rewrite ?H13 in H5 H12 H14 *.
do ?[rewrite H5|rewrite H12|rewrite H13|rewrite H14].
move => {H4 x0 H6 f0 H7 ae0 H8 b0 H9 ρ_til H10 a_κ_til}.

rewrite -[in C_Addr_til _]H12 //= C_Addr_til_inj H12.

by constructor; try done; move: H3; rewrite -H10 //=.

(*+= case: κs'_til = cons =+*)
move => κ'_til κs'_til [E1 E2].
rewrite -E1 {κ'_til E1}.
rewrite E2 {κs'_til0 E2} in H0 IHpath_til.

move => κs''_til H_κs''_til.
move: (IHpath_til κs_til κs'_til H_wf eq_refl κs''_til H_κs''_til) => IH.
rewrite /c_mid_til in H1 IH *.
by move: (path_til_Let ξ_til ξ'_til (C_Addr_til (κs_last_addr a_κ_mid_til κs'_til)) κs''_til x f ae b ρ_mid_til a_κ_mid_til c_til H (κs'_til ++ κs''_til) IH H1 H2 H3).

(*+ Case: path_til_Ret +*)
move => κs''_til H_κs''_til.
move: (IHpath_til κs_til (κ'_til :: κs'_til) H_wf eq_refl).
rewrite /c_mid_til //=; pairs.
move => Ha.
move: {Ha} (Ha κs''_til H_κs''_til) => IH.
rewrite /c_mid_til in H2.
do [pairs; rewrite -/a'_κ_til] in IH.
by move: (path_til_Ret ξ_til ξ'_til (C_Addr_til (κs_last_addr a'_κ_til κs'_til)) κs''_til ae ρ_mid_til a_κ_mid_til κ'_til (κs'_til ++ κs''_til) H IH H1 H2 H3).
Qed.

(****)

Lemma path_from_entry' {ξ_til ξ'_til c_til κs_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  path_til ξ_til ξ'_til c_0_til nil c_til κs_til ->
  (∀κs''_til ∈ stacks ξ'_til.2.2 c_til.2,
     path_til ξ_til ξ'_til (C_Addr_til c_til.2) κs''_til c_til κs''_til).
Proof.
move => H_wf H_path.

have: κs_til = [] ++ κs_til by [].
move => H. rewrite H {H} in H_path.

by move: (path_from_entry H_wf H_path).
Qed.

(****)

Lemma stacks_have_paths {ξ_til ξ'_til}:
  @Ξ_til_wf ξ_til ξ'_til ->
  ∀c_til ∈ ξ'_til.1,
  ∀κs_til ∈ stacks ξ'_til.2.2 c_til.2,
  path_til ξ_til ξ'_til c_0_til nil c_til κs_til.
Proof.
move => H_wf c_til H_c_til κs_til.

(*+*)elim: κs_til c_til H_c_til => [|κ_til κs_til IH] c'_til H_c'_til H_stacks.

(*+ null +*)
move: (Ξ_til_wf_r H_wf c'_til H_c'_til) => [κs_til [H_stacks' H_path]].

move: (stacks_null_Addr H_stacks) => H.
rewrite H {H} in H_stacks H_stacks'.

by rewrite (stacks_null_Konts H_stacks') in H_path.

(*+ cons +*)

(* Exists path to c'_til *)
move: (Ξ_til_wf_r H_wf c'_til H_c'_til) => [κs_exists_til [_ H_κs_exists_til]].

(* We have a non-popping path from entry *)
move: (path_from_entry' H_wf H_κs_exists_til) => H_non_popping_path.

(* We have a step from call to entry *)
have: exists f ae,
        let c_call_til := (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2) in
        ξ_til.1 c_call_til /\ step_Σ_sub_til (c_call_til, ξ_til.2) (C_Addr_til c'_til.2, ξ'_til.2).
move: (Ξ_til_wf_σ_κ H_wf c'_til.2 κ_til (stacks_cons_Kont H_stacks).2.2).2
  => [f [ae [H_c_call_til H_step]]].
exists f ae.
split; try done.

by move: (step_Σ_sub_κ_til_weakening H_step).
move => [f [ae [H_c_call_til H_step]]].
set c_call_til := (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2) in H_c_call_til H_step *.

(* We have a path from c_0 to call *)
have: stacks ξ'_til.2.2 c_call_til.2 κs_til.
by move: (stacks_cons_Kont H_stacks).2.1; rewrite /c_call_til //=.
move => H_stacks_call.
move: (IH c_call_til (Ξ_til_wf_r_sub H_wf _ H_c_call_til) H_stacks_call) => H_path_call.

(* We have a path from c_0 to entry *)
have: path_til ξ_til ξ'_til c_0_til nil (C_Addr_til c'_til.2) (κ_til :: κs_til).
rewrite (surjective_pairing κ_til) (surjective_pairing κ_til.1) (surjective_pairing κ_til.1.1).
apply (path_til_Let ξ_til ξ'_til c_0_til nil κ_til.1.1.1 f ae κ_til.1.1.2 κ_til.1.2 κ_til.2 (C_Addr_til c'_til.2)); try done.
by move: (Ξ_til_wf_C_Addr H_wf H_c'_til).
by inversion H_stacks; rewrite C_Addr_til_Addr; pairs.
rewrite -/c_call_til.
move => H_path_entry.

(* We have a path from c_0 to c_til *)
by move: (path_append_til H_path_entry (H_non_popping_path (κ_til :: κs_til) H_stacks)).
Qed.


(*************************************)
(**** From til paths to hat paths ****)
(*************************************)

Lemma fix_contains_c_0_hat {ξ_hat}:
  step_Ξ_hat ξ_hat = ξ_hat -> ξ_hat.1 c_0_hat.
Proof.
move => <-.
rewrite /step_Ξ_hat; pairs.
exists σ_0_hat.
by left.
Qed.

(****)

Lemma fix_contains_step {ξ_hat σ'_hat c_hat c'_hat}:
  step_Ξ_hat ξ_hat = ξ_hat ->
  step_Σ_hat (c_hat, ξ_hat.2) (c'_hat, σ'_hat) ->
  ξ_hat.1 c_hat ->
  ξ_hat.1 c'_hat /\ σ'_hat ⊑ ξ_hat.2.
Proof.
move => H_fix H_step H_σ_hat.
rewrite -H_fix /step_Ξ_hat; pairs.

(*+*)split.

(*+ c'_hat +*)
(*+=*)inversion H_step.

(*+= Let =+*)
set ϛ_hat := step_Σ_hat_Let_func x f ae b ρ_hat κ_hat ξ_hat.2 x' e' ρ_λ_hat.
exists ϛ_hat.2.
right.
exists c_hat.
split; try done.
move: (step_Σ_hat_Let x f ae b ρ_hat κ_hat ξ_hat.2 x' e' ρ_λ_hat H0).
by rewrite /ϛ_hat /step_Σ_hat_Let_func -H //= H.

(*+= Ret =+*)
set ϛ_hat := step_Σ_hat_Ret_func ae ρ_hat ξ_hat.2 x e' ρ_κ_hat κ'_hat.
exists ϛ_hat.2.
right.
exists c_hat.
split; try done.
move: (step_Σ_hat_Ret ae ρ_hat ξ_hat.2 x e' ρ_κ_hat κ'_hat).
by rewrite /ϛ_hat /step_Σ_hat_Ret_func -H0 //= H0.

(*+ substore +*)
exists (c'_hat, σ'_hat).
split; try done.
right.
exists c_hat.
split; try done.
Qed.

(****)

Lemma path_til_hat {ξ_hat ξ_til ξ'_til c_til κs_til}:
  step_Ξ_hat ξ_hat = ξ_hat ->
  @Ξ_til_wf ξ_til ξ'_til ->
  prec_Store ξ_hat.2 ξ'_til.2.1 ->
  path_til ξ_til ξ'_til c_0_til nil c_til κs_til ->
  path_hat ξ_hat c_0_hat (C_til_hat c_til κs_til).
Proof.
move => H_fix H_wf H_prec_Store p_til.
(*+*) elim: p_til => {c_til κs_til}
  [|x f ae b ρ_mid_til a_κ_mid_til c_til H_c_til κs_til c_mid_til φ'_til H_path_til IH H_c_mid_til H_κ_til H_step
   |ae ρ_mid_til a_κ_mid_til κ'_til κs_til c_mid_til x e' ρ_κ_til a'_κ_til c_til H_c_til H_path_til IH H_c_mid_til H_κ_til H_step].

(*+ nil +*)
rewrite -c_0_til_hat.
constructor.
by apply fix_contains_c_0_hat.

(*+ Let +*)
move: H_step => [σ'_sub_til [σ'_κ_sub_til]] //=
                [H_σ'_sub_til [H_σ'_κ_sub_til H]].

inversion H.
move => {H0 x0 H2 f0 H3 ae0 H4 b0 ρ_til H5 a_κ_til H6}.
rewrite H9 in H8 H10 *.
rewrite H8.

(* have: A_hat ... *)
(have: σ_til = ξ_til.2.1 by rewrite -H7) => H_σ_til.
rewrite H_σ_til in H1.
move: (substore_A_til_hat
         (prec_Clo_bij.2 (x', e', ρ_λ_til)).1
         (trans_prec_Store_til H_prec_Store (Ξ_til_wf_σ_sub H_wf)) H1) => H_A_hat.

(* have: step_Σ_hat ... *)
move: (step_Σ_hat_Let x f ae b (Env_til_hat ρ_mid_til) (Konts_til_hat κs_til) ξ_hat.2 x' e' (Env_til_hat ρ_λ_til) H_A_hat).
rewrite /step_Σ_hat_Let_func //= => H_step_hat.

have: (C_til_hat c_mid_til κs_til, ξ_hat.2)
   ⟶Σ<^ (C_til_hat c_til ((x, b, ρ_mid_til, a_κ_mid_til) :: κs_til), ξ_hat.2).
exists (σ_extend eq_Addr_hat ξ_hat.2
                 (alloc_hat x'
                            (Let x f ae b, Env_til_hat ρ_mid_til,
                             Konts_til_hat κs_til, ξ_hat.2))
                 (A_hat ae (Env_til_hat ρ_mid_til) ξ_hat.2)).
rewrite /substore /subseteq //=.

(*+=*) do ?split; try done.

(*+= substore +=*)
by move: (fix_contains_step H_fix H_step_hat (path_end_hat IH)).2.

(*+= step +=*)
rewrite /C_til_hat -H8 //= /compose //= /Frame_til_hat H7 //=.
rewrite (alloc_til_ordering' H_wf H); try done.
(*rewrite (alloc_til_ordering σ_sub_til σ_κ_sub_til ξ'_til.2.1 ξ'_til.2.2).*)
suff: ρ_extend (Env_til_hat ρ_λ_til) x'
                     (alloc_hat x'
                        (Let x f ae b, Env_til_hat ρ_mid_til,
                        Konts_til_hat κs_til, ξ_hat.2)) =
      Env_til_hat (ρ_extend ρ_λ_til x' (alloc_til x' (c_mid_til, ξ'_til.2))).
by move => <-.

apply: functional_extensionality => x''.
rewrite /Env_til_hat /ρ_extend /eq_Var.

case E: (eq_bool _ _ _); try done.
apply: prec_alloc; try done.
rewrite //=.
exists κs_til.
split; try done.
by move: (paths_have_stacks H_wf H_path_til).

rewrite -H8 //= /ρ_extend /eq_Var eq_bool_correct.1.2; try done.
by rewrite -H7.
(* END HAVE *)
move => H_sub_step.

move: (path_hat_cons ξ_hat
                        c_0_hat
                        (C_til_hat c_mid_til κs_til)
                        (C_til_hat c_til ((x, b, ρ_mid_til, c_mid_til.2) :: κs_til))).
rewrite /φ'_til /c_mid_til //=.
apply; try done.

move: H_sub_step => [?] [?] //= H_sub_step.
by move: (fix_contains_step H_fix H_sub_step (path_end_hat IH)).1.

(*+ Ret +*)
move: H_step => [σ'_sub_til [σ'_κ_sub_til]] //=
                [H_σ'_sub_til [H_σ'_κ_sub_til H]].

inversion H.
(*move => {H0 ae0 H2 ρ_til H3 a_κ_til H4 σ_til H5 σ_κ_til H6 e'0 H8 a'_κ_til0}.*)
rename x0 into x'.
rewrite -H9 {H9 σ'_κ_sub_til} in H_σ'_κ_sub_til H H1.

have: κ'_til = (x, e',  ρ_κ_til, a'_κ_til).
by rewrite /x /e' /ρ_κ_til /a'_κ_til; pairs.
move => H_κ'_til.

(* have: step_Σ_hat ... *)
move: (step_Σ_hat_Ret ae (Env_til_hat ρ_mid_til) ξ_hat.2 x e' (Env_til_hat ρ_κ_til) (Konts_til_hat κs_til)).
rewrite /step_Σ_hat_Ret_func //= => H_step_hat.

have: step_Σ_sub_hat (C_til_hat c_mid_til (κ'_til :: κs_til), ξ_hat.2)
     (C_til_hat c_til κs_til, ξ_hat.2).
exists (σ_extend eq_Addr_hat ξ_hat.2
                 (alloc_hat x
                            (Ret ae, Env_til_hat ρ_mid_til,
                             (x, e', Env_til_hat ρ_κ_til) :: Konts_til_hat κs_til,
                             ξ_hat.2)) (A_hat ae (Env_til_hat ρ_mid_til) ξ_hat.2)).
rewrite /substore /subseteq //=.

(*+=*) do ?split; try done.

(*+= substore +=*)
by apply (fix_contains_step H_fix H_step_hat (path_end_hat IH)).2.

(*+= step +=*)
rewrite /C_til_hat //=.
rewrite (alloc_til_ordering' H_wf H); try done.
suff: ρ_extend (Env_til_hat ρ_κ_til) x
                     (alloc_hat x
                        (Ret ae, Env_til_hat ρ_mid_til,
                        (x, e', Env_til_hat ρ_κ_til) :: Konts_til_hat κs_til,
                        ξ_hat.2)) =
      Env_til_hat (ρ_extend ρ_κ_til x (alloc_til x (c_mid_til, ξ'_til.2))).
by move => <-.

apply: functional_extensionality => x''.
rewrite /Env_til_hat /ρ_extend /eq_Var.

case E: (eq_bool _ _ _); try done.
apply: prec_alloc; try done.
rewrite //=.
exists (κ'_til :: κs_til).
split; try done.
by move: (paths_have_stacks H_wf H_path_til).
by rewrite /c_til //= /ρ_extend /eq_Var eq_bool_correct.1.2.
(* END HAVE *)
move => H_step_sub_hat.

apply: (path_hat_cons ξ_hat
                     c_0_hat
                     (C_til_hat c_mid_til (κ'_til :: κs_til))); try done.

move: H_step_sub_hat => [?] [?] //= H_sub_step.
by move: (fix_contains_step H_fix H_sub_step (path_end_hat IH)).1.
Qed.


(*************************************)
(********* Well formedness ***********)
(*************************************)

Lemma step_Ξ_til_wf_ξ {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  (ξ'_til = ξ_0_til /\ step_Ξ_til ξ'_til = ξ_0_til) \/
  (exists ξ_pre_til, @Ξ_til_wf ξ_pre_til ξ'_til) /\ step_Ξ_til ξ'_til = step_Ξ_til ξ'_til.
Proof.
right.
split.
by exists ξ_til.
done.
Qed.

(****)

Lemma step_Ξ_til_wf_r_sub {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.1 ⊆ (step_Ξ_til ξ'_til).1.
Proof.
apply: (step_r_til H_wf).
Qed.

(****)

Lemma step_Ξ_til_wf_σ_sub {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.2.1 ⊑ (step_Ξ_til ξ'_til).2.1.
Proof.
apply: (step_σ_til H_wf).
Qed.

(****)

Lemma step_Ξ_til_wf_σ_κ_sub {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  ξ'_til.2.2 ⊑ (step_Ξ_til ξ'_til).2.2.
Proof.
apply: (step_σ_κ_til H_wf).
Qed.

(****)

Lemma step_Ξ_til_wf_c_0 {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  (step_Ξ_til ξ'_til).1 c_0_til.
Proof.
rewrite /step_Ξ_til; pairs.
exists σ_0_til σ_κ_0_til.
by left.
Qed.

(****)

Lemma step_Ξ_til_wf_a_κ_0 {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  forall κ_til, ~(step_Ξ_til ξ'_til).2.2 a_κ_0_til κ_til.
Proof.
move => κ_til.
rewrite /not /step_Ξ_til; pairs.
move => [ϛ_til] [].

(*+*) case.

(*+ ϛ_0_til +*)
by move => ->; rewrite /ϛ_0_til //=.

(*+ not ϛ_0_til +*)
move => [c_til [_]] H_step.

(*+=*) case: H_step => [ x f ae b ρ_til σ_til σ_κ_til a_κ_til x' e' ρ_λ_til _
                       | ae ρ_til σ_til σ_κ_til a_κ_til x e' ρ_κ_til a'_κ_til _].

(*+= Let =+*)
rewrite /step_Σ_til_Let_func //= /σ_extend /eq_KAddr_til.
case E: (eq_bool _ _ _).
move: (eq_bool_correct_true.1 E).
by move/alloc_κ_0_til.
by [].

(*+= Ret =+*)
by rewrite /step_Σ_til_Ret_func //=.
Qed.

(****)

Lemma step_Ξ_til_wf_r {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
  ∀c_til ∈ (step_Ξ_til ξ'_til).1,
  ∃κs_til ∈ stacks (step_Ξ_til ξ'_til).2.2 c_til.2,
    path_til ξ'_til (step_Ξ_til ξ'_til) c_0_til nil c_til κs_til.
Proof.
rewrite {1}/step_Ξ_til; pairs.
move => c_til.
(*+*)move => [σ_til [σ_κ_til []]].

(*+ c_0_til +*)
case => -> _ _.
exists (nil (A:=Kont_til)).
split.
by apply: stacks_null.
constructor.
by apply: (step_Ξ_til_wf_c_0 H_wf).
by constructor.

(*+ not c_0_til +*)
move => [c_pre_til [H_c_pre_til H_step]].
move: (Ξ_til_wf_r H_wf c_pre_til H_c_pre_til) => [κs_til [H_stacks H_path]].

(*+=*) inversion H_step.

(*+= Let =+*)
exists ((x, b, ρ_til, a_κ_til) :: κs_til).

(*+=+*) split.

(*+=+= stacks =+=+*)

(*+=+=+*) apply: stacks_cons => //=.

by move: alloc_κ_0_til.

move: (step_stacks H_wf c_pre_til.2 κs_til H_stacks).
by rewrite -H //=.

rewrite /step_Ξ_til; pairs.
exists (c_til, (σ_til, σ_κ_til)).

(*+=+=+=*) split.

right.
by exists c_pre_til.

rewrite -H4 //= /σ_extend /eq_KAddr_til.
by rewrite (eq_bool_correct_true.2 _).

(*+=+= path =+=+*)
rewrite H2.
(*+=+=+*) apply: (path_til_Let ξ'_til (step_Ξ_til ξ'_til) _ _ _ f ae); rewrite //=.

rewrite /step_Ξ_til; pairs.
exists σ_til σ_κ_til.
right.
exists c_pre_til.
by split; try done.

apply (step_path_til H_wf); try done.
by rewrite H.

by rewrite H.
rewrite /step_Ξ_til -H2 //=; pairs.
exists (c_til, (σ_til, σ_κ_til)).
split.
right.
exists c_pre_til.
by split; try done.
rewrite //= -H4 /σ_extend /eq_KAddr_til.
by rewrite eq_bool_correct_true.2.

move: (step_σ_κ_til H_wf).
rewrite -H in H_step.
exists σ_til σ_κ_til.

rewrite -H in H_c_pre_til.
(*+=+=+=*) rewrite //=.
do ?split.

rewrite /substore /subseteq.
move => a_til clo_til.
rewrite -H3 /σ_extend /eq_Addr_til.
case E: (eq_bool _ _ _); try done.
move => H_A_til.
rewrite /step_Ξ_til; pairs.
exists (c_til, (σ_til, σ_κ_til)).
split.
right.
by exists (Let x f ae b, ρ_til, a_κ_til).

rewrite //=.
rewrite -H3 /σ_extend /eq_Addr_til eq_bool_correct.1.2.
by [].

by move: (eq_bool_correct.1.1 E).

rewrite /substore /subseteq.
move => a'_κ_til κ'_til.

rewrite -H4 /σ_extend /eq_KAddr_til.

case E: (eq_bool _ _ _); try done.
move => H_κ'_til.
rewrite /step_Ξ_til; pairs.
exists (c_til, (σ_til, σ_κ_til)).
split.
right.
by exists (Let x f ae b, ρ_til, a_κ_til).

rewrite //=.
rewrite -H4 /σ_extend /eq_KAddr_til eq_bool_correct.1.2.
by [].

by move: (eq_bool_correct.1.1 E).

by [].

(*+=+ Ret +=+*)
rewrite //=.

have: ξ'_til.2.2 a_κ_til (x, e', ρ_κ_til, a'_κ_til) by rewrite -H1 //=.
move => H_a_κ_til.

(* have: κs'_til and a path to call *)
move: (Ξ_til_wf_σ_κ H_wf a_κ_til (x, e', ρ_κ_til, a'_κ_til) H_a_κ_til).2 => //= [? [? [H_call _]]].
move: (Ξ_til_wf_r H_wf _ (Ξ_til_wf_r_sub H_wf _ H_call)) => //= [κs'_til] [H_κs'_til] H_call_path.

exists κs'_til. (* Use that κs'_til *)

(*+=+=*) split.

(*+=+= stacks =+=+*)
move: (step_stacks H_wf).
rewrite /substore /subseteq.
by auto.

(*+=+= path =+=+*)
(* have: stacks ((...) :: κs'_til) *)
move: (stacks_cons ξ'_til.2.2 a_κ_til (x, e', ρ_κ_til, a'_κ_til) κs'_til (Ξ_til_wf_a_κ_0' H_wf H_a_κ_til) H_κs'_til H_a_κ_til) => H_κs_til.

(* have a path to entry *)
move: (Ξ_til_wf_C_Addr H_wf (path_end_til H_path)) => HH.
rewrite -[a_κ_til]C_Addr_til_Addr in H_κs_til.
rewrite -H //= in HH.
move: {HH} (stacks_have_paths H_wf _ HH _ H_κs_til) => H_path_entry.

(* have a path from entry *)
rewrite C_Addr_til_Addr in H_κs_til.
rewrite -H in H_path.
move: (path_from_entry' H_wf H_path _ H_κs_til) => //= H_path_from_entry.

(* have a path to exit in ξ'_til and (step_Ξ_til ξ'_til) *)
move: (path_append_til H_path_entry H_path_from_entry) => H_path_exit.
move: (step_path_til H_wf c_0_til nil _ _ H_path_exit) => H_path_exit'.

(* have a path to return *)
move: (path_til_Ret ξ'_til (step_Ξ_til ξ'_til) c_0_til nil ae ρ_til a_κ_til (x, e', ρ_κ_til, a'_κ_til) κs'_til) => //=.

rewrite -H1.
apply.

by rewrite H2; apply (step_til H_wf H_step H_c_pre_til).1.
by [].
by rewrite H.
by pairs.

exists σ_til σ_κ_til.
rewrite //=.
do ?split.
by move: (step_til H_wf H_step H_c_pre_til).2.1.
by move: (step_til H_wf H_step H_c_pre_til).2.2.

rewrite H2.
pairs.
by rewrite H H1.
Qed.

Lemma step_Ξ_til_wf_σ {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
    ∀a_til ↦ clo_til ∈ (step_Ξ_til ξ'_til).2.1,
      ∃c_til ∈ ξ'_til.1,
      ∃c'_til ∈ (step_Ξ_til ξ'_til).1,
        step_Σ_sub_clo_til a_til clo_til (c_til, ξ'_til.2) (c'_til, (step_Ξ_til ξ'_til).2).
Proof.
move => a_til clo_til.
rewrite {1}/step_Ξ_til.
rewrite {1}(surjective_pairing ξ'_til) (surjective_pairing ξ'_til.2) //=.
pairs.
move => [ϛ'_til [H_step H_member]].

(*+*)case: H_step.

(*+ ϛ_0_til +*)
move => H.
rewrite H {H} in H_member *.
by rewrite /ϛ_0_til /σ_0_til //= in H_member.

(*+ not ϛ_0_til +*)
move => [c_til [H_c_til H_step]].

exists c_til.

(*+=*) split.
(*+= membership =+*)
move: (step_r_til H_wf c_til H_c_til).
by rewrite /step_Ξ_til; pairs.

(*+= step =+*)
exists ϛ'_til.1.

(*+=+*) split.

(*+=+ membership +=+*)
rewrite /step_Ξ_til; pairs.
exists ϛ'_til.2.1 ϛ'_til.2.2.
right.
exists c_til.
by pairs.

(*+=+ step +=+*)
(*exists ξ'_til.2.1 ξ'_til.2.2.*)
exists ϛ'_til.2.1 ϛ'_til.2.2.

rewrite //=.

do ?split.

rewrite (surjective_pairing ϛ'_til) (surjective_pairing ϛ'_til.2) in H_step.
by move: (step_til H_wf H_step H_c_til).2.1.

rewrite (surjective_pairing ϛ'_til) (surjective_pairing ϛ'_til.2) in H_step.
by move: (step_til H_wf H_step H_c_til).2.2.

by [].
by pairs.
Qed.

Lemma step_Ξ_til_wf_σ_κ {ξ_til ξ'_til} (H_wf : @Ξ_til_wf ξ_til ξ'_til):
    ∀a_κ_til ↦ κ_til ∈ (step_Ξ_til ξ'_til).2.2,
      ((step_Ξ_til ξ'_til).1 (C_Addr_til a_κ_til) /\
       exists f ae,
         let c_call_til := (Let κ_til.1.1.1 f ae κ_til.1.1.2, κ_til.1.2, κ_til.2) in
         ξ'_til.1 c_call_til /\
         step_Σ_sub_κ_til a_κ_til κ_til (c_call_til, ξ'_til.2) (C_Addr_til a_κ_til, (step_Ξ_til ξ'_til).2)).
Proof.
rewrite {1}/step_Ξ_til.
rewrite {1}(surjective_pairing ξ'_til) (surjective_pairing ξ'_til.2) //=.
pairs.

move => a_κ_til κ_til [ϛ_til [H H_κ_til]].

(*+*) case: H.

(*+ ϛ_0_til +*)
by move => H; rewrite H /ϛ_0_til //= in H_κ_til.

(*+ not ϛ_0_til +*)
move => [c_til [H_c_til H_step]].

inversion H_step; last first.
by rewrite -H0 /step_Σ_til_Ret_func //= in H_κ_til.

have: σ_til = ξ'_til.2.1 /\ σ_κ_til = ξ'_til.2.2.
by rewrite -H1 //=.
move => [H_σ_til H_σ_κ_til].

rewrite H_σ_til {H_σ_til σ_til} in H0 H1 H2 *.
rewrite H_σ_κ_til {H_σ_κ_til σ_κ_til} in H0 H1 H2 *.

(* know κ_til from ϛ_til *)
have: κ_til = (x, b, ρ_til, a_κ_til0).
rewrite -H0 /step_Σ_til_Let_func //= /σ_extend /eq_KAddr_til in H_κ_til.
by case: (eq_bool _ _ _) in H_κ_til; try done.
move => H_κ_til'.

(*+=*) split.

(*+= membership =+*)
rewrite /step_Ξ_til; pairs.
exists ϛ_til.2.1 ϛ_til.2.2.
right.
exists c_til.
split; try done.
pairs.
rewrite -H0 in H_κ_til.
move: (C_Addr_til_inj' H_κ_til) => ->.
by rewrite H0; pairs.

(*+= step =+*)
exists f ae.

(*+=+*) split.

(*+=+ membership +=+*)
by rewrite H_κ_til' //= H.

(*+=+ step +=+*)
rewrite H_κ_til' //=.

exists (*ξ'_til.2.1 ξ'_til.2.2*) ϛ_til.2.1 ϛ_til.2.2.
rewrite //= (surjective_pairing ϛ_til) (surjective_pairing ϛ_til.2) //= in H_step *.
do ?split.
(*by move: (step_σ_til H_wf); rewrite /step_Ξ_til //=; pairs.
by move: (step_σ_κ_til H_wf); rewrite /step_Ξ_til //=; pairs.*)
by move: (step_til H_wf H_step H_c_til).2.1.
by move: (step_til H_wf H_step H_c_til).2.2.
by rewrite -H_κ_til'.
rewrite -H0 in H_κ_til.
do [pairs] in H_step.
by rewrite (C_Addr_til_inj' H_κ_til) H0 H; pairs.
Qed.

(*** Initial ξ is Well-formed ***)

Lemma Ξ_til_wf_ξ_0: @Ξ_til_wf ξ_0_til ξ_0_til.
Proof.
split; try done; auto.

by rewrite /substore /subseteq.
by rewrite /substore /subseteq.

move => c_til ->.
rewrite /ξ_0_til //=.
exists (nil (A := Kont_til)).
split.
by constructor.
apply: path_til_nil; try done.
rewrite //=.
by constructor.
Qed.

(*Lemma Ξ_til_wf_ξ' {ξ_til ξ'_til}: @Ξ_til_wf ξ_til*)

(*** Stepping preserves well-formedness ***)

Lemma step_Ξ_til_wf {ξ_til ξ'_til}: @Ξ_til_wf ξ_til ξ'_til -> @Ξ_til_wf ξ'_til (step_Ξ_til ξ'_til).
Proof.
move => H_wf.
apply: mk_Ξ_til_wf.
by apply: (@step_Ξ_til_wf_ξ ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_r_sub ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_σ_sub ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_σ_κ_sub ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_c_0 ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_a_κ_0 ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_r ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_σ ξ_til ξ'_til).
by apply: (@step_Ξ_til_wf_σ_κ ξ_til ξ'_til).
Qed.

(*****************************************)
(*** Taking a step preserves precision ***)
(*****************************************)

Lemma step_prec_Store {ξ_hat ξ_til ξ'_til}:
  step_Ξ_hat ξ_hat = ξ_hat ->
  @Ξ_til_wf ξ_til ξ'_til ->
  prec_Ξ ξ_hat ξ'_til ->
  prec_Store ξ_hat.2 (step_Ξ_til ξ'_til).2.1.
Proof.
move => H_fix H_wf H_prec.
move => a_hat a_til H_prec_Addr clo_hat clo_til H_prec_Clo.
rewrite /step_Ξ_til; pairs.
move => [ϛ_til [H_step H_clo_til]].

(*+*) case: H_step.

(*+ ϛ_0_til +*)
move => H_ϛ_til.
by rewrite H_ϛ_til /ϛ_0_til //= in H_clo_til.

(*+ not ϛ_0_til +*)
move => [c_til [H_c_til H_step]].

rewrite -H_fix /step_Ξ_hat; pairs.

rewrite /prec_Ξ in H_prec.

move: (Ξ_til_wf_r H_wf c_til H_c_til) => [κs_til [H_stacks H_path]].

(*+=*) inversion H_step.

(*+= Let =+*)
set ϛ_hat := step_Σ_hat_Let_func x f ae b (Env_til_hat ρ_til) (Konts_til_hat κs_til) ξ_hat.2 x' e' (Env_til_hat ρ_λ_til).

exists ϛ_hat.
split.
right.
exists (C_til_hat c_til κs_til).
split.
by move: (H_prec.1 c_til H_c_til κs_til H_stacks).

(*+=+ step +=+*)
rewrite -H1 //= in H_prec.
move: (step_Σ_hat_Let x f ae b (Env_til_hat ρ_til) (Konts_til_hat κs_til) ξ_hat.2 x' e' (Env_til_hat ρ_λ_til) (substore_A_til_hat (prec_Clo_bij.2 (x', e', ρ_λ_til)).1 H_prec.2 H2)).
by rewrite /ϛ_hat /step_Σ_hat_Let_func -H /C_til_hat //=.

(*+=+ membership +=+*)
move: H_clo_til.
rewrite /ϛ_hat /step_Σ_hat_Let_func -H0 //=.
apply (substore_σ_extend_til_hat); try done.
by move: H_prec.2; rewrite -H1 //=.
by rewrite -H1 -H //= in H_stacks.

(*+= Ret =+*)
set κ_til := (x, e', ρ_κ_til, a'_κ_til).
move: (Ξ_til_wf_σ_κ H_wf a_κ_til (x, e', ρ_κ_til, a'_κ_til)).
rewrite -H1 //= => HH.
move: {HH} (HH H2).2 => [x_ [x1_ HH]].
have: ξ'_til.1 (Let x x_ x1_ e', ρ_κ_til, a'_κ_til).
by move: (Ξ_til_wf_r_sub H_wf (Let x x_ x1_ e', ρ_κ_til, a'_κ_til) HH.1).
move => HH1'.
move: {HH} (Ξ_til_wf_r H_wf _ HH1') => //= [κs'_til [H_κs'_til _]].

set ϛ_hat := step_Σ_hat_Ret_func ae (Env_til_hat ρ_til) ξ_hat.2 x e' (Env_til_hat ρ_κ_til) (Konts_til_hat κs'_til).

exists ϛ_hat.
split.
right.
exists (C_til_hat c_til (κ_til :: κs'_til)).
split.

(*+=+ membership +=+*)
apply (H_prec.1); try done.
apply stacks_cons; try done.
rewrite -H /not //= => HH.
rewrite HH in H2.
move: (Ξ_til_wf_a_κ_0 H_wf κ_til).
by rewrite /not -H1 /κ_til //= => HHH.
by rewrite -H1 -H /κ_til //=.

(*+=+ step +=+*)
move: (step_Σ_hat_Ret ae (Env_til_hat ρ_til) ξ_hat.2 x e' (Env_til_hat ρ_κ_til) (Konts_til_hat κs'_til)).
by rewrite /ϛ_hat -H /C_til_hat //=.

(*+=+ membership +=+*)
move: H_clo_til.
rewrite /ϛ_hat -H0 //=.
have: (x, e', Env_til_hat ρ_κ_til) :: Konts_til_hat κs'_til =
      Konts_til_hat ((x, e', ρ_κ_til, a'_κ_til) :: κs'_til) by [].
move => ->.
apply substore_σ_extend_til_hat; try done.
rewrite -H1 //= in H_prec.
by move: H_prec.2.
apply stacks_cons.
have: ξ'_til.2.2 a_κ_til (x, e', ρ_κ_til, a'_κ_til) by rewrite -H1.
by move/(Ξ_til_wf_a_κ_0' H_wf).
by rewrite -H1 in H_κs'_til.
by rewrite -H -H1 in H_stacks.
Qed.

(****)

Lemma step_prec_R {ξ_hat ξ_til ξ'_til}:
  step_Ξ_hat ξ_hat = ξ_hat ->
  @Ξ_til_wf ξ_til ξ'_til ->
  prec_Ξ ξ_hat ξ'_til ->
  prec_R ξ_hat (step_Ξ_til ξ'_til).
Proof.
move => H_fix H_wf H_prec.
move => c_til H_c_til κs_til.
move: (step_Ξ_til_wf H_wf) => H_step_wf.
move/(stacks_have_paths H_step_wf c_til H_c_til) => H_stacks.
move: (path_til_hat (ξ_hat:=ξ_hat) H_fix (step_Ξ_til_wf H_wf) (step_prec_Store H_fix H_wf H_prec) H_stacks) => H.
by move: (path_end_hat H).
Qed.


(**********************************)
(*** Iterated steps are precise ***)
(**********************************)

Inductive iterated: Ξ_til -> Prop :=
| iterated_null: iterated ξ_0_til
| iterated_cons {ξ'_til}: iterated ξ'_til -> iterated (step_Ξ_til ξ'_til).

Lemma iterated_wf {ξ'_til}: iterated ξ'_til -> exists ξ_til, @Ξ_til_wf ξ_til ξ'_til.
Proof.
elim.

exists ξ_0_til.
by move: Ξ_til_wf_ξ_0.

clear ξ'_til.
move => ξ'_til H_iterated [ξ_til H_wf].
exists ξ'_til.
by move: (step_Ξ_til_wf H_wf).
Qed.

Theorem iterated_prec {ξ_hat ξ'_til}: step_Ξ_hat ξ_hat = ξ_hat -> iterated ξ'_til -> prec_Ξ ξ_hat ξ'_til.
Proof.
move => H_fix.
elim.

(*+ iterated_null +*)
rewrite /ξ_0_til /prec_Ξ.
rewrite -H_fix /step_Ξ_hat; pairs.

split.
rewrite /prec_R //= => c_til H_c_til κs_til H_κs_til.
exists σ_0_hat.
left.
inversion H_κs_til.
rewrite H_c_til /ϛ_0_hat.
rewrite /C_til_hat /c_0_til /c_0_hat //=.
by rewrite /ρ_0_til Env_bij.2.
by rewrite /σ_κ_0_til in H1.

rewrite /prec_Store //= => a_hat a_til H_prec_Addr clo_hat clo_til H_prec_Clo H_clo_til.
exists ϛ_0_hat.
split.
by left.
by rewrite /σ_0_til in H_clo_til.

(*+ iterated_cons +*)
clear ξ'_til => ξ'_til H_iterated H_prec.
move: (iterated_wf H_iterated) => [? H_wf].
split.
by move: (step_prec_R H_fix H_wf H_prec).
by move: (step_prec_Store H_fix H_wf H_prec).
Qed.
