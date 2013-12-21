(** * SfLib: Software Foundations Library *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Import Setoid.

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
    destruct b; destruct c; auto.
Qed.

(** * From Logic.v *)

Inductive appears_in {T : Type} (n : T) : list T -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Theorem appears_in__In {T : Type} : forall (n : T) (lst : list T),
    appears_in n lst <-> In n lst.
Proof.
    intros n; induction lst.
    Case "empty". simpl. split; intro H; inversion H.
    Case "nonempty".
      split; intros H; inversion H; subst; simpl;
        try solve [ firstorder | constructor ].
      constructor 2. tauto.
Qed.

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Inductive total_relation {T : Type} : T -> T -> Prop :=
  tot : forall n m, total_relation n m.

Inductive empty_relation {T : Type} : T -> T -> Prop := .

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy; [ trivial | eapply multi_step; eauto ].
Qed. 

Module RelExtra.

  Definition partial_function {X: Type} (R: relation X) :=
    forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

  Definition reflexive {X: Type} (R: relation X) :=
    forall a : X, R a a.

  Definition transitive {X: Type} (R: relation X) :=
    forall a b c : X, (R a b) -> (R b c) -> (R a c).

  Definition symmetric {X: Type} (R: relation X) :=
    forall a b : X, (R a b) -> (R b a).

  Definition antisymmetric {X: Type} (R: relation X) :=
    forall a b : X, (R a b) -> (R b a) -> a = b.

  Definition equivalence {X:Type} (R: relation X) :=
    (reflexive R) /\ (symmetric R) /\ (transitive R).

  Definition order {X:Type} (R: relation X) :=
    (reflexive R) /\ (antisymmetric R) /\ (transitive R).

  Definition preorder {X:Type} (R: relation X) :=
    (reflexive R) /\ (transitive R).

  Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
      | rt_step : forall x y, R x y -> clos_refl_trans R x y
      | rt_refl : forall x, clos_refl_trans R x x
      | rt_trans : forall x y z,
            clos_refl_trans R x y ->
            clos_refl_trans R y z ->
            clos_refl_trans R x z.

  Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
    | rsc_refl  : forall (x : X), refl_step_closure R x x
    | rsc_step : forall (x y z : X),
                      R x y ->
                      refl_step_closure R y z ->
                      refl_step_closure R x z.

End RelExtra.

(**  Identifiers and polymorphic partial maps. *)

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  decide equality. apply eq_nat_dec.
Defined. 

Definition beq_id (id1 id2 : id) : bool :=
  match id1, id2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id__eq (id1 id2 : id) :
    beq_id id1 id2 = true <-> id1 = id2.
Proof.
  destruct id1 as [n1]; destruct id2 as [n2].
  pose proof (beq_nat_true_iff n1 n2).
  setoid_replace (Id n1 = Id n2) with (n1 = n2)
      by (firstorder; congruence).
  tauto.  
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x); congruence.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros.
  destruct (eq_id_dec x y); congruence.
Qed.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Notation "'\empty'" := empty.

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (eq_id_dec x2 x1)...
Qed.

(** -------------------- *)

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.
