Require Import syntax.
Require Import SfLib.

Inductive label_subtype : label_type -> label_type -> Prop :=
| Label_Same : forall (l : label_type), label_subtype l l
| Low_High : label_subtype Low_Label High_Label.

Definition label_join (l1 l2 : label_type) : label_type :=
match l1 with
| High_Label => High_Label
| Low_Label => l2
end.

Inductive type_subtype : type -> type -> Prop :=
| S_Int : forall (l l' : label_type),
  label_subtype l l' -> type_subtype (Int_t l) (Int_t l')
| S_Abs : forall (t1 t2 t1' t2' : type) (l l' : label_type),
  (label_subtype l l')
  -> (type_subtype t1' t1)
  -> (type_subtype t2 t2')
  -> type_subtype (Fix_t t1 t2 l) (Fix_t t1' t2' l')
| S_Refl : forall (t1 : type), type_subtype t1 t1.

Inductive guards : label_type -> type -> Prop :=
| G_Int : forall (l : label_type),
  guards l (Int_t l)
| G_Abs : forall (t1 t2 : type) (l l' : label_type),
  label_subtype l l' -> guards l (Fix_t t1 t2 l').

Inductive context : Set :=
| empty : context
| extend : context -> variable_name -> type -> context.

Definition identifier_id (var : variable_name) : nat :=
match var with
| Var n => n
end.

Definition var_name_eq (var1 var2 : variable_name) : bool :=
beq_nat (identifier_id var1) (identifier_id var2).

Fixpoint find_in_context (gamma : context) (x : variable_name) : option type :=
match gamma with
| empty => None
| extend gamma' x' t => if var_name_eq x x' then Some t else find_in_context gamma' x
end.

Require Import Coq.Arith.EqNat.

Inductive value_has_type : context -> value -> type -> Prop :=
| V_Int : forall (gamma : context) (l : label_type) (n : nat),
  value_has_type gamma (Integer (Int_t l) n) (Int_t l)
| V_Bracket : forall (gamma : context) (t : type) (v1 v2 : value),
  (value_has_type gamma v1 t)
  -> (value_has_type gamma v2 t)
  -> (guards High_Label t)
  -> value_has_type gamma (Value_Evaluation_Pair t v1 v2) t
| V_Sub : forall (gamma : context) (t t' : type) (v : value),
  (value_has_type gamma v t')
  -> (type_subtype t' t)
  -> value_has_type gamma v t
| V_Var : forall (gamma : context) (x : variable_name) (t : type),
  find_in_context gamma x = Some t
  -> value_has_type gamma (Identifier t x) t
| V_Abs : forall (gamma : context) (t t' : type) (l pc : label_type)
    (f x : variable_name) (e : expression),
  expression_has_type pc (extend (extend gamma f (Fix_t t' t l)) x t') e t
  -> value_has_type gamma (Fix (Fix_t t' t l) f x e) (Fix_t t' t l)

with expression_has_type : label_type -> context -> expression -> type -> Prop :=
| E_Value : forall (pc : label_type) (gamma : context) (v : value) (t : type),
  value_has_type gamma v t
  -> expression_has_type pc gamma (Value v) t
| E_App : forall (pc l : label_type) (gamma : context) (f v1 : value) (t1 t2 : type),
  (value_has_type gamma f (Fix_t t1 t2 l))
  -> (value_has_type gamma v1 t1)
  -> (guards l t2)
  -> (expression_has_type pc gamma (Application f v1) t2)
| E_If : forall (pc l : label_type) (gamma : context) (v1 : value) (e2 e3 : expression) (t : type),
  (value_has_type gamma v1 (Int_t l))
  -> (expression_has_type (label_join pc l) gamma e2 t)
  -> (expression_has_type (label_join pc l) gamma e3 t)
  -> (guards l t)
  -> expression_has_type pc gamma (If1 v1 e2 e3) t
| E_Let : forall (pc : label_type) (gamma : context) (x : variable_name) (v : value) (e : expression) (s t : type),
  (value_has_type gamma (Identifier s x) s)
  -> (expression_has_type pc (extend gamma x s) e t)
  -> expression_has_type pc gamma (Let_Bind x v e) t
| E_Sub : forall (pc : label_type) (gamma : context) (e : expression) (t t' : type),
  (expression_has_type pc gamma e t')
  -> (type_subtype t' t)
  -> expression_has_type pc gamma e t
| E_Bracket : forall (pc : label_type) (gamma : context) (e1 e2 : expression) (t : type),
  (expression_has_type High_Label gamma e1 t)
  -> (expression_has_type High_Label gamma e2 t)
  -> (guards High_Label t)
  -> expression_has_type pc gamma (Expression_Evaluation_Pair e1 e2) t.

(** Utility functions for checking equality and subtyping relations of types. *)
Definition label_eq (l1 l2 : label_type) : bool :=
match (l1, l2) with
| (High_Label, High_Label) => true
| (Low_Label, Low_Label) => true
| (High_Label, Low_Label) => false
| (Low_Label, High_Label) => false
end.

Fixpoint type_eq (t1 t2 : type) : bool :=
match (t1, t2) with
| (Int_t l1, Int_t l2) => label_eq l1 l2
| (Int_t _, Fix_t _ _ _) => false
| (Fix_t _ _ _, Int_t _) => false
| (Fix_t t1in t1out l1, Fix_t t2in t2out l2) =>
  andb (label_eq l1 l2) (andb (type_eq t1in t2in) (type_eq t1out t2out))
end.

Definition label_subtype_of (l1 l2 : label_type) : bool :=
match (l1, l2) with
| (High_Label, High_Label) => true
| (Low_Label, High_Label) => true
| (Low_Label, Low_Label) => true
| (High_Label, Low_Label) => false
end.

Fixpoint max (n1 n2 : nat) : nat :=
match (n1, n2) with
| (0, 0) => 0
| (S _, 0) => n1
| (0, S _) => n2
| (S n1', S n2') => S (max n1' n2')
end.

Fixpoint depth_of (t : type) : nat :=
match t with
| (Int_t _) => 1
| (Fix_t t1 t2 _) => S (max (depth_of t1) (depth_of t2))
end.

Fixpoint subtype_of (t1 t2 : type) (n:nat) : option bool :=
match (t1, t2, n) with
| (Int_t l1, Int_t l2, S _) => Some (label_subtype_of l1 l2)
| (Int_t _, Fix_t _ _ _, S _) => Some false
| (Fix_t _ _ _, Int_t _, S _) => Some false
| (Fix_t in1 out1 l1, Fix_t in2 out2 l2, S n') =>
  match (subtype_of in2 in1 n') with
  | None => None
  | Some false => Some false
  | Some true => match (subtype_of out1 out2 n') with
                 | None => None
                 | Some false => Some false
                 | Some true => Some (label_subtype_of l1 l2)
                 end
  end
| (_, _, 0) => None
end.

Definition label_of (t : type) : label_type :=
match t with
| Int_t l => l
| Fix_t _ _ l => l
end.

Definition guardsb (l : label_type) (t : type) : bool :=
label_subtype_of l (label_of t).

(** Ugh, this is probably wrong... *)
Definition type_of_value (gamma : context) (v : value) : type :=
match v with
| (Integer t n) => t
| (Value_Evaluation_Pair t v1 v2) => t
| (Identifier t x) => t
(* I should really double check the type of the expression first... *)
| (Fix t f x e) => t
end.

(** Blarrrrrrrrrrrrrrrrrrrrrg *)
Fixpoint type_of_expression (pc : label_type) (gamma : context) (e : expression) : option type :=
match e with
| (Value v) => Some (type_of_value gamma v)
| (Let_Bind x v e) => type_of_expression pc (extend gamma x (type_of_value gamma v)) e
| (If1 v e1 e2) =>
  match (type_of_value gamma v) with
  | (Fix_t _ _ _) => None
  | (Int_t l) =>
    match (type_of_expression (label_join pc l) gamma e1) with
    | Some t1 => match (type_of_expression (label_join pc l) gamma e2) with
                 | Some t2 =>
                   let d := (max (depth_of t1) (depth_of t2)) in
                   if subtype_of t1 t2 d then Some t2
                   else if subtype_of t2 t1 d then Some t1
                   else None
                 | None => None
                 end
    | None => None
    end
  end
| (Expression_Evaluation_Pair e1 e2) => 
  match (type_of_expression High_Label gamma e1) with
  | Some t1 => match (type_of_expression High_Label gamma e2) with
               | Some t2 =>
                 let d := (max (depth_of t1) (depth_of t2)) in
                 if subtype_of t1 t2 d
                 then if guardsb High_Label t2
                      then Some t2
                      else None 
                 else if subtype_of t2 t1 d
                      then if guardsb High_Label t1
                           then Some t1
                           else None
                 else None
               | None => None
               end
  | None => None
  end
| (Application f v) =>
  let tf := type_of_value gamma f in
  match tf with
  | (Int_t l) => None
  | (Fix_t tin tout l) =>
    let tv := type_of_value gamma v in
    if guardsb l tv
    then if subtype_of tv tin (max (depth_of tv) (depth_of tin))
         then Some tout
         else None
    else None
  end
end.

Definition well_typed (pc : label_type) (gamma : context) (e : expression) : Prop :=
match (type_of_expression pc gamma e) with
| Some _ => True
| None => False
end.

Fixpoint subst_v (v v_replacement : value) (var : variable_name) : value :=
match v with
| Identifier _ name =>
    if var_name_eq var name then v_replacement else v
| Integer _ _ => v
| Fix t fun_name param_name expr =>
    if orb (var_name_eq var fun_name)
           (var_name_eq var param_name)
    then v
    else Fix t fun_name param_name (subst_e expr v_replacement var)
| Value_Evaluation_Pair t v1 v2 =>
    Value_Evaluation_Pair t (subst_v v1 v_replacement var)
                            (subst_v v2 v_replacement var)
end

with subst_e (e : expression) (v_replacement : value) (var : variable_name) : expression :=
match e with
| Value v =>
    Value (subst_v v v_replacement var)
| Application v1 v2 =>
    Application (subst_v v1 v_replacement var) (subst_v v2 v_replacement var)
| Let_Bind let_var let_val let_exp =>
    if var_name_eq let_var var
    then e
    else Let_Bind let_var
                  (subst_v let_val v_replacement var)
                  (subst_e let_exp v_replacement var)
| If1 if_val true_exp false_exp =>
    If1 (subst_v if_val v_replacement var)
        (subst_e true_exp v_replacement var)
        (subst_e false_exp v_replacement var)
| Expression_Evaluation_Pair e1 e2 =>
    Expression_Evaluation_Pair (subst_e e1 v_replacement var)
                               (subst_e e2 v_replacement var)
end.

Inductive appears_free_in_value : variable_name -> value -> Prop :=
| afiv_var : forall (x : variable_name) (t : type),
    appears_free_in_value x (Identifier t x)
| afiv_fix : forall (x f y : variable_name) (e : expression) (t1 t2 : type) (l : label_type),
    x <> y
    -> x <> f
    -> appears_free_in_expression x e
    -> appears_free_in_value x (Fix (Fix_t t1 t2 l) f y e)
| afiv_bracket_left : forall (x : variable_name) (v1 v2 : value) (t : type),
    appears_free_in_value x v1
    -> appears_free_in_value x (Value_Evaluation_Pair t v1 v2)
| afiv_bracket_right : forall (x : variable_name) (v1 v2 : value) (t : type),
    appears_free_in_value x v2
    -> appears_free_in_value x (Value_Evaluation_Pair t v1 v2)

with appears_free_in_expression : variable_name -> expression -> Prop :=
| afie_var : forall (x : variable_name) (v : value),
    appears_free_in_value x v
    -> appears_free_in_expression x (Value v)
| afie_app1 : forall (x : variable_name) (v1 v2 : value),
    appears_free_in_value x v1
    -> appears_free_in_expression x (Application v1 v2)
| afie_app2 : forall (x : variable_name) (v1 v2 : value),
    appears_free_in_value x v2
    -> appears_free_in_expression x (Application v1 v2)
| afie_let1 : forall (x y : variable_name) (v : value) (e : expression),
    x <> y
    -> appears_free_in_value x v
    -> appears_free_in_expression x (Let_Bind y v e)
| afie_let2 : forall (x y : variable_name) (v : value) (e : expression),
    x <> y
    -> appears_free_in_expression x e
    -> appears_free_in_expression x (Let_Bind y v e)
| afie_iftest : forall (x : variable_name) (v : value) (et ef : expression),
    appears_free_in_value x v
    -> appears_free_in_expression x (If1 v et ef)
| afie_iftrue : forall (x : variable_name) (v : value) (et ef : expression),
    appears_free_in_expression x et
    -> appears_free_in_expression x (If1 v et ef)
| afie_iffalse : forall (x : variable_name) (v : value) (et ef : expression),
    appears_free_in_expression x ef
    -> appears_free_in_expression x (If1 v et ef)
| afie_bracket_left : forall (x : variable_name) (e1 e2 : expression),
    appears_free_in_expression x e1
    -> appears_free_in_expression x (Expression_Evaluation_Pair e1 e2)
| afie_bracket_right : forall (x : variable_name) (e1 e2 : expression),
    appears_free_in_expression x e2
    -> appears_free_in_expression x (Expression_Evaluation_Pair e1 e2).

Definition closed_val (v : value) :=
forall (x : variable_name), ~appears_free_in_value x v.

Definition closed_exp (e : expression) :=
forall (x : variable_name), ~appears_free_in_expression x e.

Theorem Lemma_10_val :
  forall (v v' : value) (s t : type) (gamma : context) (x : variable_name),
  value_has_type empty v s ->
  value_has_type (extend gamma x s) v' t ->
  value_has_type gamma (subst_v v' v x) t.
Proof.
  intros v v' s t gamma x VtypedS V'typedT.
  induction V'typedT.
  (* Case V-Int is identifier *)
  simpl. apply V_Int.
  (* Case V-Bracket *)
  simpl. apply V_Bracket.
  (* SCase left *)
  apply IHV'typedT1.
  (* SCase right *)
  apply IHV'typedT2.
  (* SCase guards *)
  apply H.
  (* Case subtype *)
  apply V_Sub with (t':=t').
  (* SCase Prove it works for subtype *)
  apply IHV'typedT.
  (* SCase Prove subtyping relation *)
  apply H.
  (* Case V_Var *)
  simpl.
  destruct (var_name_eq x x0) eqn:IdCheck.
  (* SCase id's are equal *)
  admit.
  (* SCase different id's *)
  admit.
  (* Case V_Abs *)
  simpl.
  destruct (var_name_eq x f || var_name_eq x x0) eqn:CaptureCheck.
  (* SCase id is equal to one of the argument names *)
  admit.
  (* SCase id is not captured by arg names *)
  admit.
Qed.
