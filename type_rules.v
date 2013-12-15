Require Import syntax.

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
  label_subtype l l' -> type_subtype (Simple_Type Int_t l) (Simple_Type Int_t l')
| S_Abs : forall (t1 t2 t1' t2' : type) (l l' : label_type),
  (label_subtype l l') /\ (type_subtype t1' t1) /\ (type_subtype t2 t2')
  -> type_subtype (Fix_t t1 t2 l) (Fix_t t1' t2' l')
| S_Refl : forall (t1 : type), type_subtype t1 t1.

Inductive guards : label_type -> type -> Prop :=
| G_Int : forall (l : label_type),
  guards l (Simple_Type Int_t l)
| G_Abs : forall (t1 t2 : type) (l l' : label_type),
  label_subtype l l' -> guards l (Fix_t t1 t2 l').

Definition context := variable_name -> option type.

Definition empty : context := (fun _ => None).

Require Import Coq.Arith.EqNat.

Definition extend (Gamma : context) (x : variable_name) (T : type) :=
  match x with
  | Var n => fun x' => match x' with
                       | Var n' => if beq_nat n n' then Some T else Gamma x'
                       end
  end.

Inductive value_has_type : context -> value -> type -> Prop :=
| V_Int : forall (gamma : context) (l : label_type) (n : nat),
  value_has_type gamma (Integer (Simple_Type Int_t l) n) (Simple_Type Int_t l)
| V_Bracket : forall (gamma : context) (t : type) (v1 v2 : value),
  (value_has_type gamma v1 t) /\ (value_has_type gamma v2 t) /\ (guards High_Label t)
  -> value_has_type gamma (Value_Evaluation_Pair t v1 v2) t
| V_Sub : forall (gamma : context) (t t' : type) (v : value),
  (value_has_type gamma v t') /\ (type_subtype t' t)
  -> value_has_type gamma v t
| V_Var : forall (gamma : context) (x : variable_name) (t : type),
  gamma x = Some t
  -> value_has_type gamma (Identifier t x) t
| V_Abs : forall (gamma : context) (t t' : type) (l pc : label_type) (f x : variable_name) (e : expression),
  expression_has_type pc (extend (extend gamma f (Fix_t t' t l)) x t') e t
  -> value_has_type gamma (Fix (Fix_t t' t l) f x e) (Fix_t t' t l)

with expression_has_type : label_type -> context -> expression -> type -> Prop :=
| E_Value : forall (pc : label_type) (gamma : context) (v : value) (t : type),
  value_has_type gamma v t -> expression_has_type pc gamma (Value v) t
| E_App : forall (pc l : label_type) (gamma : context) (f v1 : value) (t1 t2 : type),
  (value_has_type gamma f (Fix_t t1 t2 l)) /\ (value_has_type gamma v1 t1) /\ (guards l t2)
  -> (expression_has_type pc gamma (Application f v1) t2)
| E_If : forall (pc l : label_type) (gamma : context) (v1 : value) (e2 e3 : expression) (t : type),
  (value_has_type gamma v1 (Simple_Type Int_t l)) /\
  (expression_has_type (label_join pc l) gamma e2 t) /\
  (expression_has_type (label_join pc l) gamma e3 t) /\
  (guards l t)
  -> expression_has_type pc gamma (If1 v1 e2 e3) t
| E_Let : forall (pc : label_type) (gamma : context) (x : variable_name) (v : value) (e : expression) (s t : type),
  (value_has_type gamma (Identifier s x) s) /\
  (expression_has_type pc (extend gamma x s) e t)
  -> expression_has_type pc gamma (Let_Bind x v e) t
| E_Sub : forall (pc : label_type) (gamma : context) (e : expression) (t t' : type),
  (expression_has_type pc gamma e t') /\
  (type_subtype t' t)
  -> expression_has_type pc gamma e t
| E_Bracket : forall (pc : label_type) (gamma : context) (e1 e2 : expression) (t : type),
  (expression_has_type High_Label gamma e1 t) /\
  (expression_has_type High_Label gamma e2 t) /\
  (guards High_Label t)
  -> expression_has_type pc gamma (Expression_Evaluation_Pair e1 e2) t.

(** Utility functions for checking equality and subtyping relations of types. *)
Definition label_eq (l1 l2 : label_type) : bool :=
match (l1, l2) with
| (High_Label, High_Label) => true
| (Low_Label, Low_Label) => true
| (High_Label, Low_Label) => false
| (Low_Label, High_Label) => false
end.

Definition simple_type_eq (t1 t2 : simple_type) : bool :=
match (t1, t2) with
| (Int_t, Int_t) => true
end.

Fixpoint type_eq (t1 t2 : type) : bool :=
match (t1, t2) with
| (Simple_Type t1' l1', Simple_Type t2' l2') =>
  if (label_eq l1' l2') then (simple_type_eq t1' t2') else false
| (Fix_t _ _ _, Simple_Type _ _) => false
| (Simple_Type _ _, Fix_t _ _ _) => false
| (Fix_t t1in t1out l1, Fix_t t2in t2out l2) =>
  if (label_eq l1 l2) then
    if (type_eq t1in t2in) then
      (type_eq t1out t2out)
      else false
    else false
end.

Definition label_subtype_of (l1 l2 : label_type) : bool :=
match (l1, l2) with
| (High_Label, High_Label) => true
| (Low_Label, High_Label) => true
| (Low_Label, Low_Label) => true
| (High_Label, Low_Label) => false
end.

Definition simple_subtype_of (t1 t2 : simple_type) : bool :=
match (t1, t2) with
| (Int_t, Int_t) => true
end.

Fixpoint subtype_of (t1 t2 : type) : bool :=
if (type_eq t1 t2)
then true
else match (t1, t2) with
     | (Simple_Type t1' l1, Simple_Type t2' l2) =>
                     andb (label_subtype_of l1 l2) (simple_subtype_of t1' t2')
     | (Simple_Type _ _, Fix_t _ _ _) => false
     | (Fix_t _ _ _, Simple_Type _ _) => false
     | (Fix_t t1in t1out l1, Fix_t t2in t2out l2) =>
                     andb (andb (subtype_of t2in t1in)
                                (subtype_of t1out t2out))
                          (label_subtype_of l1 l2)
     end.

(** Ugh, this is probably wrong... *)
Definition type_of_value (gamma : context) (v : value) : type :=
match v with
| (Integer t n) => t
| (Value_Evaluation_Pair t v1 v2) => t
| (Identifier t x) => t
| (Fix t f x e) => t
end.

(** Blarrrrrrrrrrrrrrrrrrrrrg *)
Fixpoint type_of_expression (pc : label_type) (gamma : context) (e : expression) : option type :=
match e with
| (Value v) => Some (type_of_value gamma v)
| (Let_Bind x v e) => type_of_expression pc (extend gamma x (type_of_value gamma v)) e
| (If1 v e1 e2) => 
| (Expression_Evaluation_Pair e1 e2) => 
| (Application f v) => 
end.
