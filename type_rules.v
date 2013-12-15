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
  -> type_subtype (Fix_t t1 t2 l) (Fix_t t1' t2' l').

Inductive guards : label_type -> type -> Prop :=
| G_Unit : forall (l : label_type),
  guards l (Simple_Type Bottom_t l)
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
| V_Unit : forall (gamma : context) (l : label_type),
  value_has_type gamma Unit (Simple_Type Bottom_t l)
| V_Int : forall (gamma : context) (l : label_type) (n : nat),
  value_has_type gamma (Integer n) (Simple_Type Int_t l)
| V_Bracket : forall (gamma : context) (t : type) (v1 v2 : value),
  (value_has_type gamma v1 t) /\ (value_has_type gamma v2 t) /\ (guards High_Label t)
  -> value_has_type gamma (Value_Evaluation_Pair v1 v2) t
| V_Sub : forall (gamma : context) (t t' : type) (v : value),
  (value_has_type gamma v t') /\ (type_subtype t' t)
  -> value_has_type gamma v t
| V_Var : forall (gamma : context) (x : variable_name) (t : type),
  gamma x = Some t
  -> value_has_type gamma (Identifier x) t
| V_Abs : forall (gamma : context) (t t' : type) (l pc : label_type) (f x : variable_name) (e : expression),
  expression_has_type pc (extend (extend gamma f (Fix_t t' t l)) x t') e t
  -> value_has_type gamma (Fix f x e) (Fix_t t' t l)

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
  (value_has_type gamma (Identifier x) s) /\
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