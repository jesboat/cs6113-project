Require Import syntax.

Inductive label_subtype : label_type -> label_type -> Prop :=
| Label_Same : forall (l : label_type), label_subtype l l
| Low_High : label_subtype Low_Label High_Label.

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

Require Import SfLib.

Definition context := partial_map type.

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
  -> value_has_type gamma v t.