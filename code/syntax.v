
  Inductive variable_name : Set :=
  | Var : nat -> variable_name.

  Inductive label_type : Set :=
  | High_Label : label_type
  | Low_Label : label_type.
(* proof of correctness for labels will be no occurance of "unassigned" label
   in addition to the standard types-line-up deal.
*)

  Inductive type : Set :=
  | Int_t : label_type -> type
  | Fix_t : type -> type -> label_type -> type.

  Inductive value : Set :=
  | Identifier : type -> variable_name -> value
  | Integer : type -> nat -> value
  | Fix : type -> variable_name -> variable_name -> expression -> value 
  | Value_Evaluation_Pair : type -> value -> value -> value

  with 
  expression : Set :=
  | Value : value -> expression 
  | Application : value -> value -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | If1 : value -> expression -> expression -> expression
  | Expression_Evaluation_Pair : expression -> expression -> expression.

