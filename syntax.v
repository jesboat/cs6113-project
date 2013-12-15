

Require Export identifiers.



  Inductive label_type : Type := 
  | High_Label : label_type
  | Low_Label : label_type.
(* proof of correctness for labels will be no occurance of "unassigned" label
   in addition to the standard types-line-up deal.
*)

  Inductive simple_type : Type :=
  | Int_t : simple_type
  | Bottom_t : simple_type.

  Inductive type : Type :=
  | Simple_Type : simple_type -> label_type -> type
  | Fix_t : type -> type -> label_type  -> type.
  
  Inductive value : Type :=
  | Identifier : variable_name -> value
  | Unit :  value
  | Integer : nat -> value
  | Fix : variable_name -> expression -> value 
  | Void : value
  | Value_Evaluation_Pair : value -> value -> value

  with 
  expression : Type :=
  | Value : value -> expression 
  | Application : value -> value -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | If1 : value -> expression -> expression -> expression
  | Expression_Evaluation_Pair : expression -> expression -> expression.




