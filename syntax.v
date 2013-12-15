Module CoreMLSyntax.


(*racket-dependent *)
  Inductive variable_name : Type := 
  | x : variable_name
  | y : variable_name.

(*non-racket-dependent *)

  Inductive high_label : Type := 
  | High_Label_t : high_label.
  
  Inductive label_type : Type := 
  | High_Label : high_label -> label_type
  | Low_Label : label_type
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
  | Identifier : type -> variable_name -> value
  | Unit :  type -> value
  | Integer : type -> nat -> value
  | Fix : type -> variable_name -> expression -> value 
  | Void : type -> value
  | Value_Evaluation_Pair : type -> value -> value -> value

  with 
  expression : Type :=
  | Value : value -> expression 
  | Application : value -> value -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | If1 : value -> expression -> expression -> expression
  | Expression_Evaluation_Pair : expression -> expression -> expression.


End CoreMLSyntax.


