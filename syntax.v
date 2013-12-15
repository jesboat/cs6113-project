Module CoreMLSyntax.


(*racket-dependent *)
  Inductive variable_name : Type := 
  | x : variable_name
  | y : variable_name.

(*non-racket-dependent *)

  Inductive high_label : Type := 
  | High_Label_t : high_label.
  
  Inductive label : Type := 
  | High_Label : high_label -> label
  | Low_Label : label.

  Inductive simple_type : Type :=
  | Int_t : simple_type
  | Fix_t : simple_type -> simple_type -> simple_type
  | Bottom_t : simple_type.
  
  Inductive type : Type :=
  | Type_type : simple_type -> label -> type.



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
  | If1 : expression -> expression -> expression -> expression
  | Expression_Evaluation_Pair : expression -> expression -> expression.

Check Let_Bind (x) 
      ( Integer 3) (Value ( Fix (y) (Value ( Identifier x)) )) .

End CoreMLSyntax.


