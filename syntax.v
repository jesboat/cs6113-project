Module CoreMLSynatx.
  
  Inductive variable_name : Type := 
  | sample_variable_name : variable_name.
  
  Inductive value : Type :=
  | Identifier : variable_name -> value
  | Unit :  value
  | Integer : nat -> value
  | Fix : value -> value -> value 
  | Tuple : value -> value -> value.
 

  Inductive expression : Type :=
  | Value : value -> expression 
  | Application : value -> value -> expression
  | Project1 : value -> expression
  | Project2 : value -> expression 
  | Let_Bind : variable_name -> value -> expression -> expression
  | Expression_Pair : expression -> expression -> expression
  | If : expression -> expression -> expression -> expression.


End CoreMLSynatx.
