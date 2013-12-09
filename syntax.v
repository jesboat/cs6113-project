Module CoreMLSynatx.
  
  Inductive variable_name : Type := 
  | sample_variable_name : variable_name.
  
  Inductive value : Type :=
  | Identifier : variable_name -> value
  | Unit :  value
  | Integer : nat -> value
  | Fix : variable_name -> expression -> value 
  | Tuple : value -> value -> value
  | Void : value
  | Value_Evaluation_Pair : value -> value -> value

  with 
  expression : Type :=
  | Value : value -> expression 
  | Application : value -> value -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | If : expression -> expression -> expression -> expression
  |	Expression_Evaluation_Pair : expression -> expression -> expression
  | Project1 : value -> expression
  | Project2 : value -> expression.

	
End CoreMLSynatx.
