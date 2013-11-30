Module CoreMLSynatx.
  
  Inductive exception : Type := 
  | sample_exception : exception.
  
  Inductive variable_name : Type := 
  | sample_variable_name : variable_name.
  
  Inductive memory_location : Type :=
  | sample_memory_location : memory_location.
  
  Inductive value : Type :=
  | Identifier : variable_name -> value
  | Unit :  value
  | Integer : nat -> value
  | Fix : value -> value -> value 
  | Memory_Location : memory_location -> value
  | Tuple : value -> value -> value
  | Inj1 : value -> value (* what is this inj term anyway?  I have no intuition into it *)
  | Inj2 : value -> value. 
  
  Inductive answer : Type := 
  | Value : value -> answer
  | Uncaught_Exception : exception -> value -> answer.
  

  Inductive expression : Type :=
  | Answer : answer -> expression 
  | Application : value -> value -> expression
  | Ref : value -> expression 
  | Mutate : value -> value -> expression 
  | Deref : value -> expression 
  | Project1 : value -> expression
  | Project2 : value -> expression 
  | Sum_Elimination : value -> variable_name -> expression -> expression -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | Evaluation_Context : expression -> evaluation_context -> expression

  with evaluation_context : Type := 
  | i_dont_know_what_the_brackets_are : evaluation_context.

End CoreMLSynatx.
