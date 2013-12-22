Require Import Coq.Program.Program.
Require Import SfLib.

Open Scope bool_scope.


Inductive variable_name : Set :=
  | Var : nat -> variable_name.

Function names_equal (n1 : variable_name) (n2 : variable_name) : bool :=
  match n1 with
      | Var m1 => (match n2 with | Var m2 => (beq_nat m1 m2) end)
  end.


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

with expression : Set :=
  | Value : value -> expression
  | Application : value -> value -> expression
  | Let_Bind : variable_name -> value -> expression -> expression
  | If1 : value -> expression -> expression -> expression
  | Expression_Evaluation_Pair : expression -> expression -> expression.



Function left_branch (expr : expression) :=
  match expr with
    | Expression_Evaluation_Pair l r => (left_branch l)
    | Value v => Value (left_branch_val v)
    | Application f a => Application (left_branch_val f) (left_branch_val a)
    | Let_Bind nm vl e => Let_Bind nm (left_branch_val vl) (left_branch e)
    | If1 t b1 b2 => If1 (left_branch_val t) (left_branch b1) (left_branch b2)
  end

with left_branch_val (val : value) {struct val} :=
  match val with
    | Identifier t vn => val
    | Integer _ _ => val
    | Fix t f a b => Fix t f a (left_branch b)
    | Value_Evaluation_Pair t l r => (left_branch_val l)
  end.

Function right_branch (expr : expression) :=
  match expr with
    | Expression_Evaluation_Pair l r => (right_branch r)
    | Value v => Value (right_branch_val v)
    | Application f a => Application (right_branch_val f) (right_branch_val a)
    | Let_Bind nm vl e => Let_Bind nm (right_branch_val vl) (right_branch e)
    | If1 t b1 b2 => If1 (right_branch_val t) (right_branch b1) (right_branch b2)
  end

with right_branch_val (val : value) :=
  match val with
    | Identifier t vn => val
    | Integer _ _ => val
    | Fix t f a b => Fix t f a (right_branch b)
    | Value_Evaluation_Pair t l r => (right_branch_val r)
  end.

Fixpoint get_type (val : value) : type :=
  match val with
    | Identifier t _ => t
    | Integer t _ => t
    | Fix t f a b => t
    | Value_Evaluation_Pair t l r => t
  end.

Function subst_values (var : variable_name) (bind : value) (val : value): value :=
  match val with
    | Identifier _ nm => if (names_equal nm var) then bind else val
    | Fix t f a b => if (names_equal f var) then val else
                       if (names_equal a var) then val else
                         Fix t f a (subst var bind b)
    | Value_Evaluation_Pair t v1 v2 => Value_Evaluation_Pair t (subst_values var bind v1)
                                                             (subst_values var bind v2)
    | _ => val
  end

with subst (var : variable_name) (bind : value) (expr : expression) : expression :=
  let subst_values := (fun val => subst_values var bind val) in
  let subst := (fun val => subst var bind val) in
  match expr with
    | Value v => Value (subst_values v)
    | Application f a => Application (subst_values f) (subst_values a)
    | Let_Bind name val expr =>
      let new_val := (subst_values val) in
      let new_expr := if (names_equal name var) then expr else (subst expr) in
      Let_Bind name new_val new_expr
    | If1 t th el => If1 (subst_values t) (subst th) (subst el)
    | Expression_Evaluation_Pair l r => Expression_Evaluation_Pair (subst l) (subst r)
  end.


