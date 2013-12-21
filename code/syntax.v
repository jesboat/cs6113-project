Require Import SfLib.

Inductive label_type : Set :=
  | High_Label : label_type
  | Low_Label : label_type.
(* proof of correctness for labels will be no occurance of "unassigned" label
   in addition to the standard types-line-up deal.
*)

Inductive type : Set :=
  | Int_t : label_type -> type
  | Fix_t : type -> type -> label_type -> type.

Inductive pair_status : Set :=
  | pairfree : pair_status
  | has_pair : pair_status.

Inductive valuePS : pair_status -> Set :=
  | Identifier : type -> id -> valuePS pairfree
  | Integer : type -> nat -> valuePS pairfree
  | Fix : forall ps,
      type -> id -> id -> expressionPS ps -> valuePS ps
  | Value_Evaluation_Pair :
      type -> valuePS pairfree -> valuePS pairfree -> valuePS has_pair

with
  expressionPS : pair_status -> Set :=
  | Value : forall ps,
      valuePS ps -> expressionPS ps
  | Application : forall ps,
      valuePS ps -> valuePS ps -> expressionPS ps
  | Let_Bind : forall ps,
      id -> valuePS ps -> expressionPS ps -> expressionPS ps
  | If1 : forall ps,
      valuePS ps -> expressionPS ps -> expressionPS ps -> expressionPS ps
  | Expression_Evaluation_Pair :
      expressionPS pairfree -> expressionPS pairfree -> expressionPS has_pair.

Inductive value : Set :=
  | valuew : forall ps, valuePS ps -> value.

Inductive expression : Set :=
  | expressionw : forall ps, expressionPS ps -> expression.

Inductive environment : Set :=
  | Empty_Env : environment
  | Env : (id * value) -> environment -> environment.

(* better plan: no indirection permitted.  env only ever identifier-values to non-identifier values.*)
Function find_in_env (key : id) (env : environment) : (option value) :=
  match env with
    | Empty_Env => None
    | Env (vname, val) rst =>
      if (beq_id key vname) then Some val
      else find_in_env key rst
  end.

Function reduce_identifier (id : value) (env : environment) : value :=
  match id with
    | valuew _ (Identifier t v) =>
        (match (find_in_env v env) with
                   | Some v => v
                   | _ => id
                end)
    | _ => id
  end.

Fixpoint env_cons (id : id) (bind : value) (env : environment) : environment :=
  match id with
      | Id v => Env (id, (reduce_identifier bind env)) env
  end.

Function right_branch (expr : expression) :=
  match expr with
    | Expression_Evaluation_Pair l r => (right_branch r)
    | Value v => Value (right_branch_val v)
    | Application f a => Application (right_branch_val f) (right_branch_val a)
    | Let_Bind nm vl e => Let_Bind nm (right_branch_val vl) (right_branch e)
    | If1 t b1 b2 => If1 (right_branch_val t) (right_branch b1) (right_branch b2)
  end

with right_branch_val (val : value) {struct val} :=
  match val with
    | Identifier t vn => val
    | Integer _ _ => val
    | Fix t f a b => Fix t f a (right_branch b)
    | Value_Evaluation_Pair t l r => (right_branch_val r)
  end.




