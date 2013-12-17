Require Export syntax.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Export SfLib.
Require Export Rel.

Inductive environment : Type :=
| Empty_Env : environment
| Env : (variable_name * value) -> environment -> environment.

Fixpoint extract_num (var : variable_name) : nat := 
  match var with
    | Var n => n
  end.

Fixpoint names_equal (n1 : variable_name) (n2 : variable_name) : bool := 
  match n1 with
      | Var m1 => (match n2 with | Var m2 => (beq_nat m1 m2) end)
  end.

(* better plan: no indirection permitted.  env only ever identifier-values to non-identifier values.*)
Fixpoint find_in_env (key : variable_name) (env : environment) : (option value) := 
  match env with 
    | Empty_Env => None
    | Env (vname, val) rst => 
      if (names_equal key vname) then Some val
      else find_in_env key rst
  end.

Fixpoint reduce_identifier (id : value) (env : environment) : value := 
  match id with
    | Identifier t v => (match (find_in_env v env) with
                           | Some v => v
                           | _ => id
                        end)
    | _ => id
  end.

Fixpoint env_cons (id : variable_name) (bind : value) (env : environment) : environment :=
  match id with 
      | Var v => Env (id, (reduce_identifier bind env)) env
  end.


Function right_branch (expr : expression) {struct expr} := 
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

Function left_branch (expr : expression) {struct expr} := 
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

Fixpoint get_type (val : value) : type := 
  match val with 
    | Identifier t _ => t
    | Integer t _ => t
    | Fix t f a b => t
    | Value_Evaluation_Pair t l r => t
  end.

Function beta_reduction_values (var : variable_name) (bind : value) (val : value): value :=
  match val with
    | Identifier _ nm => if (names_equal nm var) then bind else val
    | Fix t f a b => if (names_equal f var) then val else 
                       if (names_equal a var) then val else
                         Fix t f a (beta_reduction var bind b)
    | Value_Evaluation_Pair t v1 v2 => Value_Evaluation_Pair t (beta_reduction_values var bind v1)
                                                             (beta_reduction_values var bind v2)
    | _ => val
  end

with beta_reduction (var : variable_name) (bind : value) (expr : expression) : expression := 
  let beta_reduction_values := (fun val => beta_reduction_values var bind val) in 
  let beta_reduction := (fun val => beta_reduction var bind val) in 
  match expr with
    | Value v => Value (beta_reduction_values v)
    | Application f a => Application (beta_reduction_values f) (beta_reduction_values a)
    | Let_Bind name val expr => 
      let new_val := (beta_reduction_values val) in
      let new_expr := if (names_equal name var) then expr else (beta_reduction expr) in
      Let_Bind name new_val new_expr
    | If1 t th el => If1 (beta_reduction_values t) (beta_reduction th) (beta_reduction el)
    | Expression_Evaluation_Pair l r => Expression_Evaluation_Pair (beta_reduction l) (beta_reduction r)
  end.

(* big-step semantics of the language *)
(* since our non-interference proof is of the form 
"Iff computation terminates with a low type, it terminates with a single value"
We don't actually have to prove any properties of step_bound in the reduction rules
(we allow divergence) *)

Fixpoint reduction_rules (expr : expression) (recursion_bound : nat) (step_bound : nat) : (option value) := 
  match step_bound with 
    | S sb => 
      (match expr with 
         | Value v => (match v with 
                           | Identifier t nm => None (* unbound identifier *)
                           | _ => Some v
                       end)
         | Application f a => 
           (match f with
              | Value_Evaluation_Pair t l r => 
                let new_expr := (Expression_Evaluation_Pair 
                                   (Application l (left_branch_val a)) 
                                   (Application r (right_branch_val a))) in
                reduction_rules new_expr recursion_bound sb
              | Fix type fname argname fexpr => 
                let bind_fun_expr := (beta_reduction 
                                         argname a (beta_reduction fname f fexpr)) in 
                (match recursion_bound with 
                   | 0 => None (* failed, bottom-out *)
                   | S n => reduction_rules bind_fun_expr n sb
                 end)
              | _ => None
            end)
         | Let_Bind lname lvalue lexpr => reduction_rules (beta_reduction lname lvalue lexpr) recursion_bound sb
         | If1 test thendo elsedo => 
           (match test with
              | Integer t val => if beq_nat val 1 then reduction_rules thendo recursion_bound sb 
                                 else reduction_rules elsedo recursion_bound sb
              | Value_Evaluation_Pair t l r=> 
                let new_expr := (Expression_Evaluation_Pair (If1 l (left_branch thendo) (left_branch elsedo)) 
                                                            (If1 r (right_branch thendo) (right_branch elsedo))) in
                reduction_rules new_expr recursion_bound sb
              | _ => reduction_rules elsedo recursion_bound sb
            end
           ) 
         | Expression_Evaluation_Pair l r => 
           let new_left := (reduction_rules l recursion_bound sb) in
           let new_right := (reduction_rules r recursion_bound sb) in
           (match new_left with
              | None => None
              | Some nl => (match new_right with 
                              | None => None
                              | Some nr => 
                                let t := (get_type nl) in
                                Some (Value_Evaluation_Pair t nl nr)
                            end)
            end)
                                                                   
       end )
    | 0 => None (* we will prove that this case never fires *)
  end.


Fixpoint reduction_rules_env (env : environment) (expr : expression) (recursion_bound : nat) (step_bound : nat) : (option value) :=
  match step_bound with 
    | S sb => 
      (match expr with 
         | Value v => Some (reduce_identifier v env)
         | Application f a => 
           (match (reduce_identifier f env) with
              | Value_Evaluation_Pair t l r => 
                let new_expr := (Expression_Evaluation_Pair 
                                   (Application l (left_branch_val a)) 
                                   (Application r (right_branch_val a))) in
                reduction_rules_env env new_expr recursion_bound sb
              | Fix type fname argname fexpr => 
                let new_env := (env_cons fname f 
                                         (env_cons argname a env)) in
                (match recursion_bound with 
                   | 0 => None (* failed, bottom-out *)
                   | S n => reduction_rules_env new_env fexpr n sb
                 end)
              | _ => None
            end)
         | Let_Bind lname lvalue lexpr => reduction_rules_env (env_cons lname lvalue env) lexpr recursion_bound sb
         | If1 test thendo elsedo => 
           (match (reduce_identifier test env) with
              | Integer t val => if beq_nat val 1 then reduction_rules_env env thendo recursion_bound sb 
                                 else reduction_rules_env env elsedo recursion_bound sb
              | Value_Evaluation_Pair t l r=> 
                let new_expr := (Expression_Evaluation_Pair (If1 l (left_branch thendo) (left_branch elsedo)) 
                                                            (If1 r (right_branch thendo) (right_branch elsedo))) in
                reduction_rules_env env new_expr recursion_bound sb
              | _ => reduction_rules_env env elsedo recursion_bound sb
            end
           ) 
         | Expression_Evaluation_Pair l r => 
           let new_left := (reduction_rules_env env l recursion_bound sb) in
           let new_right := (reduction_rules_env env r recursion_bound sb) in
           (match new_left with
              | None => None
              | Some nl => (match new_right with 
                              | None => None
                              | Some nr => 
                                let t := (get_type nl) in
                                Some (Value_Evaluation_Pair t nl nr)
                            end)
            end)
                                                                   
       end )
    | 0 => None (* we will prove that this case never fires *)
  end.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : expression -> expression -> Prop :=
| Beta_Reduction_R : forall t f x e v,
                       (Application (Fix t f x e) v) ==> (beta_reduction x v (beta_reduction f (Fix t f x e) e))
| If1_R : forall t e1 e2,
           (If1 (Integer t 1) e1 e2) ==> e1
| Ifelse_R : forall t v e1 e2,
               (not (v = (Integer t 1))) -> 
               (If1 v e1 e2) ==> e2
| Let_R : forall x v e,
            (Let_Bind x v e) ==> (beta_reduction x v e)
| Lift_App_R : forall t v1 v2 v,
                 (Application (Value_Evaluation_Pair t v1 v2) v)
                   ==> 
                   (Expression_Evaluation_Pair (Application v1 (left_branch_val v)) (Application v1 (right_branch_val v)))
| Lift_Case_R : forall t vl vr e1 e2,
                  (If1 (Value_Evaluation_Pair t vl vr) e1 e2) 
                    ==> 
                    (Expression_Evaluation_Pair 
                       (If1 vl (left_branch e1) (left_branch e2))
                       (If1 vr (right_branch e1) (right_branch e2)))
| Bracket_R : forall e1 e2 e1' e2',
                e1 ==> e1' -> 
                e2 ==> e2' ->
                Expression_Evaluation_Pair e1 e2 ==> Expression_Evaluation_Pair e1' e2'
  where " t '==>' t' " := (step t t').

Definition stepmany := refl_step_closure step.
Notation " t '==>*' t' ":= (stepmany t t') (at level 40).

Lemma leftbranch_beta_comm : forall var bound expr, 
         left_branch (beta_reduction var bound expr) = beta_reduction var (left_branch_val bound) (left_branch expr)
with leftbranch_beta_comm_val : forall var bound val,
         left_branch_val (beta_reduction_values var bound val) = 
         beta_reduction_values var (left_branch_val bound) (left_branch_val val).
Proof.
  Case "expr". clear leftbranch_beta_comm.
  intros.
  induction expr; try (simpl; f_equal; auto).
   SCase "Let". destruct (names_equal v var); trivial.   

  Case "values". clear leftbranch_beta_comm_val.
  intros. induction val; try solve [ simpl; f_equal; auto ].
   SCase "Identifier". simpl; destruct (names_equal v var); trivial.
   SCase "Fixpoint". 
     simpl. destruct (names_equal v var); destruct (names_equal v0 var); 
            try trivial; try (simpl; f_equal; trivial). Qed.



Lemma left_branch_idem : forall e, (left_branch (left_branch e)) = (left_branch e)
  with left_branch_val_idem : forall v, (left_branch_val (left_branch_val v)) = (left_branch_val v).
  Case "expr". clear left_branch_idem.
  induction e; simpl;
    repeat first [ rewrite left_branch_val_idem | rewrite IHe | rewrite IHe1 | rewrite IHe2 ]; trivial.

  Case "values". clear left_branch_val_idem.
  induction v; simpl; try (rewrite left_branch_idem); auto.  
Qed.

  
Lemma lemma_2_l:  forall e e1, e ==> e1 -> (left_branch e) ==>* (left_branch e1).
Proof.
  intros e. functional induction (left_branch e).
  Case "Expression_Evaluation_Pair".
    intros e1 Hreduces.
    inversion Hreduces; subst.
    simpl. auto. 
  Case "Value".
    intros e1 Hreduces. inversion Hreduces.
  Case "Application".
    intros e1 Hreduces.    
    inversion Hreduces; subst.
    SCase "Beta_Reduction_R".
      rewrite leftbranch_beta_comm.
      rewrite leftbranch_beta_comm. simpl. 
    SCase "Lift_App_R".
      simpl.
      rewrite left_branch_val_idem. 

  (app (pair thing1 thing2) arg)  ==>  (pair (thing1 arg) (thing2 arg))
     v                                   v
  (app thing1 arg)  ==>                (thing1 arg)

(pair 

    subst.

simpl.
auto.
 apply IHe0.
assumption.

    apply IHe0.


  induction e; intros enew Hreduces.
  Case "value".
    solve [ inversion Hreduces ].
  Case "application".
    inversion Hreduces; subst.
simpl.

    solve by inversion.


  intros e e1 Hreduces.
  induction e.
  Case "Value".
    destruct v; solve by inversion.
  Case "Application".
    destruct v; try solve by inversion.
      SCase "fix".
      simpl. SearchAbout left_branch. inversion Hreduces. subst.
      

  induction Hreduces.  
inversion H. 
  Case "Beta_Reduction". 
  (* how do i run it *)