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
                let bind_fun_expr := (subst 
                                         argname a (subst fname f fexpr)) in 
                (match recursion_bound with 
                   | 0 => None (* failed, bottom-out *)
                   | S n => reduction_rules bind_fun_expr n sb
                 end)
              | _ => None
            end)
         | Let_Bind lname lvalue lexpr => reduction_rules (subst lname lvalue lexpr) recursion_bound sb
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
                       (Application (Fix t f x e) v) ==> (subst x v (subst f (Fix t f x e) e))
| If1_R : forall t e1 e2,
           (If1 (Integer t 1) e1 e2) ==> e1
| Ifelse_R : forall v e1 e2,
                 (forall t, v <> (Integer t 1)) ->
                 (forall a b c, v <> Value_Evaluation_Pair a b c) ->
                 (If1 v e1 e2) ==> e2
| Let_R : forall x v e,
            (Let_Bind x v e) ==> (subst x v e)
| Lift_App_R : forall t v1 v2 v,
                 (Application (Value_Evaluation_Pair t v1 v2) v)
                   ==> 
                   (Expression_Evaluation_Pair (Application v1 (left_branch_val v)) (Application v1 (right_branch_val v)))
| Lift_If_R : forall t vl vr e1 e2,
                  (If1 (Value_Evaluation_Pair t vl vr) e1 e2) 
                    ==> 
                    (Expression_Evaluation_Pair 
                       (If1 vl (left_branch e1) (left_branch e2))
                       (If1 vr (right_branch e1) (right_branch e2)))
| Bracket_left_R : forall e1 e2 e1',
                e1 ==> e1' -> 
                Expression_Evaluation_Pair e1 e2 ==> Expression_Evaluation_Pair e1' e2
| Bracket_right_R : forall e1 e2 e2',
                e2 ==> e2' -> 
                Expression_Evaluation_Pair e1 e2 ==> Expression_Evaluation_Pair e1 e2'
  where " t '==>' t' " := (step t t').

Definition stepmany := refl_step_closure step.
Notation " t '==>*' t' ":= (stepmany t t') (at level 40).

Lemma step_implies_stepmany : forall t t', t ==> t' -> t ==>* t'.
  Proof.
    intros.
    assert (t ==>* t) by apply rsc_refl.
    apply (rsc_step step t t'); try assumption; try apply rsc_refl.
  Qed.
  
Lemma stepmany_refl : forall t, t ==>* t.
  Proof. intros; apply rsc_refl. Qed.


(*  Lemma step_many_and_difference_implies_step : 
    forall t t', (not (t = t')) -> t ==>* t' -> exists mid, t ==>* mid -> mid ==> t'.
    Proof.
      intros. exists t. intros. induction H0. contradict H; reflexivity. 
*)
      
    
    
Lemma leftbranch_beta_comm : forall var bound expr, 
         left_branch (subst var bound expr) = subst var (left_branch_val bound) (left_branch expr)
with leftbranch_beta_comm_val : forall var bound val,
         left_branch_val (subst_values var bound val) = 
         subst_values var (left_branch_val bound) (left_branch_val val).
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
  
Lemma left_branch_still_unequal: forall t v, t <> v -> 
                         (forall typ f x e, t <> Fix typ f x e) ->
                         (forall a b c, t <> (Value_Evaluation_Pair a b c)) -> 
                         left_branch_val t <> v.
  Proof. 
     Case "proving assertion". intros. induction t; try (simpl; assumption). pose proof (H0 t v0 v1 e) as hwrong. contradict hwrong; reflexivity. pose proof (H1 t1 t2 t3) as hwrong. contradict hwrong; reflexivity.  Qed.

Lemma left_branch_still_not_integer: forall t typ i, t <> (Integer typ i) -> 
                                                     (forall a b c, t <> (Value_Evaluation_Pair a b c)) -> 
                                                     left_branch_val t <>  (Integer typ i).
Proof.
  intros.
  destruct t; simpl; intros; congruence.
Qed.

Lemma left_branch_still_not_pair: forall t a b c,
                                    (forall a0 b0 c0, t <> Value_Evaluation_Pair a0 b0 c0)
-> left_branch_val t <> (Value_Evaluation_Pair a b c).
Proof.
  intros.
  destruct t; simpl; intros; congruence.
Qed.
   

Lemma lemma_2_l:  forall e e1, e ==> e1 -> (left_branch e) ==>* (left_branch e1).
Proof.
  intros e. functional induction (left_branch e).
  Case "Expression_Evaluation_Pair".
    intros e1 Hreduces. inversion Hreduces; subst.
    SCase "left stepped". simpl. apply IHe0. assumption.
    SCase "right stepped". simpl. apply stepmany_refl.
  Case "Value".
    intros e1 Hreduces. inversion Hreduces.
  Case "Application".
    intros e1 Hreduces.    
    inversion Hreduces; subst.
    SCase "Beta_Reduction_R".
      rewrite leftbranch_beta_comm.
      rewrite leftbranch_beta_comm. simpl. 
      pose proof (Beta_Reduction_R t f0 x (left_branch e) (left_branch_val a)) as BR. 
      apply step_implies_stepmany in BR. apply BR.
    SCase "Lift_App_R".
      simpl.
      rewrite left_branch_val_idem.  apply stepmany_refl.
  Case "Let_Bind".
    intros e1 Hreduces. 
    inversion Hreduces; subst.
    SCase "let". 
     pose proof (Let_R nm (left_branch_val vl) (left_branch e)) as LR.
     apply step_implies_stepmany in LR. rewrite leftbranch_beta_comm. assumption.
  Case "If1".
    intros e1 Hreduces.  inversion Hreduces; subst.
    SCase "0". simpl. pose proof (If1_R t0 (left_branch e1) (left_branch b2)) as IfR.
     apply step_implies_stepmany in IfR. assumption.
    SCase "nonzero".
    simpl.
    pose proof (Ifelse_R (left_branch_val t) (left_branch b1) (left_branch e1)) as IfR.
    apply step_implies_stepmany.
    apply IfR. 
    intros. pose proof (H3 t0) as newH3. apply (left_branch_still_not_integer t t0 1) in newH3. assumption.
    assumption. 
    intros. apply left_branch_still_not_pair. assumption.
    SCase "lift".
    simpl. rewrite left_branch_idem. rewrite left_branch_idem. constructor. Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.


Inductive is_value : expression -> Prop :=
  | is_value_v : forall v, is_value (Value v)
  | is_value_pair : forall v1 v2, is_value (Expression_Evaluation_Pair (Value v1) (Value v2)).

Definition stuck (t:expression) : Prop :=
  (normal_form step) t /\ ~ is_value t.

Require Classical.

Lemma stuck_or_not : forall e, stuck e \/ ~ stuck e.
Proof.
  intros. apply Classical_Prop.classic. Qed.

Lemma lemma_3_micro : forall e,
                        (forall a b, e <> Expression_Evaluation_Pair a b) ->
                        (stuck e) -> (stuck (left_branch e))  \/ (stuck (right_branch e)).
  Proof.
    intros e Hnotpair H.
    intros. destruct e. 
    Case "value".
      unfold stuck in H. inversion  H. contradict H1. constructor. 
    Case "Application".
      unfold stuck in H. inversion H. unfold normal_form in H0. 
      destruct v;
        try solve [ simpl; left; unfold stuck; split;
                    [ intro contra; solve by inversion 2
                    | intro contra; solve by inversion ] ];
            contradict H0; repeat econstructor.
    Case "Let_Bind". unfold stuck in H. inversion H. unfold normal_form in H0. contradict H0.
     econstructor. econstructor. 
    Case "If". unfold stuck in H. inversion H. unfold normal_form in H0. contradict H0. 
     destruct v;
        try solve [econstructor; apply Ifelse_R; intros; discriminate].
      SCase "Integer". compare n 1; intro Hn1; subst.
        SSCase "true". econstructor. apply If1_R.
        SSCase "false". econstructor. apply Ifelse_R. intros. congruence. intros; congruence.
      SCase "Value_Evaluation_Pair". econstructor. apply Lift_If_R. 
    Case "Expression_Evaluation_Pair". 
      specialize (Hnotpair e1 e2). congruence.
Qed.


Lemma lemma_3 : forall e, (stuck e) -> (stuck (left_branch e))  \/ (stuck (right_branch e)).
Proof.
  induction e;
    try solve [ apply lemma_3_micro; try congruence ].
  Case "E_E_P".
    intro Hstuck; inversion Hstuck as [Hnormal Hnonvalu].
Admitted.

(*
    destruct (stuck_or_not e1); destruct (stuck_or_not e2).
    SCase "both".
      simpl.
      specialize (IHe1 H). specialize (IHe2 H0).
      inversion IHe1; inversion IHe2; try tauto.
      assert (forall a b, left_branch e1 <> Expression_Evaluation_Pair a b) as Hwecouldprovethis by admit.
      destruct (stuck_or_not (left_branch e1)).
      SSCase "left(e1) stuck". tauto.
      SSCase "left(e1) not stuck". admit.
    SCase "e2 is not stuck".
      unfold stuck in H0.
      unfold normal_form in Hnormal.
      contradict Hnormal.
      eexists.
      apply Classical_Prop.not_and_or in H0.

      
      contradict H0. contradict H0.

      inversion H0.
      unfold normal_form in H1.
      apply Classical_Prop.NNPP in H1.
      inversion 

        unfold stuck in H3. 
apply Classical_Prop.not_and_or in H3.
inversion H3.
unfold normal_form in H4.
apply Classical_Prop.NNPP in H4.
inversion H4.
unfold stuck in H.
contradict H.
apply Classical_Prop.or_not_and.
left.
unfold normal_form. intro blah; contradict blah.
inversion H5; subst. rewrite <- H6 in *.
destruct e1; try solve [ simpl in *; congruence ].
  (* foo *) simpl in *. 
simpl in H6. inversion H6. subst.



econstructor. econstructor. 


left. 

unfold normal_form. intro blah; contradict blah. 


contradict 

     pose proof (lemma_3_micro (left_branch e1)).

      

    unfold stuck

    Case "e1 stuck".
    unfold normal_form in Hnormal.


  apply lemma_3_micro; try congruence.
  




simpl. unfold stuck in H. inversion H. 
      unfold normal_form in H0.
      destruct (stuck_or_not e1).
      SCase "e1 stuck". apply IHe1 in H2. tauto.


*)
