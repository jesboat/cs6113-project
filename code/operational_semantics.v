Require Export SfLib.
Require Export syntax.
Require Import Setoid.
Require Import Classical. (* :( *)

Close Scope signature_scope. (* conflicts with our `==>` *)

Inductive environment : Set :=
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

(*
Reserved Notation " t '==>' t' " (at level 40).
*)

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

Notation multistep := (multi step).
Notation " t '==>*' t' ":= (multistep t t') (at level 40).

Lemma step_implies_stepmany : forall t t', t ==> t' -> t ==>* t'.
Proof.
  intros.
  eapply multi_step. eassumption. econstructor.
Qed.
  
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
    SCase "right stepped". simpl. constructor.
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
      rewrite left_branch_val_idem.  econstructor.
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
  | is_value_pair : forall v1 v2,
      is_value v1 -> is_value v2 ->
      is_value (Expression_Evaluation_Pair v1 v2).

Definition stuck (t:expression) : Prop :=
  (normal_form step) t /\ ~ is_value t.

Lemma values_dont_step : forall e, is_value e -> ~exists e', e ==> e'.
Proof.
  induction e; intros Hisv; inversion Hisv; subst.
  Case "Value".
    intros Hsteps. inversion_clear Hsteps as [e' He'].
    inversion He'.
  Case "E_E_P of values".
    intros Hsteps. inversion_clear Hsteps as [e' He'].
    inversion He'; subst.
      specialize (IHe1 H1); contradict IHe1; eauto.
      specialize (IHe2 H2); contradict IHe2; eauto.
Qed.

Lemma steppers_not_stuck : forall e e', e ==> e' -> ~stuck e.
Proof.
  intros e e' Hred Hstuck. inversion_clear Hstuck as [Hnf Hnonval].
  unfold normal_form in Hnf; contradict Hnf. eauto.
Qed.

Lemma steppers_not_stuck' : forall e, (exists e', e ==> e') -> ~stuck e.
Proof.
  intros e He' Hstuck. inversion_clear Hstuck as [Hnf Hnonval].
  unfold normal_form in Hnf. contradiction.
Qed.

Lemma eep_steps_pieces_step : forall e1 e2 e',
    (Expression_Evaluation_Pair e1 e2) ==> e'
    -> (exists e1', e1 ==> e1')
    \/ (exists e2', e2 ==> e2').
Proof.
  intros e1 e2 e' Hsteps; inversion_clear Hsteps.
  Case "e1 steps". left. eauto.
  Case "e2 steps". right. eauto.
Qed.

Lemma eep_steps_pieces_step' : forall e1 e2,
    (exists e', (Expression_Evaluation_Pair e1 e2) ==> e')
    -> (exists e1', e1 ==> e1')
    \/ (exists e2', e2 ==> e2').
Proof.
  intros e1 e2 [e' Hsteps]; inversion_clear Hsteps.
  Case "e1 steps". left. eauto.
  Case "e2 steps". right. eauto.
Qed.

Theorem stuck_or_not : forall e, stuck e \/ ~stuck e.
Proof.
  induction e.
  Case "value".
    right. apply values_not_stuck.
  Case "application".
    destruct v;
      try solve [ left; split; intro; solve by inversion 2 ].
    SCase "Fix".
      right. eapply steppers_not_stuck. econstructor.
    SCase "Value_Evaluation_Pair".
      right. eapply steppers_not_stuck. econstructor.
  Case "Let".
    right. eapply steppers_not_stuck. econstructor.
  Case "If1".
    right.
    destruct v;
      try solve [ eapply steppers_not_stuck; econstructor; congruence ].
    SCase "intever".
      compare n 1; intro Hn1; try (subst n);
        solve [ eapply steppers_not_stuck; econstructor; congruence ].
    SCase "VEP".
      eapply steppers_not_stuck. eapply Lift_If_R.
  Case "EEP".
    apply Classical_Prop.classic. (* XXX necessary? *)
Qed.

Function left_branch_1 (e : expression) :=
  match e with
  | Expression_Evaluation_Pair e1 e2 => e1
  | Value v => Value (left_branch_1_val v)
  | Application f a => Application (left_branch_1_val f) (left_branch_1_val a)
  | Let_Bind nm vl e => Let_Bind nm (left_branch_1_val vl) (left_branch_1 e)
  | If1 t b1 b2 => If1 (left_branch_1_val t) (left_branch_1 b1) (left_branch_1 b2)
  end

with left_branch_1_val (val : value) {struct val} :=
  match val with
    | Identifier t vn => val
    | Integer _ _ => val
    | Fix t f a b => Fix t f a (left_branch_1 b)
    | Value_Evaluation_Pair t l r => l
  end.

Function right_branch_1 (e : expression) :=
  match e with
  | Expression_Evaluation_Pair e1 e2 => e2
  | Value v => Value (right_branch_1_val v)
  | Application f a => Application (right_branch_1_val f) (right_branch_1_val a)
  | Let_Bind nm vl e => Let_Bind nm (right_branch_1_val vl) (right_branch_1 e)
  | If1 t b1 b2 => If1 (right_branch_1_val t) (right_branch_1 b1) (right_branch_1 b2)
  end

with right_branch_1_val (val : value) {struct val} :=
  match val with
    | Identifier t vn => val
    | Integer _ _ => val
    | Fix t f a b => Fix t f a (right_branch_1 b)
    | Value_Evaluation_Pair t l r => r
  end.

Function paircount (e : expression) :=
  match e with
  | Expression_Evaluation_Pair e1 e2 => 1 + paircount e1 + paircount e2
  | Value v => paircount_val v
  | Application f a => paircount_val f + paircount_val a
  | Let_Bind nm vl e => paircount_val vl + paircount e
  | If1 t b1 b2 => paircount_val t + paircount b1 + paircount b2
  end

with paircount_val (val : value) {struct val} :=
  match val with
    | Identifier t vn => 0
    | Integer _ _ => 0
    | Fix t f a b => paircount b
    | Value_Evaluation_Pair t l r => 1 + paircount_val l + paircount_val r
  end.

Lemma leftbranch1_leftbranch : forall e,
    left_branch (left_branch_1 e) = left_branch e
with  leftbranch1_leftbranch_val : forall v,
    left_branch_val (left_branch_1_val v) = left_branch_val v.
Proof.
  Case "expr". clear leftbranch1_leftbranch.
    induction e;
        simpl;
        repeat (rewrite leftbranch1_leftbranch_val);
        repeat (rewrite IHe);
        repeat (rewrite IHe1);
        repeat (rewrite IHe2);
        reflexivity.
  Case "val". clear leftbranch1_leftbranch_val.
    induction v;
        simpl;
        try (rewrite leftbranch1_leftbranch);
        reflexivity.
Qed.

Lemma paircount_leftbranch : forall e,
        paircount (left_branch e) = 0
 with paircount_leftbranch_val : forall v,
        paircount_val (left_branch_val v) = 0.
Proof.
  Case "expr". clear paircount_leftbranch.
    induction e;
        simpl;
        repeat (rewrite paircount_leftbranch_val);
        repeat (rewrite IHe);
        repeat (rewrite IHe1);
        repeat (rewrite IHe2);
        trivial.

  Case "val". clear paircount_leftbranch_val.
    induction v;
        simpl;
        repeat (rewrite paircount_leftbranch);
        trivial.
Qed.

Lemma paircount0_leftbranch : forall e,
      paircount e = 0 -> left_branch e = e
with paircount0_leftbranch_val : forall v,
      paircount_val v = 0 -> left_branch_val v = v.
Proof.
  clear paircount0_leftbranch.
  induction e;
      intros; simpl in *.
  Case "value".
    rewrite paircount0_leftbranch_val. trivial. trivial.
  Case "application".
    assert (left_branch_val v = v)
        by (apply paircount0_leftbranch_val; omega).
    assert (left_branch_val v0 = v0)
        by (apply paircount0_leftbranch_val; omega).
    congruence.
  Case "let".
    assert (left_branch_val v0 = v0)
        by (apply paircount0_leftbranch_val; omega).
    assert (left_branch e = e)
        by (apply IHe; omega).
    congruence.
  Case "if".
    assert (left_branch_val v = v)
        by (apply paircount0_leftbranch_val; omega).
    assert (left_branch e1 = e1)
        by (apply IHe1; omega).
    assert (left_branch e2 = e2)
        by (apply IHe2; omega).
    congruence.
  Case "pair".
    discriminate.

  clear paircount0_leftbranch_val.
  induction v;
      intros; try reflexivity.
  Case "fix".
    simpl in *. rewrite paircount0_leftbranch; trivial.
  Case "pir".
    discriminate.
Qed.

Lemma paircount0_leftbranch1 : forall e,
      paircount e = 0 -> left_branch_1 e = e
with paircount0_leftbranch1_val : forall v,
      paircount_val v = 0 -> left_branch_1_val v = v.
Proof.
    clear paircount0_leftbranch1.
    induction e;
        intros; simpl in *;
        repeat (rewrite paircount0_leftbranch1_val);
        repeat (rewrite IHe);
        repeat (rewrite IHe1);
        repeat (rewrite IHe2);
        try solve [ reflexivity | omega ].

    clear paircount0_leftbranch1_val.
    induction v;
        intros; simpl in *;
        repeat (rewrite paircount0_leftbranch1);
        try solve [ reflexivity | omega ].
Qed.

Lemma paircount_leftbranch_1 : forall e, paircount e = 0
        \/ paircount (left_branch_1 e) < paircount e
 with paircount_leftbranch_1_val : forall v, paircount_val v = 0
        \/ paircount_val (left_branch_1_val v) < paircount_val v.
Proof.
  Case "expr". clear paircount_leftbranch_1.
    induction e;
      try (destruct (paircount_leftbranch_1_val v));
      try (destruct (paircount_leftbranch_1_val v0));
      try (destruct IHe); try (destruct IHe1); try (destruct IHe2);
      simpl in *;
      repeat
        match goal with
          | H : paircount?e = 0 |- _ =>
              let H_left := fresh H "_left" in
              let H_left1 := fresh H "_left1" in
              assert (left_branch e = e) as H_left
                by (apply paircount0_leftbranch; auto);
              assert (left_branch_1 e = e) as H_left1
                by (apply paircount0_leftbranch1; auto);
              repeat (simpl in *;
                      first [ rewrite H
                            | rewrite H_left
                            | rewrite H_left1 ]);
              simpl in *;
              clear H; clear H_left; clear H_left1
          | H : paircount_val ?v = 0 |- _ =>
              let H_left := fresh H "_left" in
              let H_left1 := fresh H "_left1" in
              assert (left_branch_val v = v) as H_left
                by (apply paircount0_leftbranch_val; auto);
              assert (left_branch_1_val v = v) as H_left1
                by (apply paircount0_leftbranch1_val; auto);
              repeat (simpl in *;
                      first [ rewrite H
                            | rewrite H_left
                            | rewrite H_left1 ]);
              simpl in *;
              clear H; clear H_left; clear H_left1
        end;
      try solve [ omega ].

  Case "val". clear paircount_leftbranch_1_val.
    induction v;
      simpl in *;
      try (destruct (paircount_leftbranch_1 e));
      omega.
Qed.

Lemma pairsize_ind (P : expression -> Prop) :
    (forall e, paircount e = 0 -> P e) ->
    (forall e, (forall e', paircount e' < paircount e -> P e') -> P e) ->
    forall e, P e.
Proof.
  intros when0 whenS.

  intro e. remember (paircount e) as n. generalize dependent e.

  pose proof
      (fun n => lt_wf_ind n (fun n => forall e, n = paircount e -> P e)).
  specialize (H n). apply H. clear H. clear n.

  intros n H1 e Hsize.
  destruct n eqn:Hn.
  Case "n=0". apply when0. auto.
  Case "n>0".
    apply whenS. intros e'. rewrite <- Hsize. intro Hsize2.
    apply H1 with (m := paircount e'); omega.
Qed.

Lemma lemma_3l_nopair : forall e,
    (forall a b, e <> Expression_Evaluation_Pair a b) ->
    (stuck e) -> (stuck (left_branch e)) /\ (stuck (right_branch e)).
Proof.
  induction e; intros Hnonpair Hstuck.
  Case "Value".
    apply values_not_stuck in Hstuck; contradiction.
  Case "Application".
    inversion Hstuck as [Hnf Hnonv]. unfold normal_form in *.
    destruct v; simpl. (* destructing the rator *)
    SCase "Identifier".
      split; split; intro; solve by inversion 2.
    SCase "Integer".
      split; split; intro; solve by inversion 2.
    SCase "Fix".
      contradict Hnf. eexists. econstructor.
    SCase "Pair".
      contradict Hnf. eexists. econstructor.
  Case "Let".
    inversion Hstuck as [Hnf Hnonv]. unfold normal_form in *.
    contradict Hnf. eexists. econstructor.
  SCase "If".
    inversion Hstuck as [Hnf Hnonv]. unfold normal_form in *.
    contradict Hnf.
    destruct v;
        try solve [ eexists; econstructor; congruence ].
    SSCase "conditional was integer".
      compare n 1; intro; subst;
          try solve [ eexists; econstructor; congruence ].
    SSCase "conditional was pair".
      eexists. eapply Lift_If_R.
  Case "Expression_Evaluation_Pair".
    specialize (Hnonpair e1 e2); congruence.
Qed.

Lemma stuck_or_steps_or_value : forall e,
  stuck e \/ is_value e \/ exists e', e ==> e'.
Proof.
  intros e.
  destruct (stuck_or_not e) as [H | H];
      unfold stuck in *; unfold normal_form in *;
      tauto.
Qed.

Lemma pair_stuck_parts_stuck : forall e1 e2,
  (stuck (Expression_Evaluation_Pair e1 e2)) -> stuck e1 \/ stuck e2.
Proof.
  intros e1 e2 Hstuck; simpl.
  inversion_clear Hstuck as [Hnf Hnonval].
  destruct (stuck_or_steps_or_value e1) as [He1 | [He1 | [e1' He1]]];
    destruct (stuck_or_steps_or_value e2) as [He2 | [He2 | [e2' He2]]];
    try solve [
        tauto (* at least one stuck *)
      | contradict Hnonval; constructor; trivial (* both values *)
      | unfold normal_form in Hnf; contradict Hnf;
        eexists; solve [ eapply Bracket_left_R; eauto
                       | eapply Bracket_right_R; eauto ]].
Qed.

Lemma lemma_3l_pair : forall e e1 e2,
    e = Expression_Evaluation_Pair e1 e2 ->
    (stuck e) -> (stuck (left_branch_1 e)) \/ (stuck (right_branch_1 e)).
Proof.
  intros. subst. simpl. apply pair_stuck_parts_stuck. assumption.
Qed.

Definition lemma_3_stmt := forall e, (stuck e) -> (stuck (left_branch e))  \/ (stuck (right_branch e)).

Lemma lemma_3l_false : ~ lemma_3_stmt.
Proof.
  pose (Integer (Int_t High_Label) 4) as four.
  pose (Value four) as valu.
  pose (Application four four) as stk.
  pose (Expression_Evaluation_Pair
        (Expression_Evaluation_Pair valu valu)
        (Expression_Evaluation_Pair stk valu))  as nasty.

  assert (stuck nasty) as Hstuck.
    split.
      intro Hsteps; inversion Hsteps; solve by inversion 3.
      intro Hisval; inversion Hisval; solve by inversion 2.

  intros lemma3.
  destruct (lemma3 nasty Hstuck) as [H | H];
      simpl in H; apply values_not_stuck in H; contradiction.
Qed.

Lemma lemma_3 : forall e, (stuck e) -> (stuck (left_branch e))  \/ (stuck (right_branch e)).
Proof.
  apply (pairsize_ind
    (fun e => stuck e -> stuck (left_branch e) \/ stuck (right_branch e))).
  Case "size 0".
    intros e Hpaircount Hstuck.
    rewrite paircount0_leftbranch; auto.
  Case "size > 0".
    intros e IHfewerpairs Hstuck.
    destruct e;
      try solve [ left;
                  apply lemma_3l_nopair;
                  intros; solve [ congruence | trivial ] ].
    SCase "Pair".
      apply pair_stuck_parts_stuck in Hstuck.
      inversion_clear Hstuck as [He1_stuck | He2_stuck]; [left | right].
      simpl in *.

      destruct e1;
        try solve [ apply lemma_3l_nopair; intros;
                    solve [ congruence |  trivial ]].
        apply pair_stuck_parts_stuck in He1_stuck.
        inversion_clear He1_stuck as [He11_stuck | He12_stuck].
        simpl in *.
        destruct e1_1;
          try solve [ apply lemma_3l_nopair; intros;
                      solve [ congruence |  trivial ]].
        apply pair_stuck_parts_stuck in He11_stuck.
        inversion_clear He11_stuck as [He111_stuck | He122_stuck].
        simpl in *.

admit.
simpl.



      assert (paircount e1 < S (paircount e1 + paircount e2)) as tmp1
          by omega.
      pose proof (IHfewerpairs e1 tmp1 He1_stuck).
      pose proof (lemma_3l_nopair e1).

      inversion_clear Hstuck as [Hnf Hval].
      destruct (stuck_or_not e1) as [He1 | He1];
        destruct (stuck_or_not e2) as [He2 | He2].
      SSCase "both stuck".
        destruct e1.
        try solve [ apply lemma_3l_micro;
                    intros; solve [ congruence | trivial ] ].
        admit.
      SSCase "e2 not stuck".
        apply not_and_or in He2.
        inversion_clear He2 as [He2_steps | He2_val].
        SSSCase "e2 steps".
          apply NNPP in He2_steps.
          inversion_clear He2_steps as [e2' He2'].
          unfold normal_form in Hnf. contradict Hnf.
          eexists. eapply Bracket_right_R. eassumption.
        SSSCase "e2 value".
      apply not_and_or in He1.
      apply not_and_or in He2.
      inversion_clear He1 as [He1_steps | He1_val];
          repeat (match goal with
                    | H : _ |- _ => apply NNPP in H
                  end).
      SCase "both step".
        unfold normal_form in Hnf. contradict Hnf.
        inversion_clear He1_steps as [e1' He1'].
        eexists. eapply Bracket_left_R. eassumption.
      SCase "e1 steps, e2 value".
        unfold normal_form in Hnf. contradict Hnf.
        inversion_clear He1_steps as [e1' He1'].
        eexists. eapply Bracket_left_R. eassumption.
      SCase "e1 value, e2 steps".
      SCase "both values".
        contradict Hval. constructor; trivial.
      Qed.
 
; contradict Hnf. econstructor. econstructor.

  apply lemma_3_micro.

  Case "E_E_P".
  try solve [ apply lemma_3_micro; try congruence ].
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
