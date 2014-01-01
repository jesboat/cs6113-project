Require Export SfLib.
Require Export syntax.

Module environments_eval.

Inductive environment : Set :=
| Empty_Env : environment
| Env : (variable_name * value) -> environment -> environment.

Fixpoint extract_num (var : variable_name) : nat :=
  match var with
    | Var n => n
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

End environments_eval.


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
                   (Expression_Evaluation_Pair (Application v1 (left_branch_val v)) (Application v2 (right_branch_val v)))
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

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Inductive is_value : expression -> Prop :=
  | is_value_v : forall v, is_value (Value v)
  | is_value_pair : forall v1 v2, is_value (Expression_Evaluation_Pair (Value v1) (Value v2)).

Definition stuck (t:expression) : Prop :=
  (normal_form step) t /\ ~ is_value t.

Lemma step_implies_stepmany : forall t t', t ==> t' -> t ==>* t'.
Proof.
  intros.
  eapply multi_step. eassumption. econstructor.
Qed.

Lemma values_dont_step : forall e, is_value e -> ~exists e', e ==> e'.
Proof.
  induction e; intros Hisv; inversion Hisv; subst.
  Case "Value".
    intros Hsteps. solve by inversion 2.
  Case "E_E_P of values".
    intros Hsteps. solve by inversion 3.
Qed.

Lemma values_not_stuck : forall v, is_value v -> ~stuck v.
Proof.
  intros. unfold stuck. tauto.
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

Lemma step_many_and_difference_implies_firststep :
    forall t t', (not (t = t')) -> t ==>* t' ->
       exists mid, t ==> mid /\ mid ==>* t'.
Proof.
  intros t t' Hne Hmulti.
  destruct Hmulti.
  Case "none". exfalso. congruence.
  Case "some".
    eexists. split; eassumption.
Qed.

Lemma step_many_and_difference_implies_laststep :
    forall t t', (not (t = t')) -> t ==>* t' ->
       exists mid, t ==>* mid /\ mid ==> t'.
Proof.
  intros t t' Hne Hmulti.
  induction Hmulti.
  Case "none". exfalso; congruence.
  Case "some".
    intros.
    destruct (eq_expression_dec y z) as [Hyz | Hyz].
    SCase "y=z". subst. exists x. split. constructor. assumption.
    SCase "y<>z".
      destruct (IHHmulti Hyz) as [mid [Hymid Hmidz]].
      exists mid. split. econstructor; eassumption. assumption.
Qed.

Theorem pairfree_subst_e : forall i r e,
            pairfree_v r -> pairfree_e e -> pairfree_e (subst i r e)
   with pairfree_subst_v : forall i r v,
            pairfree_v r -> pairfree_v v -> pairfree_v (subst_values i r v).
Proof.
  Case "e". clear pairfree_subst_e.
    intros i r; induction e; intros Hpairfree_bound Hpairfree_in;
        simpl in *; firstorder.
    SCase "Let_Bind". SSCase "body".
      destruct (names_equal v i); tauto.

  Case "v". clear pairfree_subst_v.
    intros i r; induction v; intros Hpairfree_bound Hpairfree_in;
        simpl in *; firstorder.
    SCase "Identifier".
      destruct (names_equal v i); tauto.
    SCase "Fix".
      destruct (names_equal v i); destruct (names_equal v0 i);
        firstorder.
Qed.

Theorem pairfree_step : forall e e', e ==> e'
    -> pairfree_e e -> pairfree_e e'.
Proof.
  pose proof pairfree_subst_e.
  induction e; intros e' Hreduces Hpairfree;
      inversion Hreduces; subst; simpl in *; firstorder.
Qed.

Theorem pairfree_wff_e : forall e, pairfree_e e -> wff_e e
   with pairfree_wff_v : forall v, pairfree_v v -> wff_v v.
Proof.
  Case "e". clear pairfree_wff_e.
    induction e; intros Hpairfree; firstorder.

  Case "v". clear pairfree_wff_v.
    induction v; intros Hpairfree; firstorder.
Qed.

Theorem left_pairfree_e : forall e, pairfree_e (left_branch e)
   with left_pairfree_v : forall v, pairfree_v (left_branch_val v).
Proof.
  Case "e". clear left_pairfree_e.
    induction e; firstorder.
  Case "v". clear left_pairfree_v.
    induction v; firstorder.
Qed.

Theorem right_pairfree_e : forall e, pairfree_e (right_branch e)
   with right_pairfree_v : forall v, pairfree_v (right_branch_val v).
Proof.
  Case "e". clear right_pairfree_e.
    induction e; firstorder.
  Case "v". clear right_pairfree_v.
    induction v; firstorder.
Qed.

Theorem wff_subst1_e : forall i r e,
            pairfree_v r -> wff_e e -> wff_e (subst i r e)
   with wff_subst1_v : forall i r v,
            pairfree_v r -> wff_v v -> wff_v (subst_values i r v).
Proof.
  Case "e". clear wff_subst1_e.
    pose proof pairfree_subst_v.
    pose proof pairfree_subst_e.
    pose proof left_pairfree_v.
    pose proof right_pairfree_v.
    intros i r; induction e; intros Hr_pairfree He_wff;
      simpl in *;
      repeat match goal with
        | [ H : _ \/ _ |- _ ] => inversion_clear H; [ left | right ]
      end;
      repeat match goal with
        | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
      end;
      firstorder.

  Case "v". clear wff_subst1_v.
    pose proof pairfree_wff_v.
    pose proof pairfree_subst_v.
    pose proof left_pairfree_v.
    pose proof right_pairfree_v.
    intros i r; induction v; intros Hr_pairfree Hv_wff;
      simpl in *;
      repeat match goal with
        | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
      end;
      firstorder.
Qed.

Theorem wff_subst2_e : forall i r e,
            wff_v r -> pairfree_e e -> wff_e (subst i r e)
   with wff_subst2_v : forall i r v,
            wff_v r -> pairfree_v v -> wff_v (subst_values i r v).
Proof.
  Case "e". clear wff_subst2_e.
    intros i r; induction e; intros Hr_pairfree He_wff;
        firstorder.
    SCase "Let".
      pose proof pairfree_wff_e.
      destruct (names_equal v i); firstorder.

  Case "v". clear wff_subst2_v.
    intros i r; induction v; intros Hr_pairfree Hv_wff;
        simpl in *;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        pose proof pairfree_wff_e;
        firstorder.
Qed.

Theorem wff_subst_e : forall i r e,
            wff_v r -> wff_e e -> wff_e (subst i r e)
   with wff_subst_v : forall i r v,
            wff_v r -> wff_v v -> wff_v (subst_values i r v).
Proof.
  Case "e". clear wff_subst_e.
    intros i r; induction e; intros Hr_pairfree He_wff;
        simpl in *;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        firstorder.
    SCase "pair/left".
      apply pairfree_subst_e. apply left_pairfree_v. assumption.
    SCase "pair/right".
      apply pairfree_subst_e. apply right_pairfree_v. assumption.

  Case "v". clear wff_subst_v.
    intros i r; induction v; intros Hr_pairfree Hv_wff;
        simpl in *;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        pose proof pairfree_wff_e;
        firstorder.
    SCase "pair/left".
      apply pairfree_subst_v. apply left_pairfree_v. assumption.
    SCase "pair/right".
      apply pairfree_subst_v. apply right_pairfree_v. assumption.
Qed.

Theorem wff_step : forall e e', e ==> e'
    -> wff_e e -> wff_e e'.
Proof.
  pose proof pairfree_step.
  pose proof left_pairfree_v. pose proof right_pairfree_v.
  pose proof left_pairfree_e; pose proof right_pairfree_e.
  pose proof wff_subst_e.
  induction e; intros e' Hreduces Hwff;
      inversion Hreduces; subst;
      firstorder.
Qed.

Lemma pairfree_leftbranch_idem_e :
        forall e, pairfree_e e -> left_branch e = e
 with pairfree_leftbranch_idem_v :
        forall v, pairfree_v v -> left_branch_val v = v.
Proof.
  Case "e". clear pairfree_leftbranch_idem_e.
    induction e; firstorder;
        try solve [ simpl; f_equal; firstorder ].
  Case "v". clear pairfree_leftbranch_idem_v.
    induction v; firstorder;
        try solve [ simpl; f_equal; firstorder ].
Qed.

Lemma pairfree_rightbranch_idem_e :
        forall e, pairfree_e e -> right_branch e = e
 with pairfree_rightbranch_idem_v :
        forall v, pairfree_v v -> right_branch_val v = v.
Proof.
  Case "e". clear pairfree_rightbranch_idem_e.
    induction e; firstorder;
        try solve [ simpl; f_equal; firstorder ].
  Case "v". clear pairfree_rightbranch_idem_v.
    induction v; firstorder;
        try solve [ simpl; f_equal; firstorder ].
Qed.

Lemma branch_lle : forall e,
        left_branch (left_branch e) = left_branch e.
Proof.
  intro. apply pairfree_leftbranch_idem_e. apply left_pairfree_e.
Qed.

Lemma branch_lre : forall e,
        left_branch (right_branch e) = right_branch e.
Proof.
  intro. apply pairfree_leftbranch_idem_e. apply right_pairfree_e.
Qed.

Lemma branch_rle : forall e,
        right_branch (left_branch e) = left_branch e.
Proof.
  intro. apply pairfree_rightbranch_idem_e. apply left_pairfree_e.
Qed.

Lemma branch_rre : forall e,
        right_branch (right_branch e) = right_branch e.
Proof.
  intro. apply pairfree_rightbranch_idem_e. apply right_pairfree_e.
Qed.

Lemma branch_llv : forall v,
        left_branch_val (left_branch_val v) = left_branch_val v.
Proof.
  intro. apply pairfree_leftbranch_idem_v. apply left_pairfree_v.
Qed.

Lemma branch_lrv : forall v,
        left_branch_val (right_branch_val v) = right_branch_val v.
Proof.
  intro. apply pairfree_leftbranch_idem_v. apply right_pairfree_v.
Qed.

Lemma branch_rlv : forall v,
        right_branch_val (left_branch_val v) = left_branch_val v.
Proof.
  intro. apply pairfree_rightbranch_idem_v. apply left_pairfree_v.
Qed.

Lemma branch_rrv : forall v,
        right_branch_val (right_branch_val v) = right_branch_val v.
Proof.
  intro. apply pairfree_rightbranch_idem_v. apply right_pairfree_v.
Qed.

Lemma leftbranch_beta_comm : forall var bound expr,
         left_branch (subst var bound expr) = subst var (left_branch_val bound) (left_branch expr)
with leftbranch_beta_comm_val : forall var bound val,
         left_branch_val (subst_values var bound val) =
         subst_values var (left_branch_val bound) (left_branch_val val).
Proof.
  Case "expr". clear leftbranch_beta_comm.
    intros var bound expr.
    generalize dependent bound. generalize dependent var.
    induction expr; intros var bound;
        simpl;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        try solve [ simpl; f_equal; auto ].
    SCase "Pair".
      rewrite IHexpr1. rewrite branch_llv. trivial.
  Case "value". clear leftbranch_beta_comm_val.
    intros var bound val.
    generalize dependent bound. generalize dependent var.
    induction val; intros var bound;
        simpl;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        try solve [ simpl; f_equal; auto ].
    SCase "pair".
      rewrite IHval1. rewrite branch_llv. trivial.
Qed.

Lemma rightbranch_beta_comm : forall var bound expr,
         right_branch (subst var bound expr) = subst var (right_branch_val bound) (right_branch expr)
with rightbranch_beta_comm_val : forall var bound val,
         right_branch_val (subst_values var bound val) =
         subst_values var (right_branch_val bound) (right_branch_val val).
Proof.
  Case "expr". clear rightbranch_beta_comm.
    intros var bound expr.
    generalize dependent bound. generalize dependent var.
    induction expr; intros var bound;
        simpl;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        try solve [ simpl; f_equal; auto ].
    SCase "Pair".
      rewrite IHexpr2. rewrite branch_rrv. trivial.
  Case "value". clear rightbranch_beta_comm_val.
    intros var bound val.
    generalize dependent bound. generalize dependent var.
    induction val; intros var bound;
        simpl;
        repeat match goal with
          | [ |- context [ names_equal ?v ?i ]] => destruct (names_equal v i)
        end;
        try solve [ simpl; f_equal; auto ].
    SCase "pair".
      rewrite IHval2. rewrite branch_rrv. trivial.
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
      rewrite branch_llv.  econstructor.
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
    intros. pose proof (H3 t0) as newH3.
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    SCase "lift".
    simpl. rewrite branch_lle. rewrite branch_lle. constructor. Qed.

Lemma lemma_2_r:  forall e e1, e ==> e1 -> (right_branch e) ==>* (right_branch e1).
Proof.
  intros e. functional induction (right_branch e).
  Case "Expression_Evaluation_Pair".
    intros e1 Hreduces. inversion Hreduces; subst.
    SCase "left stepped". simpl. constructor.
    SCase "right stepped". simpl. apply IHe0. assumption.
  Case "Value".
    intros e1 Hreduces. inversion Hreduces.
  Case "Application".
    intros e1 Hreduces.
    inversion Hreduces; subst.
    SCase "Beta_Reduction_R".
      rewrite rightbranch_beta_comm.
      rewrite rightbranch_beta_comm. simpl.
      pose proof (Beta_Reduction_R t f0 x (right_branch e) (right_branch_val a)) as BR.
      apply step_implies_stepmany in BR. apply BR.
    SCase "Lift_App_R".
      simpl.
      rewrite branch_rrv.  econstructor.
  Case "Let_Bind".
    intros e1 Hreduces.
    inversion Hreduces; subst.
    SCase "let".
     pose proof (Let_R nm (right_branch_val vl) (right_branch e)) as LR.
     apply step_implies_stepmany in LR. rewrite rightbranch_beta_comm. assumption.
  Case "If1".
    intros e1 Hreduces.  inversion Hreduces; subst.
    SCase "0". simpl. pose proof (If1_R t0 (right_branch e1) (right_branch b2)) as IfR.
     apply step_implies_stepmany in IfR. assumption.
    SCase "nonzero".
    simpl.
    pose proof (Ifelse_R (right_branch_val t) (right_branch b1) (right_branch e1)) as IfR.
    apply step_implies_stepmany.
    apply IfR.
    intros. pose proof (H3 t0) as newH3.
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    SCase "lift".
    simpl. rewrite branch_rre. rewrite branch_rre. constructor. Qed.

Lemma lemma_2l_strong : forall e e1,
    e ==> e1 ->
    left_branch e ==> left_branch e1 \/ left_branch e = left_branch e1.
Proof.
  intros e. functional induction (left_branch e).
  Case "Expression_Evaluation_Pair".
    intros e1 Hreduces. inversion Hreduces; subst; firstorder.
  Case "Value".
    intros e1 Hreduces. inversion Hreduces; subst.
  Case "Application".
    intros e1 Hreduces. inversion Hreduces; subst.
    SCase "Beta_Reduction_R".
      rewrite leftbranch_beta_comm.
      rewrite leftbranch_beta_comm. simpl.
      pose proof (Beta_Reduction_R t f0 x (left_branch e) (left_branch_val a)) as BR.
      firstorder.
    SCase "Lift_App_R".
      simpl.
      rewrite branch_llv.  firstorder.
  Case "Let_Bind".
    intros e1 Hreduces. inversion Hreduces; subst.
    SCase "let".
     pose proof (Let_R nm (left_branch_val vl) (left_branch e)) as LR.
     rewrite leftbranch_beta_comm. firstorder.
  Case "If1".
    intros e1 Hreduces.  inversion Hreduces; subst.
    SCase "0". simpl. pose proof (If1_R t0 (left_branch e1) (left_branch b2)) as IfR. firstorder.
    SCase "nonzero".
    simpl.
    pose proof (Ifelse_R (left_branch_val t) (left_branch b1) (left_branch e1)) as IfR.
    left; apply IfR.
    intros. pose proof (H3 t0) as newH3.
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    SCase "lift".
    simpl. rewrite branch_lle. rewrite branch_lle. firstorder. Qed.

Lemma lemma_2r_strong : forall e e1,
    e ==> e1 ->
    right_branch e ==> right_branch e1 \/ right_branch e = right_branch e1.
Proof.
  intros e. functional induction (right_branch e).
  Case "Expression_Evaluation_Pair".
    intros e1 Hreduces. inversion Hreduces; subst.
    SCase "left stepped". simpl. right. constructor.
    SCase "right stepped". simpl. apply IHe0. assumption.
  Case "Value".
    intros e1 Hreduces. inversion Hreduces.
  Case "Application".
    intros e1 Hreduces.
    inversion Hreduces; subst.
    SCase "Beta_Reduction_R".
      rewrite rightbranch_beta_comm.
      rewrite rightbranch_beta_comm. simpl.
      pose proof (Beta_Reduction_R t f0 x (right_branch e) (right_branch_val a)) as BR.
      left. apply BR.
    SCase "Lift_App_R".
      simpl.
      rewrite branch_rrv.  firstorder.
  Case "Let_Bind".
    intros e1 Hreduces.
    inversion Hreduces; subst.
    SCase "let".
     pose proof (Let_R nm (right_branch_val vl) (right_branch e)) as LR.
     rewrite rightbranch_beta_comm. firstorder.
  Case "If1".
    intros e1 Hreduces.  inversion Hreduces; subst.
    SCase "0". simpl. pose proof (If1_R t0 (right_branch e1) (right_branch b2)) as IfR. firstorder.
    SCase "nonzero".
    simpl.
    pose proof (Ifelse_R (right_branch_val t) (right_branch b1) (right_branch e1)) as IfR.
    left; apply IfR.
    intros. pose proof (H3 t0) as newH3.
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    destruct t; simpl; try first [ congruence | discriminate | assumption ].
    SCase "lift".
    simpl. rewrite branch_rre. rewrite branch_rre. firstorder. Qed.

Theorem steps_dec
    : forall e, { e' : expression | e ==> e' } + { ~exists e', e ==>  e' }.
Proof.
  induction e.
  Case "value".
    right. apply values_dont_step. constructor.
  Case "application".
    destruct v;
        try solve [ right; intro Hsteps; solve by inversion 2 ].
    SCase "rator is Fix".
      left. eexists. econstructor.
    SCase "rator is pair".
      left. eexists. econstructor.
  Case "let".
    left. eexists. econstructor.
  Case "if".
    left.
    destruct v;
      try solve [ eexists; econstructor; intros; congruence ].
    SCase "integer".
      compare n 1; intros; subst;
        try solve [ eexists; econstructor; intros; congruence ].
    SCase "pair".
      eexists. eapply Lift_If_R.
  Case "pair".
    inversion_clear IHe1 as [[e1' He1'] | He1_nosteps].
    SCase "e1 steps".
      left. eexists. eapply Bracket_left_R. eassumption.
    inversion_clear IHe2 as [[e2' He2'] | He2_nosteps].
    SCase "e2 steps".
      left. eexists. eapply Bracket_right_R. eassumption.
    SCase "neither steps".
      right.
      intro He_steps; inversion He_steps as [t Ht].
      inversion Ht; subst; firstorder.
Defined.

Lemma multi_Bracket_left : forall e1 e2 e1',
    e1 ==>* e1' ->
    Expression_Evaluation_Pair e1 e2 ==>* Expression_Evaluation_Pair e1' e2.
Proof.
  pose proof Bracket_left_R as B.
  intros. induction H.
  Case "refl".  eapply multi_refl.
  Case "step".  eapply multi_step; eauto.
Qed.

Lemma multi_Bracket_right : forall e1 e2 e2',
    e2 ==>* e2' ->
    Expression_Evaluation_Pair e1 e2 ==>* Expression_Evaluation_Pair e1 e2'.
Proof.
  pose proof Bracket_right_R as B.
  intros. induction H.
  Case "refl".  eapply multi_refl.
  Case "step".  eapply multi_step; eauto.
Qed.

Theorem steps_diamond
  : forall e e1 e2, e ==> e1 -> e ==> e2 ->
      exists e', e1 ==>* e' /\ e2 ==>* e'.
Proof.
  assert (forall e e1 e2, e ==> e1 -> e ==> e2 ->
              e1 = e2 ->
              exists e', e1 ==>* e' /\ e2 ==>* e')
      as det_diamond
      by (intros; subst; eexists; split; econstructor).
  induction e;
    intros;
      try solve [
        eapply det_diamond; [ eassumption | eassumption | idtac ];
        do 2 match goal with
          | [ H: _ ==> _ |- _ ] => inversion H; subst; clear H
        end;
        reflexivity ].
  Case "if".
    eapply det_diamond; [ eassumption | eassumption | idtac ].
    inversion H; subst; inversion H0; subst;
      try solve [ reflexivity ];
      try solve [ exfalso;
          match goal with
            | [ H : context[?a <> _] |- _ ] =>
                assert (a = a) by reflexivity;
                firstorder
          end ].
  Case "pair".
    inversion H; subst; inversion H0; subst.
    SCase "e1/e1".
      destruct (IHe1 e1' e1'0 H4 H5) as [e1'' He1''].
      exists (Expression_Evaluation_Pair e1'' e2).
      split.
        eapply multi_Bracket_left; tauto.
        eapply multi_Bracket_left; tauto.
    SCase "e1/e2".
      exists (Expression_Evaluation_Pair e1' e2').
      split.
        apply step_implies_stepmany. constructor; assumption.
        apply step_implies_stepmany. constructor; assumption.
    SCase "e2/e1".
      exists (Expression_Evaluation_Pair e1' e2').
      split.
        apply step_implies_stepmany. constructor; assumption.
        apply step_implies_stepmany. constructor; assumption.
    SCase "e2/e2".
      destruct (IHe2 e2' e2'0 H4 H5) as [e2'' He2''].
      exists (Expression_Evaluation_Pair e1 e2'').
      split.
        eapply multi_Bracket_right; tauto.
        eapply multi_Bracket_right; tauto.
Qed.

Lemma is_value_dec : forall e, {is_value e} + {~is_value e}.
Proof.
  destruct e;
      try solve [ right; intro H; inversion H ].
  Case "Value".
    left. constructor.
  Case "pair".
    destruct e1; destruct e2;
        try solve [ right; intro H; inversion H].
    left. constructor.
Defined.

Theorem stuck_or_not_dec : forall e, {stuck e} + {~ stuck e}.
Proof.
  intros e.
  unfold stuck in *. unfold normal_form in *.
  destruct (is_value_dec e); destruct (steps_dec e); firstorder.
Defined.

Theorem stuck_or_not : forall e, stuck e \/ ~stuck e.
Proof.
  intro e; destruct (stuck_or_not_dec e); auto.
Qed.

Lemma lemma_3l_nopair_strong : forall e,
    (forall a b, e <> Expression_Evaluation_Pair a b) ->
    (stuck e) -> (stuck (left_branch e)) /\ (stuck (right_branch e)).
Proof.
  induction e; intros Hnonpair Hstuck.
  Case "Value".
    apply values_not_stuck in Hstuck. contradiction. constructor.
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

Lemma lemma_3l_pairfree_strong : forall e,
    pairfree_e e ->
    (stuck e) -> (stuck (left_branch e)) /\ (stuck (right_branch e)).
Proof.
  intros e Hpairfree.
  destruct e;
    repeat (rewrite pairfree_leftbranch_idem_e);
    repeat (rewrite pairfree_rightbranch_idem_e);
    try tauto.
Qed.

Lemma lemma_3l_nopair : forall e,
    (forall a b, e <> Expression_Evaluation_Pair a b) ->
    (stuck e) -> (stuck (left_branch e)) \/ (stuck (right_branch e)).
Proof.
  intros. left. apply lemma_3l_nopair_strong; trivial.
Qed.

Lemma lemma_3l_pairfree : forall e,
    pairfree_e e ->
    (stuck e) -> (stuck (left_branch e)) \/ (stuck (right_branch e)).
Proof.
  intros. left. apply lemma_3l_pairfree_strong; trivial.
Qed.

Lemma lemma_3l_wff : forall e,
    wff_e e ->
    (stuck e) -> (stuck (left_branch e)) \/ (stuck (right_branch e)).
Proof.
  intros e Hwff Hstuck.
  destruct e;
      try solve [ apply lemma_3l_nopair; solve [ intros; congruence ] ].
  Case "e is pair".
    simpl in *.
    rewrite pairfree_leftbranch_idem_e; try tauto.
    rewrite pairfree_rightbranch_idem_e; try tauto.
    unfold stuck in *; unfold normal_form in *.
    inversion_clear Hstuck as [Hnostep Hnoval].
    destruct (steps_dec e1) as [[e1' He1'] | He1_nostep].
    SCase "e1 steps".
      contradict Hnostep. eexists. eapply Bracket_left_R. eassumption.
    destruct (steps_dec e2) as [[e2' He2'] | He2_nostep].
    SCase "e2 steps".
      contradict Hnostep. eexists. eapply Bracket_right_R. eassumption.
    destruct (is_value_dec e1) as [He1_val | He1_noval];
        [ | left; firstorder ].
    destruct (is_value_dec e2) as [He2_val | He2_noval];
        [ | right; firstorder ].
    SCase "both values".
      inversion He1_val; inversion He2_val; subst; try tauto.
      contradict Hnoval; constructor.
Qed.

