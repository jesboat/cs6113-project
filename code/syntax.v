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


Function bpairfree_v (v : value) : bool :=
  match v with
  | Identifier _ _ => true
  | Integer _ _ => true
  | Fix _ _ _ e => bpairfree_e e
  | Value_Evaluation_Pair _ _ _ => false
  end

with bpairfree_e (e : expression) : bool :=
  match e with
  | Value v => bpairfree_v v
  | Application v1 v2 => bpairfree_v v1 && bpairfree_v v2
  | Let_Bind _ v e =>
      bpairfree_v v && bpairfree_e e
  | If1 v e1 e2 =>
      bpairfree_v v && bpairfree_e e1 && bpairfree_e e2
  | Expression_Evaluation_Pair _ _ => false
  end.

Function bwff_v (v : value) : bool :=
  match v with
  | Identifier _ _ => true
  | Integer _ _ => true
  | Fix _ _ _ e => bwff_e e
  | Value_Evaluation_Pair ty v1 v2 => bpairfree_v v1 && bpairfree_v v2
  end

with bwff_e (e : expression) : bool :=
  match e with
  | Value v => bwff_v v
  | Application v1 v2 => bwff_v v1 && bwff_v v2
  | Let_Bind _ v e => bwff_v v && bwff_e e
  | If1 v e1 e2 => bwff_v v && bwff_e e1 && bwff_e e2
  | Expression_Evaluation_Pair e1 e2 => bpairfree_e e1 && bpairfree_e e2
  end.

Function pairfree_v (v : value) : Prop :=
  match v with
  | Identifier _ _ => True
  | Integer _ _ => True
  | Fix _ _ _ e => pairfree_e e
  | Value_Evaluation_Pair _ _ _ => False
  end

with pairfree_e (e : expression) : Prop :=
  match e with
  | Value v => pairfree_v v
  | Application v1 v2 => pairfree_v v1 /\ pairfree_v v2
  | Let_Bind _ v e =>
      pairfree_v v /\ pairfree_e e
  | If1 v e1 e2 =>
      pairfree_v v /\ pairfree_e e1 /\ pairfree_e e2
  | Expression_Evaluation_Pair _ _ => False
  end.

Function wff_v (v : value) : Prop :=
  match v with
  | Identifier _ _ => True
  | Integer _ _ => True
  | Fix _ _ _ e => wff_e e
  | Value_Evaluation_Pair ty v1 v2 => pairfree_v v1 /\ pairfree_v v2
  end

with wff_e (e : expression) : Prop :=
  match e with
  | Value v => wff_v v
  | Application v1 v2 => wff_v v1 /\ wff_v v2
  | Let_Bind _ v e => wff_v v /\ wff_e e
  | If1 v e1 e2 => wff_v v /\ wff_e e1 /\ wff_e e2
  | Expression_Evaluation_Pair e1 e2 => pairfree_e e1 /\ pairfree_e e2
  end.

Theorem pairfree_bpairfree_v : forall v, pairfree_v v <-> bpairfree_v v = true
   with pairfree_bpairfree_e : forall e, pairfree_e e <-> bpairfree_e e = true.
Proof.
  Case "v". clear pairfree_bpairfree_v.
    induction v; intros; simpl in *; firstorder.
    SCase "Pair". discriminate.

  Case "e". clear pairfree_bpairfree_e.
    induction e; intros; simpl in *;
        repeat (rewrite andb_true_iff);
        firstorder.
    SCase "pair". discriminate.
Qed.

Theorem wff_bwff_v : forall v, wff_v v <-> bwff_v v = true
   with wff_bwff_e : forall e, wff_e e <-> bwff_e e = true.
Proof.
  Case "v". clear wff_bwff_v.
    pose proof pairfree_bpairfree_v.
    induction v; intros; simpl in *;
        repeat (rewrite andb_true_iff);
        firstorder.

  Case "e". clear wff_bwff_e.
    pose proof pairfree_bpairfree_e.
    induction e; intros; simpl in *;
        repeat (rewrite andb_true_iff);
        firstorder.
Qed.

Lemma pairfree_wff_v : forall v, pairfree_v v -> wff_v v
with  pairfree_wff_e : forall e, pairfree_e e -> wff_e e.
Proof.
  Case "v". clear pairfree_wff_v.
    induction v; firstorder.

  Case "e". clear pairfree_wff_e.
    induction e; firstorder.
Qed.


Definition wvalue : Set := { v : value | wff_v v }.

Definition wexpression : Set := { e : expression | wff_e e }.

Definition mkwff_v (v : value) {prf : bwff_v v = true} : wvalue.
Proof.
  refine (exist wff_v v _). apply wff_bwff_v; trivial.
Defined.

Definition mkwff_e (e : expression) {prf : bwff_e e = true} : wexpression.
Proof.
  refine (exist wff_e e _). apply wff_bwff_e; trivial.
Defined.


Definition ebranch_picker_t : Set :=
    forall e e1 e2, e = Expression_Evaluation_Pair e1 e2
            -> {x : expression | x = e1 \/ x = e2}.

Definition vbranch_picker_t : Set :=
    forall v ty v1 v2, v = Value_Evaluation_Pair ty v1 v2
            -> {x : value | x = v1 \/ x = v2}.

Inductive which_branch : ebranch_picker_t -> vbranch_picker_t -> Set :=
  | pick_left : which_branch
            (fun e e1 e2 prf => exist (fun x => x = e1 \/ x = e2)
                                      e1 (or_introl eq_refl))
            (fun v ty v1 v2 prf => exist (fun x => x = v1 \/ x = v2)
                                      v1 (or_introl eq_refl))
  | pick_right : which_branch
            (fun e e1 e2 prf => exist (fun x => x = e1 \/ x = e2)
                                      e2 (or_intror eq_refl))
            (fun v ty v1 v2 prf => exist (fun x => x = v1 \/ x = v2)
                                      v2 (or_intror eq_refl))
.

Function
    get_branch_v {picke : ebranch_picker_t} {pickv : vbranch_picker_t}
                 (w : which_branch picke pickv)
                 (v : value) :=
  match v with
    | Identifier t vn => v
    | Integer _ _ => v
    | Fix t f a b => Fix t f a (get_branch_e w b)
    | Value_Evaluation_Pair t l r =>
        match w with
            | pick_left => get_branch_v w l
            | pick_right => get_branch_v w r
        end
  end
with
    get_branch_e {picke : ebranch_picker_t} {pickv : vbranch_picker_t}
                 (w : which_branch picke pickv)
                 (e : expression) :=
  match e with
  | Value v => Value (get_branch_v w v)
  | Application f a => Application (get_branch_v w f) (get_branch_v w a)
  | Let_Bind nm vl e => Let_Bind nm (get_branch_v w vl) (get_branch_e w e)
  | If1 t b1 b2 => If1 (get_branch_v w t) (get_branch_e w b1) (get_branch_e w b2)
  | Expression_Evaluation_Pair l r =>
        match w with
        | pick_left => get_branch_e w l
        | pick_right => get_branch_e w r
        end
  end.

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

Ltac rewrite_everything :=
    try
    match goal with
    | H : _ |- _ =>
            rewrite H;
            repeat (rewrite H); clear H;
            try (rewrite_everything)
    end.


Theorem leftbranch_ok_e : forall e, get_branch_e pick_left e = left_branch e
    with leftbranch_ok_v : forall v, get_branch_v pick_left v = left_branch_val v.
Proof.
    Case "e". clear leftbranch_ok_e.
        induction e; simpl; rewrite_everything; reflexivity.
    Case "v". clear leftbranch_ok_v.
        induction v; simpl; rewrite_everything; reflexivity.
Qed.

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

Theorem rightbranch_ok_e : forall e, get_branch_e pick_right e = right_branch e
    with rightbranch_ok_v : forall v, get_branch_v pick_right v = right_branch_val v.
Proof.
    Case "e". clear rightbranch_ok_e.
        induction e; simpl; rewrite_everything; reflexivity.
    Case "v". clear rightbranch_ok_v.
        induction v; simpl; rewrite_everything; reflexivity.
Qed.

Fixpoint get_type (val : value) : type :=
  match val with
    | Identifier t _ => t
    | Integer t _ => t
    | Fix t f a b => t
    | Value_Evaluation_Pair t l r => t
  end.

(* TODO: figure out `Warning: Cannot define graph(s) for subst_values, subst`

Specifically, it seems to happen only when the two Functions are
defined simultaneously. If we define them separately, parameterized
over each other, as below, everything works fine.

*)

Function subst_values (var : variable_name) (bind : value) (val : value): value :=
  match val with
    | Identifier _ nm => if (names_equal nm var) then bind else val
    | Fix t f a b => if (names_equal f var) then val else
                       if (names_equal a var) then val else
                         Fix t f a (subst var bind b)
    | Value_Evaluation_Pair t v1 v2
            => Value_Evaluation_Pair t
                    (subst_values var (left_branch_val bind) v1)
                    (subst_values var (right_branch_val bind) v2)
    | Integer _ _ => val
  end

with subst (var : variable_name) (bind : value) (expr : expression) : expression :=
  match expr with
    | Value v
        => Value (subst_values var bind v)
    | Application f a
        => Application (subst_values var bind f) (subst_values var bind a)
    | Let_Bind name val expr
        => Let_Bind name (subst_values var bind val)
                (if names_equal name var
                 then expr
                 else subst var bind expr)
    | If1 t th el
        => If1 (subst_values var bind t)
               (subst var bind th)
               (subst var bind el)
    | Expression_Evaluation_Pair l r
        => Expression_Evaluation_Pair (subst var (left_branch_val bind) l)
                                      (subst var (right_branch_val bind) r)
  end.

Function exprsize (e : expression) : nat :=
    match e with
      | Expression_Evaluation_Pair l r => 1 + exprsize l + exprsize r
      | Value v => 1 + valsize v
      | Application f a => 1 + valsize f + valsize a
      | Let_Bind nm vl e => 1 + valsize vl + exprsize e
      | If1 t b1 b2 => 1 + valsize t + exprsize b1 + exprsize b2
    end

  with valsize (val : value) :=
    match val with
      | Identifier _ _ => 1
      | Integer _ _ => 1
      | Fix t f a b => 1 + exprsize b
      | Value_Evaluation_Pair t l r => 1 + valsize l + valsize r
    end.

Theorem expr_ind_size :
    forall (P : expression -> Prop),
    (forall e, (forall e', exprsize e' < exprsize e -> P e') -> P e) ->
    forall e, P e.
Proof.
  intros P whenS.
  exact (induction_ltof1 expression exprsize P whenS).
Defined.

Theorem expr_rec_size :
    forall (P : expression -> Set),
    (forall e, (forall e', exprsize e' < exprsize e -> P e') -> P e) ->
    forall e, P e.
Proof.
  intros P whenS.
  exact (induction_ltof1 expression exprsize P whenS).
Defined.

Theorem val_ind_size :
    forall (P : value -> Prop),
    (forall v, (forall v', valsize v' < valsize v -> P v') -> P v) ->
    forall v, P v.
Proof.
  intros P whenS.
  exact (induction_ltof1 value valsize P whenS).
Defined.

Theorem size_smaller_mega_v :
    forall v,
      (forall ty fn an expr, v = Fix ty fn an expr ->
        exprsize expr < valsize v) /\
      (forall ty v1 v2, v = Value_Evaluation_Pair ty v1 v2 ->
        valsize v1 < valsize v) /\
      (forall ty v1 v2, v = Value_Evaluation_Pair ty v1 v2 ->
        valsize v2 < valsize v)
   with size_smaller_mega_e :
    forall e,
      (forall v, e = Value v ->
        valsize v < exprsize e) /\
      (forall v1 v2, e = Application v1 v2 ->
        valsize v1 < exprsize e) /\
      (forall v1 v2, e = Application v1 v2 ->
        valsize v2 < exprsize e) /\
      (forall vn v1 e1, e = Let_Bind vn v1 e1 ->
        valsize v1 < exprsize e) /\
      (forall vn v1 e1, e = Let_Bind vn v1 e1 ->
        exprsize e1 < exprsize e) /\
      (forall v1 e1 e2, e = If1 v1 e1 e2 ->
        valsize v1 < exprsize e) /\
      (forall v1 e1 e2, e = If1 v1 e1 e2 ->
        exprsize e1 < exprsize e) /\
      (forall v1 e1 e2, e = If1 v1 e1 e2 ->
        exprsize e2 < exprsize e) /\
      (forall e1 e2, e = Expression_Evaluation_Pair e1 e2 ->
        exprsize e1 < exprsize e) /\
      (forall e1 e2, e = Expression_Evaluation_Pair e1 e2 ->
        exprsize e2 < exprsize e).
Proof.
  Case "v". clear size_smaller_mega_v.
    induction v;
        repeat split; intros; simpl;
        match goal with
        | [ H : _ = _ |- _ ] => inversion_clear H; subst
        end;
        omega.

  Case "e". clear size_smaller_mega_e.
    induction e;
        repeat split; intros; simpl;
        match goal with
        | [ H : _ = _ |- _ ] => inversion_clear H; subst
        end;
        omega.
Qed.

Theorem val_rec_size :
    forall (P : value -> Set),
    (forall v, (forall v', valsize v' < valsize v -> P v') -> P v) ->
    forall v, P v.
Proof.
  intros P whenS.
  exact (induction_ltof1 value valsize P whenS).
Defined.

Theorem left_size_e : forall e, exprsize (left_branch e) <= exprsize e
   with left_size_v : forall v, valsize (left_branch_val v) <= valsize v.
Proof.
  Case "e". clear left_size_e.
    induction e;
        try match goal with
        | [ v1 : value |- _ ] => pose proof (left_size_v v1)
        end;
        try match goal with
        | [ v1 : value |- _ ] =>
            match goal with
            | [ H : context [ valsize v1 ] |- _ ] => fail 1
            | _ => pose proof (left_size_v v1)
            end
        end;
        simpl;
        omega.

  Case "v". clear left_size_v.
    induction v;
        try match goal with
        | [ e1 : expression |- _ ] => pose proof (left_size_e e1)
        end;
        simpl;
        omega.
Qed.

Theorem right_size_e : forall e, exprsize (right_branch e) <= exprsize e
   with right_size_v : forall v, valsize (right_branch_val v) <= valsize v.
Proof.
  Case "e". clear right_size_e.
    induction e;
        try match goal with
        | [ v1 : value |- _ ] => pose proof (right_size_v v1)
        end;
        try match goal with
        | [ v1 : value |- _ ] =>
            match goal with
            | [ H : context [ valsize v1 ] |- _ ] => fail 1
            | _ => pose proof (right_size_v v1)
            end
        end;
        simpl;
        omega.

  Case "v". clear right_size_v.
    induction v;
        try match goal with
        | [ e1 : expression |- _ ] => pose proof (right_size_e e1)
        end;
        simpl;
        omega.
Qed.

Function wubst_values0
        (wubst : variable_name -> value -> expression -> expression)
        (var : variable_name) (bind : value) (val : value): value :=
  match val with
    | Identifier _ nm => if (names_equal nm var) then bind else val
    | Fix t f a b => if (names_equal f var) then val else
                       if (names_equal a var) then val else
                         Fix t f a (wubst var bind b)
    | Value_Evaluation_Pair t v1 v2 => Value_Evaluation_Pair t (wubst_values0 wubst var (left_branch_val bind) v1)
                                                             (wubst_values0 wubst var (right_branch_val bind) v2)
    | Integer _ _ => val
  end.

Function wubst0
        (wubst_values : variable_name -> value -> value -> value)
        (var : variable_name) (bind : value) (expr : expression) : expression :=
  match expr with
    | Value v
        => Value (wubst_values var bind v)
    | Application f a
        => Application (wubst_values var bind f) (wubst_values var bind a)
    | Let_Bind name val expr
        => Let_Bind name (wubst_values var bind val)
                (if names_equal name var
                 then expr
                 else wubst0 wubst_values var bind expr)
    | If1 t th el
        => If1 (wubst_values var bind t)
               (wubst0 wubst_values var bind th)
               (wubst0 wubst_values var bind el)
    | Expression_Evaluation_Pair l r
        => Expression_Evaluation_Pair
                (wubst0 wubst_values var (left_branch_val bind) l)
                (wubst0 wubst_values var (right_branch_val bind) r)
  end.

Definition wubst_values := wubst_values0 subst.
Definition wubst := wubst0 subst_values.

(*
Theorem wubst_values_ok : forall i b v, subst_values i b v = wubst_values i b v
    with wubst_ok : forall i b e, subst i b e = wubst i b e.
Proof.
    Case "v". clear wubst_values_ok.
        unfold wubst_values in *. unfold wubst in *.
        induction v; try solve [ reflexivity
                               | simpl; rewrite_everything; reflexivity ].
        simpl.
        assert (subst_values i (left_branch_val b) v1
                = wubst_values0 subst i (left_branch_val b) v1) by admit.
        assert (subst_values i (right_branch_val b) v2
                = wubst_values0 subst i (right_branch_val b) v2) by admit.
        rewrite_everything; reflexivity.
    Case "e". clear wubst_ok.
        unfold wubst_values in *. unfold wubst in *.
        induction e; try solve [ reflexivity
                               | simpl; rewrite_everything; reflexivity ].
        simpl.
        assert (subst i (left_branch_val b) e1
                = wubst0 subst_values i (left_branch_val b) e1) by admit.
        assert (subst i (right_branch_val b) e2
                = wubst0 subst_values i (right_branch_val b) e2) by admit.
        rewrite_everything; reflexivity.
Admitted.
(* Qed. *)

Theorem wubst_eq : forall i b e, wubst i b e = wubst0 wubst_values i b e.
Proof.
    intros.
    pose proof wubst_values_ok as H. (* not sure why necessary *)
    induction e;
        simpl; unfold wubst; simpl; fold wubst; (* do recursion *)
        repeat first [ rewrite IHe | rewrite IHe1 | rewrite IHe2 ];
        repeat (rewrite H);
        reflexivity.
Defined.

Theorem wubst_values_eq : forall i b v, wubst_values i b v = wubst_values0 wubst i b v.
Proof.
    intros.
    induction v;
        simpl; unfold wubst_values; simpl; fold wubst_values;
        repeat first [ rewrite IHv | rewrite IHv1 | rewrite IHv2 ];
        repeat (rewrite wubst_ok);
        reflexivity.
Defined.
*)
