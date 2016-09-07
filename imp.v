Set Implicit Arguments.

(** 

Build with 

  > coqc imp.v

using a recent version of Coq (e.g., 8.5pl1).

*)

Require Import List. Import ListNotations.

(** Syntax *)

Inductive val : Type :=
| VTrue : val
| VFalse : val.

Lemma val_eq_dec : forall v1 v2 : val, {v1=v2}+{v1<>v2}.
Proof. decide equality. Qed.

Inductive exp : Type :=
| EVal : val -> exp
| EAnd : exp -> exp -> exp.

Lemma exp_eq_dec : forall e1 e2 : exp, {e1=e2}+{e1<>e2}.
Proof. decide equality. apply val_eq_dec. Qed.

Inductive com : Type :=
| CSkip : com
| CPrint : exp -> com
| CIte : exp -> com -> com -> com
| CWhile : exp -> com -> com
| CSeq : com -> com -> com.

Lemma com_eq_dec : forall c1 c2 : com, {c1=c2}+{c1<>c2}.
Proof.
  decide equality.
  apply exp_eq_dec.
  apply exp_eq_dec.
  apply exp_eq_dec.  
Qed.

(** Semantics *)

Fixpoint eval (e : exp) : val :=
  match e with
  | EVal v => v
  | EAnd e1 e2 =>
    let v1 := eval e1 in
    let v2 := eval e2 in
    match v1, v2 with
    | VFalse, VFalse => VFalse
    | VFalse, VTrue => VFalse
    | VTrue, VFalse => VFalse
    | VTrue, VTrue => VTrue
    end
  end.

Definition state := list val.

Inductive step : com -> state -> com -> state -> Prop :=
| step_print :
    forall s e,
      step (CPrint e) s CSkip (s ++ [eval e])

| step_ite_true :
    forall s e c1 c2,
      eval e = VTrue -> 
      step (CIte e c1 c2) s c1 s

| step_ite_false :
    forall s e c1 c2,
      eval e = VFalse -> 
      step (CIte e c1 c2) s c2 s

| step_while :
    forall s e c,
      step (CWhile e c) s (CIte e (CSeq c (CWhile e c)) CSkip) s

| step_cseq1 :
    forall s c2,
      step (CSeq CSkip c2) s c2 s

| step_cseq2 :
    forall s s' c1 c1' c2,
      step c1 s c1' s' -> 
      step (CSeq c1 c2) s (CSeq c1' c2) s'.

(*the transitive closure of the step relation*)
Inductive step_plus : com -> state -> com -> state -> Prop :=
| step1 :
    forall c s c' s',
      step c s c' s' ->
      step_plus c s c' s'

| step_trans :
    forall c s c'' s'' c' s',
      step c s c'' s'' ->
      step_plus c'' s'' c' s' ->
      step_plus c s c' s'.

Lemma step_plus_trans :
  forall c s c'' s'' c' s',
    step_plus c s c'' s'' ->
    step_plus c'' s'' c' s' ->
    step_plus c s c' s'.
Proof.
  intros until s'; intros H.
  revert c' s'.
  induction H.
  { intros cx sx H2.
    eapply step_trans; eauto. }
  intros cx sx H2.
  eapply step_trans; eauto.
Qed.  

(** Constant Propagation *)

Fixpoint constprop (c : com) :=
  match c with
  | CSkip => CSkip
  | CPrint e => CPrint e
  | CIte (EVal VTrue) c1 c2 => constprop c1
  | CIte (EVal VFalse) c1 c2 => constprop c2
  (*we could of course do more constprop in the next case...*)  
  | CIte (EAnd e1 e2) c1 c2 => CIte (EAnd e1 e2) (constprop c1) (constprop c2)
  (*and in this one as well...*)                                  
  | CWhile e c' => CWhile e (constprop c')
  | CSeq c1 c2 => CSeq (constprop c1) (constprop c2)
  end.

(** Simulation Relation/Proof *)

Inductive com_match : com -> com -> Prop :=
| com_match_skip :
    com_match CSkip CSkip

| com_match_print :
    forall e,
      com_match (CPrint e) (CPrint e)

| com_match_ite_false :
    forall c1 c1' c2,
      com_match c1 c1' ->     
      com_match (CIte (EVal VTrue) c1 c2) c1'

| com_match_ite_true :
    forall c1 c2 c2',
      com_match c2 c2' ->     
      com_match (CIte (EVal VFalse) c1 c2) c2'

| com_match_ite_other :
    forall e c1 c1' c2 c2',
      com_match c1 c1' ->           
      com_match c2 c2' ->     
      com_match (CIte e c1 c2) (CIte e c1' c2')
                
| com_match_while :
    forall e c c',
      com_match c c' ->
      com_match (CWhile e c) (CWhile e c')

| com_match_cseq :
    forall c1 c1' c2 c2',
      com_match c1 c1' ->
      com_match c2 c2' ->
      com_match (CSeq c1 c2) (CSeq c1' c2').

Lemma constprop_com_match :
  forall c, com_match c (constprop c).
Proof.
  induction c; try solve[constructor|constructor; auto].
  destruct e; [destruct v; constructor; auto|constructor; auto].
Qed.

Definition R (c : com) (s : state) (c' : com) (s' : state) :=
  s=s' /\ com_match c c'.

Lemma com_match_skip_step_plus :
  forall c s, 
    com_match c CSkip ->
    c = CSkip \/ step_plus c s CSkip s.
Proof.
  intros c s H; revert s.
  induction c; try solve[inversion H].
  { intros s; constructor. auto. }
  intros s. inversion H; subst.
  { destruct (IHc1 H4 s).
    { subst c1.
      right. constructor. constructor. auto. }
    right. eapply step_trans; eauto. constructor; auto. }
  destruct (IHc2 H4 s).
  { subst c2.
    right. constructor. constructor. auto. }
  right. eapply step_trans; eauto. constructor; auto.
Qed.

Lemma step_plus_seq :
  forall c1 c1' c2 s s', 
    step_plus c1 s c1' s' -> 
    step_plus (CSeq c1 c2) s (CSeq c1' c2) s'.
Proof.
  intros until s'; intros H.
  induction H.
  { constructor.
    constructor; auto. }
  eapply step_plus_trans; eauto.
  constructor.
  constructor; auto.
Qed.  

Lemma step_plus_seq_CSkip :
  forall c1 c2 s, 
    step_plus c1 s CSkip s -> 
    step_plus (CSeq c1 c2) s c2 s.
Proof.
  intros c1 c2 s H.
  eapply step_plus_trans.
  eapply step_plus_seq in H.
  apply H.
  constructor.
  constructor.
Qed.

(** Main simulation diagram *)

Lemma diagram :
  forall c s d t d' t',
    step d t d' t' ->
    R c s d t ->
    exists c' s',
      step_plus c s c' s' /\
      R c' s' d' t'.
Proof.
  intros c s d t d' t' H H1.
  revert d' t' H.
  destruct H1 as [H1 H2]; subst s.
  induction H2.
  { intros d' t'; inversion 1; subst. }
  { intros d' t'; inversion 1; subst.
    exists CSkip, (t++[eval e]); split; [constructor; auto|].
    split; auto; constructor. }
  { intros d' t' H.
    destruct (IHcom_match _ _ H) as [c1'' [s'' [H3 H4]]].
    exists c1'', s''; split; auto.
    eapply step_trans; eauto.
    constructor; auto. }
  { intros d' t' H.
    destruct (IHcom_match _ _ H) as [c1'' [s'' [H3 H4]]].
    exists c1'', s''; split; auto.
    eapply step_trans; eauto.
    constructor; auto. }
  { intros d' t' H.
    inversion H; subst.
    { exists c1, t'; split.
      constructor.
      constructor; auto.
      split; auto. }
    { exists c2, t'; split.
      constructor.
      constructor; auto.
      split; auto. }}
  { intros d' t'; inversion 1; subst.
    exists (CIte e (CSeq c (CWhile e c)) CSkip), t'; split.
    constructor.
    constructor.
    split; auto.
    constructor.
    constructor; auto.
    constructor; auto.
    constructor. }
  intros d' t'; inversion 1; subst.
  { apply (@com_match_skip_step_plus _ t') in H2_.
    exists c2, t'; split.
    { destruct H2_.
      { subst c1.
        constructor.
        constructor. }
      apply step_plus_seq_CSkip; auto. }
    split; auto. }
  destruct (@IHcom_match1 _ _ H5) as [c1'' [t'' [H7 H8]]].
  exists (CSeq c1'' c2), t''; split.
  apply step_plus_seq; auto.
  destruct H8; subst t''.
  split; auto.
  constructor; auto.
Qed.  

Lemma consequence1 :
  forall c s d t d' t',
    step_plus d t d' t' ->
    R c s d t ->
    exists c' s',
      step_plus c s c' s' /\
      R c' s' d' t'.
Proof.
  intros c s d t d' t' H; revert c s.
  induction H.
  { intros cx sx H2.
    eapply diagram in H; eauto. }
  intros cx sx H2.
  eapply diagram in H; eauto.
  destruct H as [cy [sy [H3 H4]]].
  destruct (IHstep_plus _ _ H4) as [cz [sz [H5 H6]]].
  exists cz, sz; split; auto.
  eapply step_plus_trans; eauto.
Qed.

(* Theorem: 
   If the constant-propagated version of command [c] produces 
   event list [ev_list], then so does [c]. *)

Lemma consequence2 :
  forall c d' ev_list,
    step_plus (constprop c) [] d' ev_list ->
    exists c', step_plus c [] c' ev_list.
Proof.
  intros c d' ev_list H.
  assert (H2: R c [] (constprop c) []).
  { split; auto.
    apply constprop_com_match. }
  destruct (consequence1 H H2) as [c' [s' [H3 H4]]].
  destruct H4; subst s'.
  exists c'; auto.
Qed.
