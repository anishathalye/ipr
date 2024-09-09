Require Import IPR.Common.

Require Import List.

Create HintDb machine.

Record machine (input output : Type) :=
  {
    state : Type;
    init : state;
    step : state -> input -> result output state -> Prop;
    reset : state -> state -> Prop;
  }.

Arguments state [input output].
Arguments init [input output].
Arguments step [input output].
Arguments reset [input output].

Definition no_reset {I O : Type} (M : machine I O) : Prop :=
  M.(reset) = fun s s' => s = s'.

Definition deterministic {I O : Type} (M : machine I O) : Prop :=
  forall s i r1 r2,
    M.(step) s i r1 ->
    M.(step) s i r2 ->
    r1 = r2.

Definition total {I O : Type} (M : machine I O) : Prop :=
  forall s i,
  exists r,
    M.(step) s i r.

Inductive event (I O : Type) :=
| IO : I -> O -> event I O
| Reset : event I O.

Arguments IO [I O].
Arguments Reset {I O}.

Definition trace (I O : Type) := list (event I O).

Inductive execution {I O : Type} (M : machine I O) : M.(state) -> trace I O -> M.(state) -> Prop :=
| ExecutionEmpty : forall s, execution _ s nil s
| ExecutionStep : forall s i s' o tr s'',
    M.(step) s i (Result o s') ->
    execution _ s' tr s'' ->
    execution _ s (IO i o :: tr) s''
| ExecutionReset : forall s s' tr s'',
    M.(reset) s s' ->
    execution _ s' tr s'' ->
    execution _ s (Reset :: tr) s''.

#[export] Hint Constructors execution : machine.

Inductive execution_r {I O : Type} (M : machine I O) : M.(state) -> trace I O -> M.(state) -> Prop :=
| ExecutionREmpty : forall s, execution_r _ s nil s
| ExecutionRStep : forall s tr s' i o s'',
    execution_r _ s tr s' ->
    M.(step) s' i (Result o s'') ->
    execution_r _ s (tr ++ IO i o :: nil) s''
| ExecutionRReset : forall s tr s' s'',
    execution_r _ s tr s' ->
    M.(reset) s' s'' ->
    execution_r _ s (tr ++ Reset :: nil) s''.

#[export] Hint Constructors execution_r : machine.

Definition in_traces {I O : Type} (M : machine I O) (tr : trace I O) : Prop :=
  exists sf, execution M M.(init) tr sf.

#[export] Hint Unfold in_traces : machine.

(* M1 <= M2, any sequence of outputs that can be produced by M1 can also be produced by M2 *)
Definition refines {I O : Type} (M1 M2 : machine I O) : Prop :=
  forall tr,
    in_traces M1 tr ->
    in_traces M2 tr.

#[export] Hint Unfold refines : machine.

Lemma refines_refl :
  forall I O (M : machine I O),
    refines M M.
Proof.
  auto with machine.
Qed.

Lemma refines_trans :
  forall I O (M1 M2 M3 : machine I O),
    refines M1 M2 ->
    refines M2 M3 ->
    refines M1 M3.
Proof.
  auto with machine.
Qed.

(* any sequence of outputs that can be produced by one can be produced by the other *)
Definition equivalent {I O : Type} (M1 M2 : machine I O) : Prop :=
  refines M1 M2 /\ refines M2 M1.

#[export] Hint Unfold equivalent : machine.

Lemma equivalent_refl :
  forall I O (M : machine I O),
    equivalent M M.
Proof.
  auto with machine.
Qed.

Lemma equivalent_symm :
  forall I O (M1 M2 : machine I O),
    equivalent M1 M2 ->
    equivalent M2 M1.
Proof.
  unfold equivalent.
  intuition.
Qed.

Lemma equivalent_trans :
  forall I O (M1 M2 M3 : machine I O),
    equivalent M1 M2 ->
    equivalent M2 M3 ->
    equivalent M1 M3.
Proof.
  unfold equivalent.
  intuition (eauto using refines_trans).
Qed.

Definition forward_simulation_relation
  {I O : Type} {M1 M2 : machine I O}
  (R : M1.(state) -> M2.(state) -> Prop) :=
  (* initialization *)
  R M1.(init) M2.(init) /\
    (* step *)
    (forall s1 i o s1' s2,
        R s1 s2 ->
        M1.(step) s1 i (Result o s1') ->
        exists s2', M2.(step) s2 i (Result o s2') /\ R s1' s2') /\
    (* reset *)
    (forall s1 s1' s2,
        R s1 s2 ->
        M1.(reset) s1 s1' ->
        exists s2', M2.(reset) s2 s2' /\ R s1' s2').

Theorem forward_simulation :
  forall (I O : Type) (M1 M2 : machine I O)
    (R : M1.(state) -> M2.(state) -> Prop),
    forward_simulation_relation R ->
    refines M1 M2.
Proof.
  intros I O M1 M2 R (Hinit & Hstep & Hreset).
  unfold refines, in_traces.
  generalize dependent (M1.(init)).
  generalize dependent (M2.(init)).
  intros s2 s1 HR.
  intros tr Hexec.
  generalize dependent s2.
  destruct Hexec as [s1f Hexec].
  induction Hexec; try solve [ eauto with machine ].
  - intros s2 HR.
    specialize (Hstep _ _ _ _ _ HR H).
    destruct Hstep as [s2' [Hres HR']].
    destruct (IHHexec s2' HR') as [s2f Hexec'].
    eauto with machine.
  - intros s2 HR.
    destruct (Hreset _ _ _ HR H) as (s2' & Hs2'reset & Hs2'R).
    destruct (IHHexec _ Hs2'R).
    eauto with machine.
Qed.

Lemma execution_join :
  forall I O (M : machine I O) s0 s1 s2 io1 io2,
    execution M s0 io1 s1 ->
    execution M s1 io2 s2 ->
    execution M s0 (io1 ++ io2) s2.
Proof.
  induction 1; subst; simpl; intros; eauto with machine.
Qed.

#[export] Hint Resolve execution_join : machine.

Lemma execution_cons :
  forall I O (M : machine I O) s0 s1 s2 tr1 tr2,
    execution M s0 (tr1 :: nil) s1 ->
    execution M s1 tr2 s2 ->
    execution M s0 (tr1 :: tr2) s2.
Proof.
  intros I O M s0 s1 s2 io1 io2 H H0.
  replace (io1 :: io2) with ((io1 :: nil) ++ io2) by auto.
  eapply execution_join; eauto.
Qed.

#[export] Hint Resolve execution_cons : machine.

Lemma execution_consume :
  forall I O (M : machine I O) s0 s2 evt tr,
    execution M s0 (evt :: tr) s2 ->
    exists s1,
      execution M s0 (evt :: nil) s1 /\
        execution M s1 tr s2.
Proof.
  intros I O M s0 s2 evt tr H.
  inversion H; subst;
    eauto with machine.
Qed.

#[export] Hint Resolve execution_consume : machine.

Lemma execution_split :
  forall I O (M : machine I O) s0 s2 tr1 tr2,
    execution M s0 (tr1 ++ tr2) s2 ->
    exists s1,
      execution M s0 tr1 s1 /\
        execution M s1 tr2 s2.
Proof.
  intros I O M s0 s2 io1.
  generalize dependent s2.
  generalize dependent s0.
  induction io1; eauto with machine.
  intros s0 s2 io2 H.
  pose proof (execution_consume _ _ _ _ _ _ _ H) as Hcons.
  inversion Hcons as [? [? Hintr]].
  specialize (IHio1 _ _ _ Hintr).
  inversion IHio1; eexists; intuition; eauto with machine.
Qed.

#[export] Hint Resolve execution_split : machine.

Lemma execution_r_execution :
  forall I O (M : machine I O) s io s',
    execution_r M s io s' ->
    execution M s io s'.
Proof.
  intros I O M s io s' H.
  induction H; eauto with machine.
Qed.

#[export] Hint Resolve execution_r_execution : machine.

Lemma execution_r_join :
  forall I O (M : machine I O) s0 s1 s2 tr1 tr2,
    execution_r M s0 tr1 s1 ->
    execution_r M s1 tr2 s2 ->
    execution_r M s0 (tr1 ++ tr2) s2.
Proof.
  intros I O M s0 s1 s2 io1 io2.
  generalize dependent s2.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent io1.
  induction io2 as [| io] using rev_ind.
  - intros io1 s0 s1 s2 H0 H1.
    inversion H1; subst.
    + rewrite app_nil_r; assumption.
    + destruct tr; simpl in *; congruence.
    + destruct tr; simpl in *; congruence.
  - intros io1 s0 s1 s2 H0 H1.
    destruct io as [i o | ].
    + inversion H1.
      * destruct io2; simpl in *; congruence.
      * apply app_inj_tail in H.
        destruct H as [Hio2 Hio].
        inversion Hio; clear Hio.
        subst.
        rewrite app_assoc.
        eauto with machine.
      * apply app_inj_tail in H; destruct H; congruence.
    + rewrite app_assoc.
      inversion H1.
      * destruct io2; simpl in *; congruence.
      * apply app_inj_tail in H; destruct H; congruence.
      * apply app_inj_tail in H.
        destruct H; subst.
        eauto with machine.
Qed.

#[export] Hint Resolve execution_r_join : machine.

Lemma execution_execution_r :
  forall I O (M : machine I O) s tr s',
    execution M s tr s' ->
    execution_r M s tr s'.
Proof.
  intros I O M s tr s' H.
  induction H; auto with machine.
  - replace (IO i o :: tr) with ((IO i o :: nil) ++ tr) by auto.
    eapply execution_r_join; eauto.
    replace (IO i o :: nil) with (nil ++ (IO i o :: nil)) by auto.
    eauto with machine.
  - replace (Reset :: tr) with ((Reset :: nil) ++ tr) by auto.
    eapply execution_r_join; eauto.
    replace (Reset :: nil) with (nil ++ (@Reset I O :: nil)) by auto.
    eauto with machine.
Qed.

#[export] Hint Resolve execution_execution_r : machine.

Theorem refines_forward_simulation :
  forall (I O : Type) (M1 M2 : machine I O),
    deterministic M2 ->
    no_reset M1 ->
    no_reset M2 ->
    refines M1 M2 ->
    exists (R : M1.(state) -> M2.(state) -> Prop),
      forward_simulation_relation R.
Proof.
  intros I O M1 M2 Hdet Hreset1 Hreset2 H.
  exists (fun m1 m2 =>
       m1 = M1.(init) /\ m2 = M2.(init) \/
         exists io, execution_r M1 M1.(init) io m1 /\
                 execution_r M2 M2.(init) io m2).
  split; try solve [ auto ].
  split.
  - intros s1 i o s1' s2 HR Hstep.
    destruct HR as [Hinit | Hhist].
    + destruct Hinit; subst.
      specialize (H (IO i o :: nil) ltac:(eauto with machine)).
      destruct H as [s2' H].
      inversion H; subst.
      eexists.
      split.
      * eauto.
      * right.
        exists (IO i o :: nil).
        split; eauto with machine.
    + destruct Hhist as [io [Hexec1 Hexec2]].
      specialize (H (io ++ IO i o :: nil)).
      assert (execution_r M1 (init M1) (io ++ IO i o :: nil) s1') as Hexec1' by eauto with machine.
      apply execution_r_execution in Hexec1'.
      specialize (H (ex_intro _ s1' Hexec1')).
      unfold in_traces in H.
      destruct H as [s2' Hs2'].
      apply execution_execution_r in Hs2'.
      inversion Hs2'.
      1: { destruct io; simpl in *; congruence. }
      2: { apply app_inj_tail in H; destruct H; congruence. }
      subst.
      apply app_inj_tail in H.
      destruct H.
      subst.
      inversion H1; clear H1; subst.
      (* given the same inputs, final state must match *)
      assert (s2 = s').
      * clear - Hexec2 H0 Hdet Hreset2.
        generalize dependent Hexec2.
        generalize dependent H0.
        generalize dependent s2.
        generalize dependent s'.
        induction io using rev_ind.
        -- intros s s' H H'.
           inversion H; inversion H'; subst; auto; destruct tr; simpl in *; congruence.
        -- intros s s' H H'.
           destruct x.
           ++ inversion H.
              1:{ destruct io; simpl in *; congruence. }
              2:{ apply app_inj_tail in H0; destruct H0; congruence. }
              inversion H'.
              1:{ destruct io; simpl in *; congruence. }
              2:{ apply app_inj_tail in H5; destruct H5; congruence. }
              apply app_inj_tail in H0.
              apply app_inj_tail in H5.
              intuition.
              inversion H11; inversion H12; subst.
              specialize (IHio _ _ H1 H6); subst.
              specialize (Hdet _ _ _ _ H3 H8).
              inversion Hdet; reflexivity.
           ++ (* both are reset, nothing changes, can use IH *)
             inversion H.
             1:{ destruct io; simpl in *; congruence. }
             1:{ apply app_inj_tail in H0; destruct H0; congruence. }
             inversion H'.
             1:{ destruct io; simpl in *; congruence. }
             1:{ apply app_inj_tail in H5; destruct H5; congruence. }
             apply app_inj_tail in H0.
             apply app_inj_tail in H5.
             intuition.
             rewrite Hreset2 in H8.
             rewrite Hreset2 in H3.
             subst.
             eauto with machine.
      * subst.
        eexists.
        split.
        -- eauto.
        -- right.
           eexists; eauto with machine.
  - intros s1 s1' s2 HR Hreset.
    rewrite Hreset2.
    rewrite Hreset1 in Hreset; subst.
    eexists; eauto.
Qed.

Definition backward_simulation_relation
  {I O : Type} {M1 M2 : machine I O}
  (R : M1.(state) -> M2.(state) -> Prop) :=
  (* R is total *)
  (forall s1, exists s2, R s1 s2) /\
    (* start *)
    (forall s2, R M1.(init) s2 -> s2 = M2.(init)) /\
    (* step *)
    (forall s1 i o s1' s2',
        R s1' s2' ->
        M1.(step) s1 i (Result o s1') ->
        exists s2, M2.(step) s2 i (Result o s2') /\ R s1 s2) /\
    (* reset *)
    (forall s1 s1' s2',
        R s1' s2' ->
        M1.(reset) s1 s1' ->
        exists s2, M2.(reset) s2 s2' /\ R s1 s2).

Lemma backward_simulate :
  forall (I O : Type) (M1 M2 : machine I O)
    (R : M1.(state) -> M2.(state) -> Prop),
    backward_simulation_relation R ->
    forall s1 io s1' s2',
      R s1' s2' ->
      execution M1 s1 io s1' ->
      exists s2,
        R s1 s2 /\ execution M2 s2 io s2'.
Proof.
  intros I O M1 M2 R H s1 io s1' s2' HR Hexec.
  induction Hexec.
  - eauto with machine.
  - specialize (IHHexec HR).
    destruct IHHexec as [? [HR' ?]].
    destruct H as (_ & _ & Hstep & _).
    specialize (Hstep _ _ _ _ _ HR' H0).
    destruct Hstep as [? [? ?]].
    eauto with machine.
  - specialize (IHHexec HR).
    destruct IHHexec as [? [HR' ?]].
    destruct H as (_ & _ & _ & Hreset).
    specialize (Hreset _ _ _ HR' H0).
    destruct Hreset as (? & ? & ?).
    eauto with machine.
Qed.

Theorem backward_simulation :
  forall (I O : Type) (M1 M2 : machine I O)
    (R : M1.(state) -> M2.(state) -> Prop),
    backward_simulation_relation R ->
    refines M1 M2.
Proof.
  intros I O M1 M2 R HR.
  unfold refines, in_traces.
  intros io Hexec.
  destruct Hexec as [s1f Hexec].
  pose proof (backward_simulate _ _ _ _ _ HR) as Hback.
  destruct HR as [Htotal [Hinit Hstep]].
  destruct (Htotal s1f) as [s2f HRf].
  specialize (Hback _ _ _ s2f HRf Hexec).
  destruct Hback as [s2 [Hinit2 Hexec2]].
  specialize (Hinit s2).
  specialize (Hinit Hinit2).
  subst; eauto.
Qed.
