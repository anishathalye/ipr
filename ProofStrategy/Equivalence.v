Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.ProofStrategy.Self.
Require Import IPR.ProofStrategy.Wrap.

Require Import List.
Require Import Program.Equality.

Section EQUIVALENT.

  Definition well_formed1 {Il Ol Ir Or : Type} (evt : event (Il + Ir) (Ol + Or)) : Prop :=
    match evt with
    | IO l r =>
        match (l, r) with
        | (inl _, inl _) => True
        | (inr _, inr _) => True
        | _ => False
        end
    | Reset => True
    end.

  Inductive well_formed {Il Ol Ir Or : Type} : trace (Il + Ir) (Ol + Or) -> Prop :=
  | WellFormedEmpty : well_formed nil
  | WellFormedApp :
    forall evt tr,
      well_formed1 evt ->
      well_formed tr ->
      well_formed (tr ++ evt :: nil)
  .

  Lemma in_traces_real_well_formed :
    forall Ir Or I1 O1 (M : machine (I1 + Ir) (O1 + Or)) tr,
      in_traces (add_driver M (identity_driver I1 O1)) tr ->
      well_formed tr.
  Proof.
    intros Ir Or I1 O1 M tr H.
    destruct H as [sf Htr].
    apply execution_execution_r in Htr.
    induction Htr.
    - constructor.
    - constructor; auto.
      inversion H; simpl; auto.
    - constructor; simpl; tauto.
  Qed.

  Lemma in_traces_ideal_well_formed :
    forall Il Ol I2 O2 (M : machine (Il + I2) (Ol + O2)) tr,
      in_traces (add_emulator M (identity_emulator I2 O2)) tr ->
      well_formed tr.
  Proof.
    intros Il Ol I2 O2 M io H.
    destruct H as [sf Htr].
    apply execution_execution_r in Htr.
    induction Htr.
    - constructor.
    - constructor; auto.
      inversion H; simpl; auto.
    - constructor; simpl; tauto.
  Qed.

  Definition collapse1 {A : Type} (x : A + A) : A :=
    match x with
    | inl x => x
    | inr x => x
    end.

  Definition collapse_event {I O : Type} (evt : event (I + I) (O + O)) : event I O :=
    match evt with
    | IO i o => IO (collapse1 i) (collapse1 o)
    | Reset => Reset
    end.

  Definition collapse {I O : Type} (tr : trace (I + I) (O + O)) : trace I O :=
    map collapse_event tr.

  Lemma collapse_snoc :
    forall I O (tr : trace (I + I) (O + O)) (evt : event (I + I) (O + O)),
      collapse (tr ++ evt :: nil) = collapse tr ++ collapse_event evt :: nil.
  Proof.
    intros I O ios io.
    unfold collapse.
    rewrite map_app.
    auto.
  Qed.

  Lemma in_traces_collapse :
    forall I O (M : machine I O) io,
      well_formed io ->
      in_traces (mux M) io <->
      in_traces M (collapse io).
  Proof.
    intros I O M io Hwf.
    split.
    - clear Hwf.
      intros [sf' Hexec'].
      apply execution_execution_r in Hexec'.
      unfold in_traces.
      remember (init (mux M)) as s0'.
      remember (init M) as s0.
      assert (s0 = s0') by (subst; auto).
      clear Heqs0 Heqs0'.
      cut (exists sf, execution_r M s0 (collapse io) sf /\ sf = sf').
      + intros.
        destruct H0 as [sf [Hexec Heq]].
        subst.
        eauto with machine.
      + generalize dependent H.
        generalize dependent s0.
        induction Hexec'; eauto with machine.
        * intros s0 H0.
          destruct (IHHexec' _ H0) as [sf [Hexec Heq]].
          eexists; split; eauto.
          rewrite collapse_snoc.
          econstructor; eauto.
          inversion H; subst; auto.
        * intros s0 H0.
          destruct (IHHexec' _ H0) as [sf [Hexec Heq]].
          eexists; split; eauto.
          rewrite collapse_snoc.
          econstructor; eauto.
          simpl in *; subst; auto.
    - intros [sf Hexec].
      apply execution_execution_r in Hexec.
      unfold in_traces.
      remember (init (mux M)) as s0'.
      remember (init M) as s0.
      assert (s0 = s0') by (subst; auto).
      clear Heqs0 Heqs0'.
      cut (exists sf', execution_r (mux M) s0 io sf /\ sf = sf').
      + intros.
        destruct H0 as [sf' [Hexec' Heq]].
        subst.
        eauto with machine.
      + remember (collapse io) as io'.
        generalize dependent Heqio'.
        generalize dependent H.
        generalize dependent s0'.
        generalize dependent io.
        induction Hexec.
        * intros io Hwf s0' H Heqio'.
          exists s0'.
          split; auto.
          destruct io; simpl in *; try congruence.
          eauto with machine.
        * intros io0 Hwf s0' H0 Heqio'.
          destruct io0 as [ | evt' tr' ] using rev_ind;
            try solve [ destruct tr; simpl in *; congruence ].
          clear IHtr'. (* don't need this *)
          unfold collapse in Heqio'.
          rewrite map_app in Heqio'.
          apply app_inj_tail in Heqio'.
          destruct Heqio' as [Heqios' Heqio'].
          inversion Hwf; try solve [ destruct tr'; simpl in *; congruence ].
          apply app_inj_tail in H1.
          destruct H1.
          rewrite <- H1 in Heqios'.
          destruct (IHHexec _ H3 _ H0 Heqios') as [sf' [Hexec' Heq']].
          eexists; split; auto.
          subst.
          destruct evt' as [ i' o' | ]; simpl in *; try congruence.
          destruct i', o'; simpl in *; try tauto;
            inversion Heqio'; subst;
            econstructor; eauto;
            simpl;
            eauto with ipr.
        * intros io Hwf s0' H0 Heqio'.
          destruct io as [ | evt' tr' ] using rev_ind;
            try solve [ destruct tr; simpl in *; congruence ].
          clear IHtr'. (* don't need this *)
          unfold collapse in Heqio'.
          rewrite map_app in Heqio'.
          apply app_inj_tail in Heqio'.
          destruct Heqio' as [Heqios' Heqio'].
          inversion Hwf; try solve [ destruct tr'; simpl in *; congruence ].
          apply app_inj_tail in H1.
          destruct H1.
          rewrite <- H1 in Heqios'.
          destruct (IHHexec _ H3 _ H0 Heqios') as [sf' [Hexec' Heq']].
          eexists; split; auto.
          subst.
          destruct evt' as [ i' o' | ]; simpl in *; try congruence.
          eauto with machine.
  Qed.

  Lemma in_traces_mux_well_formed :
    forall I O (M : machine I O) io,
      in_traces (mux M) io ->
      well_formed io.
  Proof.
    intros I O M io H.
    unfold in_traces in H.
    destruct H as [sf Hexec].
    apply execution_execution_r in Hexec.
    remember (init (mux M)) as s0.
    clear Heqs0.
    induction Hexec.
    - constructor.
    - constructor; auto.
      inversion H; subst; simpl; auto.
    - constructor; simpl; tauto.
  Qed.

  Lemma equivalent_mux_equivalent :
    forall I O (M1 M2 : machine I O),
    equivalent M1 M2 ->
    equivalent (mux M1) (mux M2).
  Proof.
    intros I O M1 M2 H.
    split.
    - intros io Hio.
      pose proof (in_traces_mux_well_formed _ _ _ _ Hio).
      apply in_traces_collapse; auto.
      apply H.
      apply in_traces_collapse; auto.
    - intros io Hio.
      pose proof (in_traces_mux_well_formed _ _ _ _ Hio).
      apply in_traces_collapse; auto.
      apply H.
      apply in_traces_collapse; auto.
  Qed.

  Theorem IPR_by_equivalence :
    forall I O (M1 M2 : machine I O),
      equivalent M1 M2 ->
      IPR M1 M2 (identity_driver I O).
  Proof.
    intros I O M1 M2 Heq.
    apply equivalent_mux_equivalent in Heq.
    exists (identity_emulator I O).
    simpl.
    eapply equivalent_trans.
    { apply wrap_driver. apply Heq. }
    unfold ideal_world.
    apply IPR_self'.
  Qed.

End EQUIVALENT.
