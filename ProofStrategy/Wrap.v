Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Utils.

Require Import List.
Require Import Program.Equality.

Section WRAP.

  Lemma wrap_driver_helper :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M : machine (I2 + I1) (O2 + O1))
      (d23 : driver I2 O2 I3 O3) ds tr dsf,
      execution (add_driver M d23) ds tr dsf ->
      exists trd,
        execution M (driver_state_proj ds) trd (driver_state_proj dsf) /\
          forall (M' : machine (I2 + I1) (O2 + O1)) s' sf',
            execution M' s' trd sf' ->
            execution (add_driver M' d23) (driver_state_inj ds s') tr (driver_state_inj dsf sf').
  Proof.
    intros.
    dependent induction H.
    { eexists. split; [ econstructor | ].
      intros. inversion H; clear H; subst. econstructor. }
    - (* step *)
      inversion H; clear H; subst;
        destruct IHexecution as (trd & Htrd & IH).
      + eexists (IO _ _ :: trd); split.
        { econstructor; eauto. }
        intros M' s' sf' H.
        specialize (IH M').
        inversion H; clear H; subst.
        specialize (IH _ _ H8).
        econstructor. { econstructor; eauto. }
        eauto.
      + eexists (IO _ _ :: trd); split.
        { econstructor; eauto. }
        intros M' s' sf' H.
        specialize (IH M').
        inversion H; clear H; subst.
        specialize (IH _ _ H8).
        econstructor. { econstructor; eauto. }
        eauto.
      + eapply dexec_dexec_trace in H6.
        destruct H6 as (dtr & Hexec & Htr).
        eexists ((Reset :: _) ++ _); split.
        { eapply execution_join; eauto.
          econstructor; eauto. }
        intros M' s' sf' H.
        eapply execution_split in H.
        destruct H as (? & He1 & He2).
        specialize (IH M' _ _ He2).
        econstructor.
        2:{ eassumption. }
        inversion He1; subst.
        econstructor; eauto.
        eapply dexec_dexec_trace.
        eauto.
      + eapply dexec_dexec_trace in H4.
        destruct H4 as (dtr & Hexec & Htr).
        eexists (_ ++ _); split.
        { eapply execution_join; eauto. }
        intros M' s' sf' H.
        eapply execution_split in H.
        destruct H as (? & He1 & He2).
        specialize (IH _ _ _ He2).
        econstructor. 2:{ eassumption. }
        econstructor.
        eapply dexec_dexec_trace.
        eauto.
    - (* reset, makes underlying machine reset *)
      destruct IHexecution as (trd & He & IH).
      exists (Reset :: trd).
      split.
      + econstructor; eauto.
        destruct s, s'; simpl in *; tauto.
      + intros M' s'0 sf' H1.
        inversion H1; subst.
        specialize (IH _ _ _ H5).
        econstructor.
        2:{ eassumption. }
        destruct s, s'; tauto.
  Qed.

  Lemma wrap_driver :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M1 M2 : machine (I2 + I1) (O2 + O1))
      (d23 : driver I2 O2 I3 O3),
      equivalent M1 M2 ->
      equivalent
        (add_driver M1 d23)
        (add_driver M2 d23).
  Proof.
    intros I1 O1 I2 O2 I3 O3 M1 M2 d23 H.
    unfold equivalent in  *; intuition.
    - clear H1. revert H0.
      unfold refines.
      unfold in_traces.
      simpl.
      generalize (init M1). generalize (init M2).
      intros.
      destruct H as (? & He).
      eapply wrap_driver_helper in He.
      destruct He as (? & He & Hinv).
      edestruct H0 as (? & He2).
      { eexists. eauto. }
      specialize (Hinv _ _ _ He2).
      eexists. eauto.
    - clear H0. revert H1.
      unfold refines.
      unfold in_traces.
      simpl.
      generalize (init M1). generalize (init M2).
      intros.
      destruct H as (? & He).
      eapply wrap_driver_helper in He.
      destruct He as (? & He & Hinv).
      edestruct H1 as (? & He2).
      { eexists. eauto. }
      specialize (Hinv _ _ _ He2).
      eexists. eauto.
  Qed.

  Lemma wrap_emulator_helper :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M : machine (I3 + I2) (O3 + O2))
      (e21 : emulator I2 O2 I1 O1) es tr esf,
      execution (add_emulator M e21) es tr esf ->
      exists tre,
        execution M (emulator_state_proj es) tre (emulator_state_proj esf) /\
          forall (M' : machine (I3 + I2) (O3 + O2)) s' sf',
            execution M' s' tre sf' ->
            execution (add_emulator M' e21) (emulator_state_inj es s') tr (emulator_state_inj esf sf').
  Proof.
    intros.
    dependent induction H.
    { eexists. split; [ econstructor | ].
      intros. inversion H; clear H; subst. econstructor. }
    - (* step *)
      inversion H; clear H; subst;
        destruct IHexecution as (tre & Htre & IH).
      + eexists (IO _ _ :: tre); split.
        { econstructor; eauto. }
        intros M' s' sf' H.
        specialize (IH M').
        inversion H; clear H; subst.
        specialize (IH _ _ H8).
        econstructor. { econstructor; eauto. }
        eauto.
      + eexists (Reset :: IO _ _ :: tre); split.
        { econstructor; eauto.
          econstructor; eauto. }
        intros M' s' sf' H.
        specialize (IH M').
        inversion H; clear H; subst.
        inversion H4; clear H4; subst.
        specialize (IH _ _ H10).
        econstructor. { econstructor; eauto. }
        eauto.
      + eapply eexec_eexec_trace in H4.
        destruct H4 as (etr & Hexec & Htr).
        eexists (_ ++ _); split.
        { eapply execution_join; eauto. }
        intros M' s' sf' H.
        eapply execution_split in H.
        destruct H as (? & He1 & He2).
        specialize (IH M' _ _ He2).
        econstructor.
        2:{ eassumption. }
        simpl.
        constructor.
        eapply eexec_eexec_trace.
        eauto.
      + eapply eexec_eexec_trace in H4.
        destruct H4 as (dtr & Hexec & Htr).
        eexists (_ ++ _); split.
        { eapply execution_join; eauto. }
        intros M' s' sf' H.
        eapply execution_split in H.
        destruct H as (? & He1 & He2).
        specialize (IH _ _ _ He2).
        econstructor. 2:{ eassumption. }
        econstructor.
        eapply eexec_eexec_trace.
        eauto.
    - (* reset, makes underlying machine reset *)
      destruct IHexecution as (tre & He & IH).
      exists (Reset :: tre).
      split.
      + econstructor; eauto.
        destruct s, s'; simpl in *; tauto.
      + intros M' s'0 sf' H1.
        inversion H1; subst.
        specialize (IH _ _ _ H5).
        econstructor.
        2:{ eassumption. }
        destruct s, s'; tauto.
  Qed.

  Lemma wrap_emulator :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M1 M2 : machine (I3 + I2) (O3 + O2))
      (e21 : emulator I2 O2 I1 O1),
      equivalent M1 M2 ->
      equivalent
        (add_emulator M1 e21)
        (add_emulator M2 e21).
  Proof.
    intros I1 O1 I2 O2 I3 O3 M1 M2 e21 H.
    unfold equivalent in  *; intuition.
    - clear H1. revert H0.
      unfold refines.
      unfold in_traces.
      simpl.
      generalize (init M1). generalize (init M2).
      intros.
      destruct H as (? & He).
      eapply wrap_emulator_helper in He.
      destruct He as (? & He & Hinv).
      edestruct H0 as (? & He2).
      { eexists. eauto. }
      specialize (Hinv _ _ _ He2).
      eexists. eauto.
    - clear H0. revert H1.
      unfold refines.
      unfold in_traces.
      simpl.
      generalize (init M1). generalize (init M2).
      intros.
      destruct H as (? & He).
      eapply wrap_emulator_helper in He.
      destruct He as (? & He & Hinv).
      edestruct H1 as (? & He2).
      { eexists. eauto. }
      specialize (Hinv _ _ _ He2).
      eexists. eauto.
  Qed.

End WRAP.
