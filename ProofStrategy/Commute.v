Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Tactics.
Require Import IPR.Utils.

Require Import Program.Equality.

Section COMMUTE.

  Lemma eexec_wrap_driver :
    forall (O1 I2 O2 I3 O3 ES : Type)
      (M2 : machine (I2 + I2) (O2 + O2))
      (d23 : driver I2 O2 I3 O3)
      (estep : eproc ES I2 O2 O1)
      ol ms ds es ms' es',
      eexec M2 O1 estep (ms, es) (Result ol (ms', es')) ->
      driver_state_proj ds = ms ->
      exists ds',
        (driver_state_proj ds' = ms') /\
          eexec (add_driver M2 d23) O1 estep (ds, es) (Result ol (ds', es')).
  Proof.
    intros O1 I2 O2 I3 O3 ES M2 d23 estep ol ms ds es ms' es' H H0.
    (* we need to do induction over the derivation of the execution,
       not just over the structure of estep, because of the while loop *)
    dependent induction H.
    - exists (DriverLow ms'); split; auto.
      destruct ds; subst;
        repeat constructor; auto.
    - exists ds; split; auto.
      constructor.
    - exists ds; split; auto.
      constructor; auto.
    - exists ds; split; auto.
      constructor.
    - destruct s'.
      specialize (IHeexec1 _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H1).
      destruct IHeexec1 as [ds' [? ?]].
      specialize (IHeexec2 _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H2).
      destruct IHeexec2 as [ds'' [? ?]].
      exists ds''.
      split; auto.
      econstructor; eauto.
    - destruct s', s''.
      specialize (IHeexec1 _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H2).
      destruct IHeexec1 as [ds' [? ?]].
      specialize (IHeexec2 _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H3).
      destruct IHeexec2 as [ds'' [? ?]].
      specialize (IHeexec3 _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H5).
      destruct IHeexec3 as [ds''' [? ?]].
      exists ds'''.
      split; auto.
      econstructor; eauto.
    - specialize (IHeexec _ _ _ _ d23 _ _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl H0).
      destruct IHeexec as [ds' [? ?]].
      exists ds'.
      split; auto.
      solve [ econstructor; eauto ].
  Qed.

  Lemma dexec_unwrap_emulator :
    forall (I1 O1 I2 O2 O3 : Type)
      (M2 : machine (I2 + I2) (O2 + O2))
      (dstep : dproc I2 O2 O3)
      (e21 : emulator I2 O2 I1 O1)
      m o2 s',
      dexec (add_emulator M2 e21) O3 dstep (EmulatorHigh m) (Result o2 s') ->
      exists ms',
        s' = EmulatorHigh ms' /\
          dexec M2 O3 dstep m (Result o2 ms').
  Proof.
    intros I1 O1 I2 O2 O3 M2 dstep e21 m o2 s' H.
    dependent induction H.
    - inv_exec H.
      eexists; split; eauto with driver.
    - eauto with driver.
    - destruct (IHdexec1 _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      destruct (IHdexec2 _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      eauto with driver.
    - destruct (IHdexec1 _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      destruct (IHdexec2 _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      destruct (IHdexec3 _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      eauto with driver.
    - destruct (IHdexec _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      eauto with driver.
    - destruct (IHdexec _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      eauto with driver.
    - destruct (IHdexec _ _ _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ?).
      subst.
      eauto with driver.
  Qed.

  Lemma dexec_wrap_emulator :
    forall (I1 O1 I2 O2 O3 : Type)
      (M2 : machine (I2 + I2) (O2 + O2))
      (dstep : dproc I2 O2 O3)
      (e21 : emulator I2 O2 I1 O1)
      s o2 s',
      dexec M2 O3 dstep s (Result o2 s') ->
      dexec (add_emulator M2 e21) O3 dstep (EmulatorHigh s) (Result o2 (EmulatorHigh s')).
  Proof.
    intros I1 O1 I2 O2 O3 M2 dstep e21 s o2 s' H.
    dependent induction H.
    - repeat constructor; auto.
    - eauto with driver.
    - specialize (IHdexec1 _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      specialize (IHdexec2 _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      eauto with driver.
    - specialize (IHdexec1 _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      specialize (IHdexec2 _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      specialize (IHdexec3 _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      eauto with driver.
    - specialize (IHdexec _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      eauto with driver.
    - specialize (IHdexec _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      eauto with driver.
    - specialize (IHdexec _ e21 _ _ _ eq_refl eq_refl JMeq_refl JMeq_refl JMeq_refl).
      eauto with driver.
  Qed.

  Lemma eexec_unwrap_driver :
    forall (O1 I2 O2 I3 O3 ES : Type)
      (M2 : machine (I2 + I2) (O2 + O2))
      (d23 : driver I2 O2 I3 O3)
      (estep : eproc ES I2 O2 O1)
      ds es o1 ds' es',
      eexec (add_driver M2 d23) O1 estep (ds, es) (Result o1 (ds', es')) ->
      eexec M2 O1 estep (driver_state_proj ds, es) (Result o1 (driver_state_proj ds', es')).
  Proof.
    intros O1 I2 O2 I3 O3 ES M2 d23 estep ds es o1 ds' es' H.
    dependent induction H.
    - constructor.
      destruct ds; inv_exec H; subst; simpl; auto.
    - eauto with emulator.
    - eauto with emulator.
    - eauto with emulator.
    - destruct s'.
      specialize (IHeexec1 _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      specialize (IHeexec2 _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      eauto with emulator.
    - destruct s', s''.
      specialize (IHeexec1 _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      specialize (IHeexec2 _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      specialize (IHeexec3 _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      eauto with emulator.
    - specialize (IHeexec _ _ _ _ _ _ _ eq_refl JMeq_refl JMeq_refl).
      eauto with emulator.
  Qed.

  Lemma wrap_comm :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M2 : machine (I2 + I2) (O2 + O2))
      (d23 : driver I2 O2 I3 O3)
      (e21 : emulator I2 O2 I1 O1),
      equivalent
        (add_driver (add_emulator M2 e21) d23)
        (add_emulator (add_driver M2 d23) e21).
  Proof.
    intros I1 O1 I2 O2 I3 O3 M2 d23 e21.
    split.
    - apply forward_simulation
        with (R := fun s t =>
                     match s with
                     | DriverHigh (EmulatorHigh m) => t = EmulatorHigh (DriverHigh m)
                     | DriverLow (EmulatorLow m e) => t = EmulatorLow (DriverHigh m) e \/ t = EmulatorLow (DriverLow m) e
                     | _ => False
                     end).
      unfold forward_simulation_relation; repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [ [m1 | m1 e1] | [m1 | m1 e1] ],
            s2 as [ [m2 | m2] | dm2 e2 ];
          try tauto;
          try solve [ inversion HR; discriminate ].
        * (* in high-level mode *)
          inversion HR; clear HR; subst.
          destruct i;
            inversion Hstep; clear Hstep; subst.
          -- (* got high-level input *)
            destruct (dexec_unwrap_emulator _ _ _ _ _ _ _ _ _ _ _ H2) as (s2' & Heq & Hexec').
            subst.
            eexists (EmulatorHigh (DriverHigh s2')).
            split; auto.
            repeat constructor; auto.
          -- (* got low-level input *)
            inversion H2; clear H2; subst.
            destruct (eexec_wrap_driver _ _ _ _ _ _ _ d23 _ _ _ (DriverHigh m1) _ _ _ H3 ltac:(auto)) as [s2' [Heq Hexec']].
            exists (EmulatorLow s2' es).
            split.
            ++ constructor; auto.
            ++ destruct s2'; subst; auto.
        * (* in low-level mode *)
          destruct i;
            inversion Hstep; clear Hstep; subst.
          -- (* got high-level input *)
            simpl in H3.
            destruct s'; try tauto.
            destruct (dexec_unwrap_emulator _ _ _ _ _ _ _ _ _ _ _ H4) as (s2' & Heq & Hexec').
            subst.
            exists (EmulatorHigh (DriverHigh s2')).
            split; auto.
            apply EmulatorStepLowHigh with (ms' := DriverHigh s);
              [ | constructor; auto ].
            destruct HR; inversion H; auto.
          -- (* got low-level input *)
            inversion H2; clear H2; subst.
            destruct (eexec_wrap_driver _ _ _ _ _ _ _ d23 _ _ _ dm2 _ _ _ H0 ltac:(inversion HR; inversion H; subst; auto)) as [s2' [Heq Hexec']].
            exists (EmulatorLow s2' es').
            split.
            ++ destruct s2'; inversion HR; inversion H; subst; constructor; auto.
            ++ destruct s2'; subst; auto.
      + (* reset *)
        intros s1 s1' s2 H H0.
        unfold driver_reset, emulator_reset in *.
        simpl in *.
        unfold driver_reset, emulator_reset in *.
        destruct s1 as [[] | []], s1' as [[] | []], s2 as [[] | []];
          inversion H; try inversion H1; subst;
          try tauto;
          try discriminate;
          eexists; split; eauto;
          simpl; eauto.
    - apply forward_simulation
        with (R := fun s t =>
                     match s with
                     | EmulatorHigh (DriverHigh m) => t = DriverHigh (EmulatorHigh m)
                     | EmulatorLow (DriverHigh m) e => t = DriverLow (EmulatorLow m e)
                     | EmulatorLow (DriverLow m) e => t = DriverLow (EmulatorLow m e)
                     | _ => False
                     end).
      unfold forward_simulation_relation; repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [ [m1 | m1] | dm1 e1 ];
          try tauto;
          try solve [ inversion HR; discriminate ].
        * (* in high-level mode *)
          subst.
          destruct i;
            inversion Hstep; clear Hstep; subst.
          -- (* got high-level input *)
            inversion H2; clear H2; subst.
            pose proof (dexec_wrap_emulator _ _ _ _ _ _ _ e21 _ _ _ H3).
            eexists; split; eauto.
            constructor.
            auto.
          -- (* got low-level input *)
            pose proof (eexec_unwrap_driver _ _ _ _ _ _ _ d23 _ _ _ _ _ _ H2).
            exists (DriverLow (EmulatorLow (driver_state_proj ms') es)).
            split.
            ++ repeat constructor; auto.
            ++ destruct ms'; simpl; auto.
        * (* in low-level mode *)
          destruct i;
            inversion Hstep; clear Hstep; subst.
          -- (* got high-level input *)
            simpl in H3; unfold driver_reset in H3.
            destruct ms'; simpl in H3; [ | destruct dm1; tauto ].
            inversion H5; clear H5; subst.
            eexists; split; eauto.
            pose proof (dexec_wrap_emulator _ _ _ _ _ _ _ e21 _ _ _ H2).
            destruct dm1; subst.
            ++ econstructor; eauto.
               simpl; auto.
            ++ econstructor; eauto.
               simpl; auto.
          -- (* got low-level input *)
            pose proof (eexec_unwrap_driver _ _ _ _ _ _ _ d23 _ _ _ _ _ _ H0).
            exists (DriverLow (EmulatorLow (driver_state_proj ms') es')).
            split.
            ++ destruct dm1; subst; repeat constructor; auto.
            ++ destruct ms'; simpl; auto.
      + (* reset *)
        intros s1 s1' s2 H H0.
        unfold driver_reset, emulator_reset in *.
        simpl in *.
        unfold driver_reset, emulator_reset in *.
        destruct s1 as [[] | []], s1' as [[] | []], s2 as [[] | []];
          inversion H; try inversion H1; subst;
          try tauto;
          try discriminate;
          eexists; split; eauto;
          simpl; eauto.
  Qed.

End COMMUTE.
