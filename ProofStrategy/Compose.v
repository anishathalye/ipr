Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Tactics.
Require Import IPR.Utils.

Require Import Program.Equality.

Section COMPOSE.

  Lemma dexec_unwrap_driver :
    forall (Ir Or I1 O1 I2 O2 I3 O3 : Type)
      (M1 : machine (I1 + Ir) (O1 + Or))
      (d12 : driver I1 O1 I2 O2) (d23 : driver I2 O2 I3 O3)
      s i o s',
    dexec (add_driver M1 d12) O3 (d23 i) (DriverHigh s) (Result o s') ->
    exists s'',
      s' = DriverHigh s'' /\
        dexec M1 O3 ((d12 ∘ d23)%dproc i) s (Result o s'').
  Proof.
    intros Ir Or I1 O1 I2 O2 I3 O3 M1 d12 d23 s i o s' H.
    unfold driver_compose.
    remember (d23 i) as d23i eqn:Heqd23i.
    clear Heqd23i.
    dependent induction H.
    - inversion H; subst.
      eauto.
    - eexists; split; eauto.
      constructor.
    - specialize (IHdexec1 _ _ _ _ (fun _ => p) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec1 as (? & ? & ?); subst.
      specialize (IHdexec2 _ _ _ _ d23 _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec2 as (? & ? & ?).
      eexists; split; eauto.
      eauto with driver.
    - specialize (IHdexec1 _ _ _ _ (fun _ => g) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec1 as (? & ? & ?); subst.
      specialize (IHdexec2 _ _ _ _ (fun _ => b) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec2 as (? & ? & ?); subst.
      specialize (IHdexec3 _ _ _ _ (fun _ => b) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec3 as (? & ? & ?); subst.
      eexists; split; auto.
      eauto with driver.
    - specialize (IHdexec _ _ _ _ (fun _ => g) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec as (? & ? & ?); subst.
      eexists; split; auto.
      eauto with driver.
    - specialize (IHdexec _ _ _ _ (fun _ => p) _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec as (? & ? & ?); subst.
      eexists; split; eauto.
      eauto with driver.
    - specialize (IHdexec _ _ _ _ (fun _ => p') _ i _ _ eq_refl JMeq_refl JMeq_refl).
      destruct IHdexec as (? & ? & ?); subst.
      eexists; split; eauto.
      eauto with driver.
  Qed.

  Lemma dexec_wrap_driver :
    forall (Ir Or I1 O1 I2 O2 I3 O3 : Type)
      (M1 : machine (I1 + Ir) (O1 + Or))
      (d12 : driver I1 O1 I2 O2) (d23 : driver I2 O2 I3 O3)
      s i o s',
      dexec M1 O3 ((d12 ∘ d23)%dproc i) s (Result o s') ->
      dexec (add_driver M1 d12) O3 (d23 i) (DriverHigh s) (Result o (DriverHigh s')).
  Proof.
    intros Ir Or I1 O1 I2 O2 I3 O3 M1 d12 d23 s i o s' H.
    unfold driver_compose in H.
    remember (d23 i) as d23i eqn:Heqd23i; clear Heqd23i.
    clear d23.
    generalize dependent H.
    generalize dependent s'.
    generalize dependent s.
    induction d23i; intros; simpl in *.
    - constructor.
      simpl.
      auto with ipr.
    - rinv_dexec_head.
      auto with driver.
    - inv_exec H0.
      specialize (H _ _ _ _ H8).
      specialize (IHd23i _ _ _ H6).
      eauto with driver.
    - (* inversion is not enough, we need to do induction over the derivation of the execution for the while loop *)
      dependent induction H.
      + specialize (IHdexec3 _ _ _ i tt _ _ IHd23i1 IHd23i2 _ eq_refl JMeq_refl JMeq_refl).
        specialize (IHd23i1 _ _ _ H).
        specialize (IHd23i2 _ _ _ H0).
        eauto with driver.
      + specialize (IHd23i1 _ _ _ H).
        eauto with driver.
    - inv_exec H.
      + specialize (IHd23i1 _ _ _ H4).
        eauto with driver.
      + specialize (IHd23i2 _ _ _ H4).
        eauto with driver.
  Qed.

  Lemma driver_compose_wrap_add_driver :
    forall (Ir Or I1 O1 I2 O2 I3 O3 : Type)
      (M1 : machine (I1 + Ir) (O1 + Or))
      (d12 : driver I1 O1 I2 O2) (d23 : driver I2 O2 I3 O3),
      equivalent
        (add_driver M1 (d12 ∘ d23)%dproc)
        (add_driver (add_driver M1 d12) d23).
  Proof.
    intros Ir Or I1 O1 I2 O2 I3 O3 M1 d12 d23.
    split.
    - apply forward_simulation
        with (R := fun s t =>
                     match s with
                     | DriverHigh m => t = DriverHigh (DriverHigh m)
                     | DriverLow m => t = DriverLow (DriverLow m)
                     end).
      repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1].
        * (* was in high-level mode *)
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; subst.
            pose proof (dexec_wrap_driver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2).
            eexists; split; eauto.
            eauto with ipr.
          -- inversion Hstep; subst.
             eexists; split; eauto.
             constructor.
             simpl.
             auto with ipr.
        * (* was in low-level mode *)
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; subst.
            pose proof (dexec_wrap_driver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4).
            eexists; split; eauto.
            econstructor; eauto.
            simpl; auto.
          -- inversion Hstep; subst.
             eexists; split; eauto.
             constructor.
             simpl.
             auto with ipr.
      + intros s1 s1' s2 H H0.
        destruct s1, s1', s2;
          inversion H; subst;
          eexists; split; eauto;
          simpl; eauto;
          tauto.
    - apply forward_simulation
        with (R := fun s t =>
                     match s with
                     | DriverHigh (DriverHigh m) => t = DriverHigh m
                     | DriverLow (DriverLow m) => t = DriverLow m
                     | _ => False
                     end).
      repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1].
        * (* was in high-level mode *)
          destruct s1 as [s1 | s1]; try tauto.
          subst.
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; subst.
            destruct (dexec_unwrap_driver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2) as [s2' [Heq Hstep']].
            subst.
            eauto with ipr.
          -- inversion Hstep; subst.
             inversion H2; subst.
             eauto with ipr.
        * (* was in low-level mode *)
          destruct s1 as [s1 | s1]; try tauto.
          subst.
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; subst.
            simpl in H3.
            destruct s' as [s' | s']; try tauto.
            destruct (dexec_unwrap_driver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4) as [s2' [Heq Hstep']].
            subst.
            eauto with ipr.
          -- inversion Hstep; subst.
             inversion H2; subst.
             eauto with ipr.
      + intros s1 s1' s2 H H0.
        unfold driver_reset in *.
        simpl in H0; unfold driver_reset in H0.
        destruct s1 as [[? | ?] | [? | ?]], s1' as [[? | ?] | [? | ?]], s2;
          inversion H; subst;
          try tauto;
          eexists; split; eauto;
          simpl; eauto.
  Qed.

  Lemma eexec_unwrap_emulator :
    forall (Il Ol I1 O1 I2 O2 I3 O3 : Type)
      (M3 : machine (Il + I3) (Ol + O3))
      (e32 : emulator I3 O3 I2 O2) (e21 : emulator I2 O2 I1 O1)
      ms es1 i o ms' es1',
      eexec (add_emulator M3 e32) O1 (e21.(estep) i) (ms, es1) (Result o (ms', es1')) ->
      exists es2 es2',
        es2 = match ms with
              | EmulatorHigh _ => e32.(einit)
              | EmulatorLow _ e => e
              end /\
          es2' = match ms' with
                 | EmulatorHigh _ => e32.(einit)
                 | EmulatorLow _ e => e
                 end /\
          eexec M3 O1 ((e32 ∘ e21).(estep)%eproc i) (emulator_state_proj ms, (es1, es2)) (Result o (emulator_state_proj ms', (es1', es2'))).
  Proof.
    intros Il Ol I1 O1 I2 O2 I3 O3 M3 e32 e21 ms es1 i o ms' es1' H.
    destruct e21 as [ES21 e21init e21step].
    unfold emulator_compose; simpl.
    simpl in *.
    clear e21init.
    remember (e21step i) as e21i eqn:Heqe21i.
    clear Heqe21i.
    clear e21step.
    dependent induction H.
    - inversion H; subst;
        eexists; eexists; repeat split;
        apply expand_state_preserve; eauto.
    - eexists; eexists; repeat split;
        eauto with emulator.
    - eexists; eexists; repeat split;
        eauto with emulator.
    - eexists; eexists; repeat split;
        eauto with emulator.
    - destruct s'.
      destruct (IHeexec1 _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      destruct (IHeexec2 _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      do 2 eexists; repeat split.
      simpl.
      destruct ms, ms'; simpl; subst;
        eauto with emulator.
    - destruct s', s''.
      destruct (IHeexec1 _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      destruct (IHeexec2 _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      destruct (IHeexec3 _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      do 2 eexists; repeat split.
      simpl.
      destruct ms, ms'; simpl; subst;
        eauto with emulator.
    - destruct (IHeexec _ _ _ _ _ _ i _ _ _ eq_refl JMeq_refl JMeq_refl) as (? & ? & ? & ? & ?).
      do 2 eexists; repeat split.
      simpl.
      destruct ms, ms'; simpl; subst;
        eauto with emulator.
  Qed.

  Lemma eexec_wrap_emulator :
    forall (Il Ol I1 O1 I2 O2 I3 O3 : Type)
      (M3 : machine (Il + I3) (Ol + O3))
      (e32 : emulator I3 O3 I2 O2) (e21 : emulator I2 O2 I1 O1)
      ms es1 es2 i o ms' es1' es2',
      eexec M3 O1 ((e32 ∘ e21).(estep)%eproc i) (ms, (es1, es2)) (Result o (ms', (es1', es2'))) ->
      forall s,
        match s with
        | EmulatorHigh m => m = ms /\ es2 = e32.(einit)
        | EmulatorLow m e => m = ms /\ e = es2
        end ->
        exists s',
          match s' with
          | EmulatorHigh m => m = ms' /\ es2' = e32.(einit)
          | EmulatorLow m e => m = ms' /\ e = es2'
          end /\
            eexec (add_emulator M3 e32) O1 (e21.(estep) i) (s, es1) (Result o (s', es1')).
  Proof.
    intros Il Ol I1 O1 I2 O2 I3 O3 M3 e32 e21 ms es1 es2 i.
    destruct e21 as [ES21 e21init e21step].
    simpl in *.
    remember (e21step i) as e21i eqn:He21i; clear He21i; clear i.
    clear e21step.
    clear e21init.
    generalize dependent es2.
    generalize dependent es1.
    generalize dependent ms.
    induction e21i; intros; simpl in *.
    - destruct s; destruct H0; subst;
        apply expand_state_preserve' in H;
        destruct H; subst;
        eexists (EmulatorLow _ _); split; eauto;
        repeat constructor; auto.
    - rinv_eexec_head.
      eauto with emulator.
    - rinv_eexec_head.
      eauto with emulator.
    - rinv_eexec_head.
      eauto with emulator.
    - rinv_eexec_head.
      destruct s', p.
      destruct (IHe21i _ _ _ _ _ _ _ H7 _ H1) as (? & ? & ?).
      destruct (H _ _ _ _ _ _ _ _ H9 _ H0) as (? & ? & ?).
      eauto with emulator.
    - remember (inline_calls e21i1 (estep e32)) as g eqn:Hg; clear Hg.
      remember (inline_calls e21i2 (estep e32)) as b eqn:Hb; clear Hb.
      remember (es1, es2) as es.
      remember (es1', es2') as es'.
      replace es1 with (fst es) by (subst; auto).
      replace es1' with (fst es') by (subst; auto).
      replace es2 with (snd es) in * by (subst; auto).
      replace es2' with (snd es') in * by (subst; auto).
      clear Heqes.
      clear Heqes'.
      clear es1 es2 es1' es2'.
      destruct o.
      generalize dependent H0.
      generalize dependent s.
      eapply eexec_while_ind
        with (P := fun ms es ms' es' => forall s,
                       match s with
                       | EmulatorHigh m => m = ms /\ snd es = einit e32
                       | EmulatorLow m e => m = ms /\ e = snd es
                       end ->
                       exists s',
                         match s' with
                         | EmulatorHigh m => m = ms' /\ snd es' = einit e32
                         | EmulatorLow m e => m = ms' /\ e = snd es'
                         end /\ eexec (add_emulator M3 e32) unit (While e21i1 e21i2)%eproc (s, fst es) (Result tt (s', fst es')));
        [ | | exact H ].
      + clear ms ms' es es' H.
        intros.
        destruct es, es'.
        destruct (IHe21i1 _ _ _ _ _ _ _ H _ H0) as (? & ? & ?).
        eauto with emulator.
      + clear ms ms' es es' H.
        intros.
        destruct es, es1, es2, es'.
        destruct (IHe21i1 _ _ _ _ _ _ _ H _ H3) as (? & ? & ?).
        destruct (IHe21i2 _ _ _ _ _ _ _ H0 _ H4) as (? & ? & ?).
        destruct (H2 _ H6) as (? & ? & ?).
        eauto with emulator.
  Qed.

  Lemma emulator_compose_wrap_add_emulator :
    forall (Il Ol I1 O1 I2 O2 I3 O3 : Type)
      (M3 : machine (Il + I3) (Ol + O3))
      (e32 : emulator I3 O3 I2 O2) (e21 : emulator I2 O2 I1 O1),
      equivalent
        (add_emulator (add_emulator M3 e32) e21)
        (add_emulator M3 (e32 ∘ e21)%eproc).
  Proof.
    intros Il Ol I1 O1 I2 O2 I3 O3 M3 e32 e21.
    split.
    - apply forward_simulation
        with (R := fun s t =>
                     match s with
                     | EmulatorHigh (EmulatorHigh m) => t = EmulatorHigh m
                     | EmulatorLow (EmulatorHigh m) es1 => t = EmulatorLow m (es1, e32.(einit))
                     | EmulatorLow (EmulatorLow m es2) es1 => t = EmulatorLow m (es1, es2)
                     | _ => False
                     end).
      repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1 es1].
        * (* was in high-level mode *)
          destruct s1 as [s1 | ]; try tauto.
          subst.
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; subst.
            inversion H2; subst.
            eexists; repeat split.
            eauto with ipr.
          -- (* got low-level input *)
            inversion Hstep; subst.
            destruct (eexec_unwrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2) as (es2 & es2' & Hes2 & Hes2' & Hexec).
            destruct ms' as [ms' | ms' es2''];
              subst;
              eexists; split; eauto;
              eauto with ipr.
        * (* was in low-level mode *)
          destruct s1 as [s1 | s1 es2].
          -- subst.
             destruct i.
             ++ (* got high-level input *)
               inversion Hstep; clear Hstep; subst.
               simpl in H3.
               destruct ms' as [s' | s' e']; try tauto.
               inversion H5; clear H5; subst.
               eexists; repeat split.
               eauto with ipr.
             ++ (* got low-level input *)
               inversion Hstep; clear Hstep; subst.
               destruct (eexec_unwrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0) as (es2 & es2' & Hes2 & Hes2' & Hexec).
               destruct ms' as [ms' | ms' es2''];
                 subst;
                 eexists; split; eauto;
                 eauto with ipr.
          -- subst.
             destruct i.
             ++ (* got high-level input *)
               inversion Hstep; clear Hstep; subst.
               simpl in H3.
               destruct ms' as [s' | s' e']; try tauto.
               inversion H5; clear H5; subst.
               eexists; repeat split.
               eauto with ipr.
             ++ (* got low-level input *)
               inversion Hstep; clear Hstep; subst.
               destruct (eexec_unwrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0) as (es2_ & es2' & Hes2 & Hes2' & Hexec).
               destruct ms' as [ms' | ms' es2''];
                 subst;
                 eexists; split; eauto;
                 eauto with ipr.
      + intros s1 s1' s2 H H0.
        unfold emulator_reset in *.
        simpl in H0; unfold emulator_reset in H0.
        destruct s1 as [[? | ? ?] | [? | ? ?]], s1' as [[? | ? ?] | [? | ? ?]], s2;
          inversion H; subst;
          try tauto;
          eexists; split; eauto;
          simpl; eauto.
    - apply forward_simulation
        with (R := fun s t =>
                     match t with
                     | EmulatorHigh (EmulatorHigh m) => s = EmulatorHigh m
                     | EmulatorLow (EmulatorHigh m) es1 => s = EmulatorLow m (es1, e32.(einit))
                     | EmulatorLow (EmulatorLow m es2) es1 => s = EmulatorLow m (es1, es2)
                     | _ => False
                     end).
      repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1 es12].
        * (* was in high-level mode *)
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; clear Hstep; subst.
            destruct s2 as [[s2 | ] | [s2 | s2 es2] es1]; try tauto;
              inversion HR; clear HR; subst.
            eexists (EmulatorHigh (EmulatorHigh _)); split; auto.
            constructor.
            simpl.
            constructor.
            auto.
          -- (* got low-level input *)
            inversion Hstep; clear Hstep; subst.
            destruct s2 as [[s2 | ] | [s2 | s2 es2] es1]; try tauto; try discriminate.
            destruct es as (es1, es2).
            inversion HR; clear HR; subst.
            destruct (eexec_wrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 (EmulatorHigh s2) ltac:(intuition)) as (s2' & Heq & Hexec').
            exists (EmulatorLow s2' es1).
            destruct s2'; destruct Heq; subst;
              eauto with ipr.
        * (* was in low-level mode *)
          destruct i.
          -- (* got high-level input *)
            inversion Hstep; clear Hstep; subst.
            destruct s2 as [[s2 | ] | [s2 | s2 es2] es1]; try tauto;
              inversion HR; clear HR; subst;
              eexists (EmulatorHigh (EmulatorHigh _)); split; eauto;
              solve [ econstructor; [ | simpl; constructor; eauto ]; auto ].
          -- (* got low-level input *)
            inversion Hstep; clear Hstep; subst.
            destruct s2 as [[s2 | ] | [s2 | s2 es2] es1]; try tauto; try discriminate.
            ++ inversion HR; clear HR; subst.
               destruct es' as (es'1, es'2).
               destruct (eexec_wrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 (EmulatorHigh s2) ltac:(intuition)) as (s2' & Heq & Hexec').
               exists (EmulatorLow s2' es'1).
               destruct s2'; destruct Heq; subst;
                 eauto with ipr.
            ++ inversion HR; clear HR; subst.
               destruct es' as (es'1, es'2).
               destruct (eexec_wrap_emulator _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 (EmulatorLow s2 es2) ltac:(intuition)) as (s2' & Heq & Hexec').
               exists (EmulatorLow s2' es'1).
               destruct s2'; destruct Heq; subst;
                 eauto with ipr.
      + intros s1 s1' s2 H H0.
        unfold emulator_reset in *.
        simpl in *.
        unfold emulator_reset in *.
        destruct s1, s1', s2 as [[? | ? ?] | [? | ? ?]];
          inversion H; clear H; subst; try tauto;
          solve [
              first [ eexists (EmulatorHigh (EmulatorHigh _)) |
                      eexists (EmulatorLow (EmulatorHigh _) _) |
                      eexists (EmulatorLow (EmulatorLow _ _) _) ];
              split;
              eauto
            ].
  Qed.

End COMPOSE.
