Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Tactics.

Require Import List.
Require Import Program.Equality.

Section SIMULATION.

  Variable I1 O1 I2 O2 : Type.
  Variable M1 : machine I1 O1.
  Variable d : driver I1 O1 I2 O2.
  Variable M2 : machine I2 O2.

  (* R holds in between spec-level operations *)
  Variable R : M1.(state) -> M2.(state) -> Prop.

  (* this one talks about a single operation, matching Knox *)
  Definition functional_simulation : Prop :=
    (* R holds on initial state *)
    R M1.(init) M2.(init) /\
      (* R is preserved by reset *)
      (forall s1 s2 s1',
          R s1 s2 ->
          M1.(reset) s1 s1' ->
          R s1' s2) /\
      (* at least one driver execution terminates *)
      (forall s1 s2 i2,
          R s1 s2 ->
          exists o2 s1',
            dexec (mux M1) _ (d i2) s1 (Result o2 s1')) /\
      (* driver output matches spec, and R holds *)
      (forall s1 s2 i2 o2 s1',
          R s1 s2 ->
          dexec (mux M1) _ (d i2) s1 (Result o2 s1') ->
          exists s2', M2.(step) s2 i2 (Result o2 s2') /\ R s1' s2').

  Definition io_to_machine_trace (io : list (I1 * O1)) : trace I1 O1 :=
    map (fun '(i, o) => IO i o) io.

  Definition io_to_ideal_machine_trace (io : list (I1 * O1)) :
    trace (I2 + I1) (O2 + O1) :=
    map (fun '(i, o) => IO (inr i) (inr o)) io.

  Definition physical_simulation : Prop :=
    exists (e : emulator I2 O2 I1 O1),
    forall s1 s2 io s1' s1'',
      R s1 s2 ->
      execution M1 s1 (io_to_machine_trace io) s1' ->
      M1.(reset) s1' s1'' ->
      exists s2' e2',
        execution (ideal_world M2 e) (EmulatorHigh s2)
          (io_to_ideal_machine_trace io) (EmulatorLow s2' e2') /\
          R s1'' s2'.

  Definition lifted_R (e : emulator I2 O2 I1 O1) (ds1 : driver_state M1.(state)) (es2 : emulator_state M2.(state) e.(estate)) :=
    match (ds1, es2) with
    | (DriverHigh s1, EmulatorHigh s2) => R s1 s2
    | (DriverLow s1, EmulatorLow s2 e2) =>
        forall io s1' s1'',
          execution M1 s1 (io_to_machine_trace io) s1' ->
          reset M1 s1' s1'' ->
          exists s2' e2',
            execution (ideal_world M2 e) (EmulatorLow s2 e2) (io_to_ideal_machine_trace io) (EmulatorLow s2' e2') /\
              R s1'' s2'
    | _ => False
    end.

  Lemma eexec_deterministic :
    forall (ES T : Type) (estep : eproc ES I2 O2 T)
      s2 res res',
      deterministic M2 ->
      eexec (mux M2) T estep s2 res ->
      eexec (mux M2) T estep s2 res' ->
      res = res'.
  Proof.
    intros ES T estep s2 res res' Hdet Hexec1 Hexec2.
    dependent induction Hexec1.
    - inv_exec Hexec2.
      inversion H; subst.
      inversion H3; subst.
      specialize (Hdet _ _ _ _ H5 H6).
      inversion Hdet.
      subst; auto.
    - inv_exec Hexec2; auto.
    - inv_exec Hexec2; auto.
    - inv_exec Hexec2; auto.
    - inv_exec Hexec2; auto.
      specialize (IHHexec1_1 _ H4).
      inversion IHHexec1_1; subst.
      specialize (IHHexec1_2 _ H6).
      auto.
    - inv_exec Hexec2; auto.
      + specialize (IHHexec1_1 _ H2).
        inversion IHHexec1_1; subst.
        specialize (IHHexec1_2 _ H3).
        inversion IHHexec1_2; subst.
        specialize (IHHexec1_3 _ H5).
        auto.
      + exfalso.
        specialize (IHHexec1_1 _ H3).
        inversion IHHexec1_1.
    - inv_exec Hexec2.
      + exfalso.
        specialize (IHHexec1 _ H2).
        inversion IHHexec1.
      + specialize (IHHexec1 _ H3).
        inversion IHHexec1; auto.
  Qed.

  Definition resettable {I O : Type} (M : machine I O) :=
    forall s, exists s', M.(reset) s s'.

  Theorem IPR_by_functional_physical_simulation :
    total M1 ->
    deterministic M2 ->
    resettable M1 ->
    no_reset M2 ->
    functional_simulation ->
    physical_simulation ->
    IPR M1 M2 d.
  Proof.
    intros Htot1 Hdet2 Hrst1 Hnrst2 (Hinit & Hreset & Hterm & Hcorrectness) (e & Hsecurity).
    exists e.
    split.
    - apply forward_simulation with (R := lifted_R e).
      unfold lifted_R.
      repeat split; simpl; auto.
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1], s2 as [s2 | s2 e2]; simpl in HR; try tauto.
        * destruct i as [i2 | i1];
            inversion Hstep; subst.
          -- specialize (Hcorrectness _ _ _ _ _ HR H2).
             destruct Hcorrectness as (s2' & Hstep' & HR').
             exists (EmulatorHigh s2').
             split; auto.
             constructor.
             simpl.
             auto with ipr.
          -- destruct (Hrst1 s') as (? & Hx).
             assert (execution M1 s1 (IO i1 ol :: nil) s') as Hstep'.
             { inversion H2; subst. eauto with machine. }
             pose proof (Hsecurity s1 s2 ((i1, ol) :: nil) s' _ HR Hstep' Hx) as H.
             destruct H as (s2' & e2' & Hexec' & HR').
             exists (EmulatorLow s2' e2').
             split.
             ++ inversion Hexec'; subst.
                inversion H6; subst.
                inversion H5; subst.
                eauto with ipr.
             ++ intros io s1' s1'' H H0.
                assert (execution M1 s1 (io_to_machine_trace ((i1, ol) :: io)) s1').
                { inversion H2; subst. econstructor; eauto. }
                specialize (Hsecurity s1 s2 ((i1, ol) :: io) s1' _ HR H1 H0).
                destruct Hsecurity as (s2'' & e2'' & Hexec'' & HR'').
                inversion Hexec''; clear Hexec''; subst.
                inversion Hexec'; clear Hexec'; subst.
                inversion H11; clear H11; subst.
                inversion H8; clear H8; subst.
                inversion H10; clear H10; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H6 H7).
                inversion H3; subst.
                eexists _, _; eauto with ipr.
        * destruct i as [i2 | i1];
            inversion Hstep; clear Hstep; subst.
          -- simpl in H3.
             destruct (HR nil s1 s' ltac:(constructor) H3) as (s2' & e2' & Hexecnil & HR').
             inversion Hexecnil; clear Hexecnil; subst.
             specialize (Hcorrectness _ _ _ _ _ HR' H4).
             destruct Hcorrectness as (s2'' & Hstep'' & HR'').
             exists (EmulatorHigh s2'').
             split; auto.
             econstructor; simpl; eauto with ipr.
             rewrite Hnrst2; auto.
          -- destruct (Hrst1 s') as (? & Hx).
             assert (execution M1 s1 (IO i1 ol :: nil) s') as Hstep'.
             { inversion H2; subst. eauto with machine. }
             pose proof (HR ((i1, ol) :: nil) _ _ Hstep' Hx) as H.
             destruct H as (s2' & e2' & Hexec' & HR').
             exists (EmulatorLow s2' e2').
             inversion Hexec'; clear Hexec'; subst.
             inversion H6; clear H6; subst.
             inversion H5; clear H5; subst.
             split.
             ++ eauto with ipr.
             ++ intros io s1' s1'' H H1.
                assert (execution M1 s1 (io_to_machine_trace ((i1, ol) :: io)) s1').
                { inversion H2; subst. econstructor; eauto. }
                destruct (HR _ _ _ H3 H1) as (s2'' & e2'' & Hexec'' & HR'').
                exists s2'', e2''.
                split; auto.
                inversion Hexec''; clear Hexec''; subst.
                inversion H9; clear H9; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H0 H5).
                inversion H4; clear H4; subst.
                eauto with ipr.
      + intros s1 s1' s2 HR Hr.
        destruct s1 as [s1 | s1], s1' as [s1' | s1'], s2 as [s2 | s2 e2]; simpl in *; try tauto.
        * exists (EmulatorHigh s2).
          split.
          -- rewrite Hnrst2; auto.
          -- eapply Hreset; eauto.
        * exists (EmulatorHigh s2).
          simpl; split; auto.
          -- rewrite Hnrst2; auto.
          -- specialize (HR nil s1 s1' ltac:(constructor) Hr).
             destruct HR as (s2' & e2' & Hexec' & HR').
             simpl in Hexec'.
             inversion Hexec'; subst.
             auto.
    - apply forward_simulation with (R := fun s2 s1 => lifted_R e s1 s2).
      unfold lifted_R.
      repeat split; simpl; auto.
      + intros s2 i o s2' s1 HR Hstep.
        destruct s2 as [s2 | s2 e2], s1 as [s1 | s1]; simpl in HR; try tauto.
        * destruct i as [i2 | i1];
            inversion Hstep; subst.
          -- destruct (Hterm s1 s2 i2 HR) as (o & s1' & Hdexec).
             exists (DriverHigh s1').
             destruct (Hcorrectness _ _ _ _ _ HR Hdexec) as (s2' & Hstep' & HR').
             inversion H2; subst.
             specialize (Hdet2 _ _ _ _ Hstep' H3).
             inversion Hdet2; subst.
             auto with ipr.
          -- destruct (Htot1 s1 i1) as ((o1' & s1') & Hs1').
             exists (DriverLow s1').
             split.
             ++ constructor.
                simpl; constructor.
                destruct (Hrst1 s1') as (? & Hx).
                assert (execution M1 s1 (IO i1 o1' :: nil) s1') as Hstep' by (eauto with machine).
                specialize (Hsecurity s1 s2 ((i1, o1') :: nil) s1' _ HR Hstep' Hx).
                destruct Hsecurity as (s2' & e2' & Hexec' & HR').
                inversion Hexec'; clear Hexec'; subst.
                inversion H6; clear H6; subst.
                inversion H5; clear H5; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H2 H3).
                inversion H; subst.
                auto.
             ++ intros io s1'0 s1'' H H0.
                assert (execution M1 s1 (io_to_machine_trace ((i1, o1') :: io)) s1'0) by (eauto with machine).
                specialize (Hsecurity s1 s2 ((i1, o1') :: io) _ _ HR H1 H0).
                destruct Hsecurity as (s2' & e2' & Hexec' & HR').
                inversion Hexec'; clear Hexec'; subst.
                inversion H8; clear H8; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H2 H6).
                inversion H3; subst.
                eexists _, _; eauto with ipr.
        * destruct i as [i2 | i1];
            inversion Hstep; subst.
          -- simpl in H3.
             rewrite Hnrst2 in H3; subst.
             destruct (Hrst1 s1) as (s1' & Hr1).
             specialize (HR nil s1 s1' ltac:(constructor) Hr1).
             destruct HR as (s2' & e2' & Hexecnil & HR).
             inversion Hexecnil; subst.
             destruct (Hterm _ _ i2 HR) as (o & s1'' & Hdexec).
             exists (DriverHigh s1'').
             destruct (Hcorrectness _ _ _ _ _ HR Hdexec) as (s2'' & Hstep' & HR').
             inversion H5; subst.
             specialize (Hdet2 _ _ _ _ Hstep' H2).
             inversion Hdet2; subst.
             eauto with ipr.
          -- destruct (Htot1 s1 i1) as ((o1' & s1') & Hs1').
             exists (DriverLow s1').
             split.
             ++ constructor.
                simpl; constructor.
                destruct (Hrst1 s1') as (? & Hx).
                destruct (HR ((i1, o1') :: nil) s1' _ ltac:(eauto with machine) Hx) as (s2' & e2' & Hexec' & HR').
                inversion Hexec'; clear Hexec'; subst.
                inversion H6; clear H6; subst.
                inversion H5; clear H5; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H0 H1).
                inversion H; subst.
                auto.
             ++ intros io s1'0 s1'' H H1.
                assert (execution M1 s1 (io_to_machine_trace ((i1, o1') :: io)) s1'0) by (eauto with machine).
                destruct (HR _ _ _ H2 H1) as (s2' & e2' & Hexec' & HR').
                inversion Hexec'; clear Hexec'; subst.
                inversion H8; clear H8; subst.
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 H0 H4).
                inversion H3; subst.
                eauto with ipr.
      + intros s2 s2' s1 HR Hr.
        destruct s2 as [s2 | s2 e2], s2' as [s2' | s2' e2'], s1 as [s1 | s1]; simpl in *; try tauto.
        * destruct (Hrst1 s1) as (s1' & Hrst1').
          exists (DriverHigh s1').
          split; auto.
          rewrite Hnrst2 in Hr; subst.
          eapply Hreset; eauto.
        * destruct (Hrst1 s1) as (s1' & Hrst1').
          exists (DriverHigh s1').
          split; auto.
          rewrite Hnrst2 in Hr; subst.
          specialize (HR nil s1 s1' ltac:(constructor) Hrst1').
          destruct HR as (s2'' & e2'' & Hexecnil & HR').
          inversion Hexecnil; clear Hexecnil; subst.
          auto.
  Qed.

End SIMULATION.
