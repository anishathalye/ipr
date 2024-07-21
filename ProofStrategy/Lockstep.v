Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Utils.

Section LOCKSTEP.

  Variable I1 O1 I2 O2 : Type.

  Variable encode_input : I2 -> I1.
  Variable decode_output : O1 -> O2.

  Definition lockstep_driver : driver I1 O1 I2 O2 :=
    fun i2 => (o1 <- Call (encode_input i2); Ret (decode_output o1))%dproc.

  Variable decode_input : I1 -> option I2.
  Variable encode_output : option O2 -> O1. (* has to produce a "default output" *)

  Definition lockstep_emulator : emulator I2 O2 I1 O1 :=
    {|
      estate := unit;
      einit := tt;
      estep := (fun i1 => match decode_input i1 with
                       | Some i2 => o2 <- Call i2; ERet (encode_output (Some o2))
                       | None => ERet (encode_output None)
                       end)%eproc
    |}.

  Variable M1 : machine I1 O1.
  Variable M2 : machine I2 O2.
  Variable R : M1.(state) -> M2.(state) -> Prop.

  Definition lifted_lockstep_R (s1 : driver_state M1.(state)) (s2 : emulator_state M2.(state) unit) : Prop :=
    R (driver_state_proj s1) (emulator_state_proj s2) /\
      driver_mode s1 = emulator_mode s2.

  Theorem IPR_by_lockstep :
    no_reset M1 ->
    no_reset M2 ->
    total M1 ->
    deterministic M2 ->
    (forall i2, decode_input (encode_input i2) = Some i2) ->
    (forall o2, decode_output (encode_output (Some o2)) = o2) ->
    R M1.(init) M2.(init) ->
    (forall s1 s2 i1 oi2 o1 s1',
        R s1 s2 ->
        decode_input i1 = oi2 ->
        M1.(step) s1 i1 (Result o1 s1') ->
        match oi2 with
        | Some i2 => exists o2 s2',
            M2.(step) s2 i2 (Result o2 s2') /\
              R s1' s2' /\
              o1 = encode_output (Some o2)
        | None => o1 = encode_output None /\
                   s1' = s1
        end) ->
    IPR M1 M2 lockstep_driver.
  Proof.
    intros Hnr1 Hnr2 Htot1 Hdet2 Hinput Houtput Hinit Hlockstep.
    exists lockstep_emulator.
    split.
    - apply forward_simulation with (R := lifted_lockstep_R).
      split.
      { split; auto. }
      (* reset *)
      split.
      2:{ intros s1 s1' s2 (HR & Hmode) Hreset.
          exists (EmulatorHigh (emulator_state_proj s2)).
          destruct s1 as [s1 | s1], s1' as [s1' | s1'], s2;
            simpl in Hmode; try discriminate;
            simpl in Hreset; try tauto; rewrite Hnr1 in Hreset;
            unfold lifted_lockstep_R;
            simpl in *;
            subst;
            repeat split;
            auto;
            rewrite Hnr2; reflexivity.
      }
      intros s1 i o s1' s2 [HR Hmode] Hstep.
      simpl in *.
      (* could be in low-level or high-level mode, could get low-level or high-level input *)
      destruct s1 as [s1 | s1], i as [i2 | i1];
        destruct s2 as [s2 | s2 []]; simpl in Hmode; try discriminate;
        inversion Hstep; clear Hstep; subst.
      + (* high-level state, high-level input *)
        unfold lockstep_driver in *.
        rinv_dexec_head.
        specialize (Hlockstep s1 s2 (encode_input i2) (Some i2) v s' HR).
        inversion H3; clear H3; subst.
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct Hlockstep as (o2 & s2' & Hstep & HR' & Hout).
        exists (EmulatorHigh s2').
        split; [ | unfold lifted_lockstep_R; intuition ].
        constructor.
        simpl.
        constructor.
        assert (decode_output v = o2) by (subst; auto).
        rewrite H.
        assumption.
      + (* high-level state, low-level input *)
        (* could correspond to a low-level input or a high-level input, we don't know *)
        specialize (Hlockstep s1 s2 i1 (decode_input i1) ol s' HR).
        inversion H2; clear H2; subst.
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct (decode_input i1) as [i2 | ] eqn:Hdecode1.
        * (* does correspond to a high-level input *)
          destruct Hlockstep as (o2 & s2' & Hstep & HR' & Hout).
          exists (EmulatorLow s2' tt).
          split; [ | unfold lifted_lockstep_R; intuition ].
          constructor.
          simpl.
          rewrite Hdecode1.
          econstructor.
          -- constructor.
             simpl.
             constructor.
             exact Hstep.
          -- rewrite Hout.
             constructor.
        * (* does not correspond to a high-level input *)
          destruct Hlockstep as (Hout & Heq).
          subst.
          exists (EmulatorLow s2 tt).
          split; [ | unfold lifted_lockstep_R; intuition ].
          constructor.
          simpl.
          rewrite Hdecode1.
          constructor.
      + (* low-level state, high-level input *)
        simpl in H3; rewrite Hnr1 in H3; subst.
        unfold lockstep_driver in *.
        rinv_dexec_head.
        specialize (Hlockstep s' s2 (encode_input i2) (Some i2) v s'' HR).
        inversion H3; clear H3; subst.
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct Hlockstep as (o2 & s2' & Hstep & HR' & Hout).
        exists (EmulatorHigh s2').
        split; [ | unfold lifted_lockstep_R; intuition ].
        econstructor; [ simpl; rewrite Hnr2; auto | ].
        simpl.
        constructor.
        assert (decode_output v = o2) by (subst; auto).
        rewrite H.
        assumption.
      + (* low-level state, low-level input *)
        specialize (Hlockstep s1 s2 i1 (decode_input i1) ol s' HR).
        inversion H2; clear H2; subst.
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct (decode_input i1) as [i2 | ] eqn:Hdecode1.
        * (* does correspond to a high-level input *)
          destruct Hlockstep as (o2 & s2' & Hstep & HR' & Hout).
          exists (EmulatorLow s2' tt).
          split; [ | unfold lifted_lockstep_R; intuition ].
          constructor.
          simpl.
          rewrite Hdecode1.
          econstructor.
          -- constructor.
             simpl.
             constructor.
             exact Hstep.
          -- rewrite Hout.
             constructor.
        * (* does not correspond to a high-level input *)
          destruct Hlockstep as (Hout & Heq).
          subst.
          exists (EmulatorLow s2 tt).
          split; [ | unfold lifted_lockstep_R; intuition ].
          constructor.
          simpl.
          rewrite Hdecode1.
          constructor.
    - apply forward_simulation with (R := fun s2 s1 => lifted_lockstep_R s1 s2).
      split.
      { split; auto. }
      (* reset *)
      split.
      2:{ intros s1 s1' s2 (HR & Hmode) Hreset.
          exists (DriverHigh (driver_state_proj s2)).
          destruct s1 as [s1 | s1], s1' as [s1' | s1'], s2;
            simpl in Hmode; try discriminate;
            simpl in Hreset; try tauto; rewrite Hnr2 in Hreset;
            unfold lifted_lockstep_R;
            simpl in *;
            subst;
            repeat split;
            auto;
            rewrite Hnr1; reflexivity.
      }
      intros s2 i o s2' s1 [HR Hmode] Hstep.
      simpl in *.
      (* could be in low-level or high-level mode, could get low-level or high-level input *)
      destruct s2 as [s2 | s2 []], i as [i2 | i1];
        destruct s1 as [s1 | s1]; simpl in Hmode; try discriminate;
        inversion Hstep; clear Hstep; subst.
      + (* high-level state, high-level input *)
        destruct (Htot1 s1 (encode_input i2)) as [[o1' s1'] Hsi1].
        exists (DriverHigh s1').
        specialize (Hlockstep s1 s2 (encode_input i2) (Some i2) o1' s1' HR).
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct Hlockstep as (o2' & s2' & Hstep2 & HR' & Hout).
        inversion H2; clear H2; subst.
        specialize (Hdet2 _ _ _ _ H3 Hstep2).
        inversion Hdet2; subst.
        repeat constructor; auto.
        unfold lockstep_driver.
        econstructor.
        * constructor.
          simpl.
          constructor.
          apply Hsi1.
        * rewrite Houtput.
          constructor.
      + (* high-level state, low-level input *)
        (* could correspond to a low-level input or a high-level input, we don't know *)
        destruct (Htot1 s1 i1) as [[o1' s1'] Hsi1].
        exists (DriverLow s1').
        specialize (Hlockstep s1 s2 i1 (decode_input i1) o1' s1' HR ltac:(auto) Hsi1).
        simpl in H2.
        destruct (decode_input i1) as [i2 | ] eqn:Hdecode1.
        * (* does correspond to a high-level input *)
          destruct Hlockstep as (o2' & s2' & Hstep2 & HR' & Hout).
          rinv_eexec_head.
          inversion H2; clear H2; subst.
          specialize (Hdet2 _ _ _ _ H4 Hstep2).
          inversion Hdet2; subst.
          repeat constructor; auto.
          simpl.
          constructor.
          exact Hsi1.
        * (* does not correspond to a high-level input *)
          destruct Hlockstep as (Hout & Heq).
          simpl in *.
          subst.
          rinv_eexec_head.
          split.
          -- constructor.
             simpl.
             constructor.
             auto.
          -- unfold lifted_lockstep_R.
             split; auto.
      + (* low-level state, high-level input *)
        simpl in H3; rewrite Hnr2 in H3; subst.
        destruct (Htot1 s1 (encode_input i2)) as [[o1' s1'] Hsi1].
        exists (DriverHigh s1').
        specialize (Hlockstep s1 ms' (encode_input i2) (Some i2) o1' s1' HR).
        specialize (Hlockstep ltac:(auto) ltac:(auto)).
        destruct Hlockstep as (o2' & s2' & Hstep2 & HR' & Hout).
        inversion H5; clear H5; subst.
        specialize (Hdet2 _ _ _ _ H2 Hstep2).
        inversion Hdet2; subst.
        repeat constructor; auto.
        unfold lockstep_driver.
        econstructor; [ simpl; rewrite Hnr1; auto | ].
        econstructor.
        * constructor.
          simpl.
          constructor.
          apply Hsi1.
        * rewrite Houtput.
          constructor.
      + (* low-level state, low-level input *)
        destruct (Htot1 s1 i1) as [[o1' s1'] Hsi1].
        exists (DriverLow s1').
        specialize (Hlockstep s1 s2 i1 (decode_input i1) o1' s1' HR ltac:(auto) Hsi1).
        simpl in H0.
        destruct (decode_input i1) as [i2 | ] eqn:Hdecode1.
        * (* does correspond to a high-level input *)
          destruct Hlockstep as (o2' & s2' & Hstep2 & HR' & Hout).
          rinv_eexec_head.
          inversion H2; clear H2; subst.
          specialize (Hdet2 _ _ _ _ H4 Hstep2).
          inversion Hdet2; subst.
          repeat constructor; auto.
          simpl.
          constructor.
          exact Hsi1.
        * (* does not correspond to a high-level input *)
          destruct Hlockstep as (Hout & Heq).
          simpl in *.
          subst.
          rinv_eexec_head.
          split.
          -- constructor.
             simpl.
             constructor.
             auto.
          -- unfold lifted_lockstep_R.
             split; auto.
  Qed.

End LOCKSTEP.
