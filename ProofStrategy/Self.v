Require Import IPR.Common.
Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.Tactics.
Require Import IPR.Utils.

Section SELF.

  Definition identity_driver (I O : Type) : driver I O I O := fun i => (Call i)%dproc.

  Definition identity_emulator (I O : Type) : emulator I O I O :=
    {|
      estate := unit;
      einit := tt;
      estep := fun i => (Call i)%eproc
    |}.

  Lemma IPR_self' :
    forall I O (M : machine I O),
      equivalent (add_driver (mux M) (identity_driver _ _))
                 (add_emulator (mux M) (identity_emulator _ _)).
  Proof.
    intros I O M.
    split.
    - apply forward_simulation
        with (R := fun s t => driver_state_proj s = emulator_state_proj t /\
                             driver_mode s = emulator_mode t).
      repeat split.
      + intros s1 i o s1' s2 (? & ?) Hstep.
        destruct s1; destruct s2 as [? | ? []]; simpl in *; subst; try discriminate;
          destruct i; destruct o; inversion Hstep; subst;
          try match goal with
            | [ H : dexec _ _ _ _ _ |- _ ] => inv_exec H
            end.
        * exists (EmulatorHigh s').
          eauto with ipr.
        * exists (EmulatorLow s' tt).
          eauto with ipr emulator.
        * exists (EmulatorHigh s'').
          eauto with ipr emulator.
        * exists (EmulatorLow s' tt).
          eauto with ipr emulator.
      + intros s1 s1' s2 (? & ?) Hreset.
        destruct s1' as [s1' | ?]; [ | destruct s1; simpl in *; tauto ].
        simpl in *.
        exists (EmulatorHigh s1').
        repeat split.
        destruct s1; destruct s2; simpl in *; subst; auto.
    - apply forward_simulation
        with (R := fun s t => emulator_state_proj s = driver_state_proj t /\
                             emulator_mode s = driver_mode t).
      repeat split.
      + intros s1 i o s1' s2 (? & ?) Hstep.
        destruct s1; destruct s2; simpl in *; subst; try discriminate;
          destruct i; destruct o; inversion Hstep; subst;
          try match goal with
            | [ H : eexec _ _ _ _ _ |- _ ] => inv_exec H
            end.
        * exists (DriverHigh ms').
          eauto with ipr driver.
        * exists (DriverLow ms').
          eauto with ipr driver.
        * exists (DriverHigh ms'').
          eauto with ipr driver.
        * exists (DriverLow ms').
          eauto with ipr driver.
      + intros s1 s1' s2 (? & ?) Hreset.
        destruct s1' as [s1' | ?]; [ | destruct s1; simpl in *; tauto ].
        simpl in *.
        exists (DriverHigh s1').
        repeat split.
        destruct s1; destruct s2; simpl in *; subst; auto.
  Qed.

  Theorem IPR_self :
    forall I O (M : machine I O),
      IPR M M (identity_driver I O).
  Proof.
    intros.
    exists (identity_emulator _ _).
    apply IPR_self'.
  Qed.

End SELF.
