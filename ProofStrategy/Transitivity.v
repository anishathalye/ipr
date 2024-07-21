Require Import IPR.Definition.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.
Require Import IPR.ProofStrategy.Commute.
Require Import IPR.ProofStrategy.Compose.
Require Import IPR.ProofStrategy.Wrap.

Section TRANSITIVITY.

  Theorem IPR_by_transitivity :
    forall (I1 O1 I2 O2 I3 O3 : Type)
      (M1 : machine I1 O1) (M2 : machine I2 O2) (M3 : machine I3 O3)
      (d12 : driver I1 O1 I2 O2) (d23 : driver I2 O2 I3 O3),
      IPR M1 M2 d12 ->
      IPR M2 M3 d23 ->
      IPR M1 M3 (d12 ∘ d23)%dproc.
  Proof.
    intros I1 O1 I2 O2 I3 O3 M1 M2 M3 d12 d23 [e21 H12] [e32 H23].
    exists (e32 ∘ e21)%eproc.
    eapply equivalent_trans; [ apply driver_compose_wrap_add_driver | ].
    eapply equivalent_trans; [ apply wrap_driver; eauto | ].
    eapply equivalent_trans; [ apply wrap_comm | ].
    eapply equivalent_trans; [ apply wrap_emulator; eauto | ].
    apply emulator_compose_wrap_add_emulator.
  Qed.

End TRANSITIVITY.
