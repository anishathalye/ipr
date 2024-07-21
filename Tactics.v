Require Import Classes.EquivDec.

Ltac sigT_eq :=
  lazymatch goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.

Ltac inv_exec H :=
  inversion H; subst; clear H; repeat sigT_eq.
