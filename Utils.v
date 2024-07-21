Require Import IPR.Definition.

Inductive mode := High | Low.

Definition driver_mode {S : Type} (s : driver_state S) : mode :=
  match s with
  | DriverHigh _ => High
  | DriverLow _ => Low
  end.

Definition emulator_mode {S ES : Type} (s : emulator_state S ES) : mode :=
  match s with
  | EmulatorHigh _ => High
  | EmulatorLow _ _ => Low
  end.

Definition driver_state_proj {S : Type} (s : driver_state S) : S :=
  match s with
  | DriverHigh s => s
  | DriverLow s => s
  end.

Definition driver_state_inj {S S' : Type} (s : driver_state S) (s' : S') : driver_state S' :=
  match s with
  | DriverHigh s => DriverHigh s'
  | DriverLow s => DriverLow s'
  end.

Definition emulator_state_proj {S ES : Type} (s : emulator_state S ES) : S :=
  match s with
  | EmulatorHigh s => s
  | EmulatorLow s _ => s
  end.

Definition emulator_state_inj {S S' ES : Type} (s : emulator_state S ES) (s' : S') : emulator_state S' ES :=
  match s with
  | EmulatorHigh s => EmulatorHigh s'
  | EmulatorLow s e => EmulatorLow s' e
  end.
