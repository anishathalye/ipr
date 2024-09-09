Require Import IPR.Common.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Machine.

Require Import List.

(* 1 is implementation / low level / real
   2 is specification / high level / ideal *)

Section MUX.

  Variable I O : Type.
  Variable M : machine I O.

  Inductive mux_step : M.(state) -> (I + I) -> result (O + O) M.(state) -> Prop :=
  | MuxStepL : forall s i s' o,
      M.(step) s i (Result o s') ->
      mux_step s (inl i) (Result (inl o) s')
  | MuxStepR : forall s i s' o,
      M.(step) s i (Result o s') ->
      mux_step s (inr i) (Result (inr o) s')
  .

  Definition mux : machine (I + I) (O + O) :=
    {|
      state := M.(state);
      init := M.(init);
      step := mux_step;
      reset := M.(reset);
    |}.

End MUX.

Arguments mux [I O].

Create HintDb ipr.

#[export] Hint Constructors mux_step : ipr.
#[export] Hint Unfold mux : ipr.

Section DRIVER.

  Variable Ir Or I1 O1 I2 O2 : Type.
  Variable M1 : machine (I1 + Ir) (O1 + Or).
  Variable d : driver I1 O1 I2 O2.

  (* tracks mode/state *)
  Inductive driver_state (S : Type) :=
  | DriverHigh : S -> driver_state S
  | DriverLow : S -> driver_state S
  .

  Arguments DriverHigh [S].
  Arguments DriverLow [S].

  Inductive driver_step : driver_state M1.(state) -> (I2 + Ir) -> result (O2 + Or) (driver_state M1.(state)) -> Prop :=
  (* in low-level mode, got low-level input *)
  | DriverStepLowLow : forall s il s' ol,
      M1.(step) s (inr il) (Result (inr ol) s') ->
      driver_step (DriverLow s) (inr il) (Result (inr ol) (DriverLow s'))
  (* in high-level mode, got low-level input; no special action needed *)
  | DriverStepHighLow : forall s il s' ol,
      M1.(step) s (inr il) (Result (inr ol) s') ->
      driver_step (DriverHigh s) (inr il) (Result (inr ol) (DriverLow s'))
  (* in low-level mode, got high-level input: need to reset first *)
  | DriverStepLowHigh : forall s s' i2 s'' o2,
      M1.(reset) s s' ->
      dexec _ _ (d i2) s' (Result o2 s'') ->
      driver_step (DriverLow s) (inl i2) (Result (inl o2) (DriverHigh s''))
  (* in high-level mode, got high-level input *)
  | DriverStepHighHigh : forall s i2 s' o2,
      dexec _ _ (d i2) s (Result o2 s') ->
      driver_step (DriverHigh s) (inl i2) (Result (inl o2) (DriverHigh s'))
  .

  Definition driver_reset (s1 s2 : driver_state M1.(state)) : Prop :=
    match s1 with
    | DriverHigh s1'
    | DriverLow s1' =>
        match s2 with
        | DriverHigh s2' => M1.(reset) s1' s2'
        | _ => False
        end
    end.

  Definition add_driver : machine (I2 + Ir) (O2 + Or) :=
    {|
      state := driver_state _;
      init := DriverHigh M1.(init);
      step := driver_step;
      reset := driver_reset;
    |}.

End DRIVER.

Arguments DriverHigh [S].
Arguments DriverLow [S].

Arguments add_driver [Ir Or I1 O1 I2 O2].

Definition real_world {I1 O1 I2 O2 : Type} (M1 : machine I1 O1) (d : driver I1 O1 I2 O2) : machine (I2 + I1) (O2 + O1) :=
  add_driver (mux M1) d.

#[export] Hint Constructors driver_state : ipr.
#[export] Hint Constructors driver_step : ipr.
#[export] Hint Unfold add_driver : ipr.
#[export] Hint Unfold real_world : ipr.

Section EMULATOR.

  Variable Il Ol I1 O1 I2 O2 : Type.
  Variable M2 : machine (Il + I2) (Ol + O2).
  Variable e : emulator I2 O2 I1 O1.

  (* tracks mode/state *)
  Inductive emulator_state (S ES : Type) :=
  | EmulatorHigh : S -> emulator_state S ES
  | EmulatorLow : S -> ES -> emulator_state S ES
  .

  Arguments EmulatorHigh [S ES].
  Arguments EmulatorLow [S ES].

  Inductive emulator_step : emulator_state M2.(state) e.(estate) -> (Il + I1) -> result (Ol + O1) (emulator_state M2.(state) e.(estate)) -> Prop :=
  (* in high-level mode, got high-level input *)
  | EmulatorStepHighHigh : forall ms i2 ms' o2,
      M2.(step) ms (inl i2) (Result (inl o2) ms') ->
      emulator_step (EmulatorHigh ms) (inl i2) (Result (inl o2) (EmulatorHigh ms'))
  (* in low-level mode, got high-level input *)
  | EmulatorStepLowHigh : forall ms es ms' i2 ms'' o2,
      (* like in driver_step, we reset when going from low-level mode to high-level mode *)
      M2.(reset) ms ms' ->
      M2.(step) ms' (inl i2) (Result (inl o2) ms'') ->
      emulator_step (EmulatorLow ms es) (inl i2) (Result (inl o2) (EmulatorHigh ms''))
  (* in high-level mode, got low-level input *)
  | EmulatorStepHighLow : forall ms i1 ms' es o1,
      eexec _ _ (e.(estep) i1) (ms, e.(einit)) (Result o1 (ms', es)) ->
      emulator_step (EmulatorHigh ms) (inr i1) (Result (inr o1) (EmulatorLow ms' es))
  (* in low-level mode, got low-level input *)
  | EmulatorStepLowLow : forall ms es i1 ms' es' o1,
      eexec _ _ (e.(estep) i1) (ms, es) (Result o1 (ms', es')) ->
      emulator_step (EmulatorLow ms es) (inr i1) (Result (inr o1) (EmulatorLow ms' es'))
  .

  Definition emulator_reset (s1 s2 : emulator_state M2.(state) e.(estate)) : Prop :=
    match s1 with
    | EmulatorHigh s1'
    | EmulatorLow s1' _ =>
        match s2 with
        | EmulatorHigh s2' => M2.(reset) s1' s2'
        | _ => False
        end
    end.

  Definition add_emulator : machine (Il + I1) (Ol + O1) :=
    {|
      state := emulator_state _ _;
      init := EmulatorHigh M2.(init);
      step := emulator_step;
      reset := emulator_reset;
    |}.

End EMULATOR.

Arguments EmulatorHigh [S ES].
Arguments EmulatorLow [S ES].

Arguments add_emulator [Il Ol I1 O1 I2 O2].

Definition ideal_world {I1 O1 I2 O2 : Type} (M2 : machine I2 O2) (e : emulator I2 O2 I1 O1) : machine (I2 + I1) (O2 + O1) :=
  add_emulator (mux M2) e.

#[export] Hint Constructors emulator_state : ipr.
#[export] Hint Constructors emulator_step : ipr.
#[export] Hint Unfold add_emulator : ipr.
#[export] Hint Unfold ideal_world : ipr.

Definition IPR {I1 O1 I2 O2} (M1 : machine I1 O1) (M2 : machine I2 O2) (d : driver I1 O1 I2 O2) : Prop :=
  exists (e : emulator I2 O2 I1 O1),
    equivalent (real_world M1 d) (ideal_world M2 e).
