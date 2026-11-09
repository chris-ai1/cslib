/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Complexity of the identity function

A machine with a single state and no work tapes scans the input from left to right, copying each
symbol to the output tape, and halts on the blank at the right end of the input. On input `w` it
outputs `w` after `w.length + 1` steps, and having no work tapes it uses zero space.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_id`: the identity is computable in one step per
  input symbol and zero space.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

-- A local abbreviation for the input position in the scanning invariants.
local notation "scanCfg" => fun input q n out =>
  wordsCfg input q (k := 0) Fin.elim0 out (Fin.mk (min (n + 1) (List.length input + 1)) (by omega))

/-- The copy machine: a single state and no work tapes. It copies every input symbol to the output
tape while moving right, and halts on reading the blank at the right end of the input. -/
def copy : MultiTapeTM 0 Symbol Unit :=
  ofTr () fun _ s _ =>
    match s with
    | some b => { inputTape := 1, workTapes := Fin.elim0, output := some b, state := some () }
    | none => { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

namespace Copy

/-- Copy any unread suffix, appending it to an existing output word. -/
lemma runFrom_suffix (w : List Symbol) {input : List Symbol} {n : ℕ}
    (h : input.drop n = w) (out : List Symbol) :
    copy.runFrom (scanCfg input (some ()) n out) (w.length + 1) =
      scanCfg input none (n + w.length) (out ++ w) := by
  induction w generalizing n out with
  | nil =>
    rw [show ([] : List Symbol).length + 1 = 1 from rfl, runFrom_one, step_of_state rfl,
      inputSymbol_wordsCfg_nil h Fin.elim0, copy, tr_ofTr, Action.apply_wordsCfg_stay]
    simp
  | cons b w ih =>
    have ht : input.drop (n + 1) = w := by rw [← List.drop_drop, h]; rfl
    rw [show (b :: w).length + 1 = 1 + (w.length + 1) by simp; omega,
      runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0,
      copy, tr_ofTr, Action.apply_wordsCfg_right]
    change copy.runFrom _ _ = _
    simpa only [List.length_cons, Option.toList_some, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih ht (out ++ [b])

/-- The copy machine outputs its input unchanged, in one step per symbol and zero space. -/
theorem computesInTimeAndSpace (input : List Symbol) :
    ComputesInTimeAndSpace copy input input (input.length + 1) 0 := by
  have h := runFrom_suffix input (input := input) (n := 0) (by simp) []
  have hr : copy.runFrom (copy.initCfg input) (input.length + 1) =
      scanCfg input none input.length input := by
    simpa [wordsCfg_noTapes, MultiTapeNTM.initCfg, copy, ofTr] using h
  exact ⟨⟨_, congrArg Cfg.state hr, congrArg Cfg.output hr⟩,
    runsInTime_of_halted (congrArg Cfg.state hr), by simp⟩

end Copy

variable {α : Type*}

/-- The identity function is computable in one step per input symbol and zero space. -/
public theorem computableInTimeAndSpace_id {enc : α ↪ List Bool} :
    ComputableInTimeAndSpace (id : α → α) enc enc
      (fun a => (enc a).length + 1) (fun _ => 0) :=
  ⟨0, Unit, inferInstance, copy, fun a ↦ Copy.computesInTimeAndSpace (enc a)⟩

end Turing.MultiTapeTM
