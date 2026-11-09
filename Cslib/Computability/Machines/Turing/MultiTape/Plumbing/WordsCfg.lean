/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Tapes holding words and configurations of such tapes

The normal form in which "tape transformer" machines (cf. `TransformsTapes.lean`) start and finish:
every work tape holds a word in the cells `0, 1, …` and is blank everywhere else, with every work
head at the start. The input head defaults to its starting position and can be set explicitly
for scanning proofs.

## Main definitions

* `Turing.tapeOfList`: the tape holding exactly a given word.
* `Turing.wordsCfg`: the configuration whose tapes hold given words.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def tapeOfList (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma tapeOfList_ofNat (xs : List Symbol) (n : ℕ) : tapeOfList xs n = xs[n]? := rfl

@[simp]
lemma tapeOfList_negSucc (xs : List Symbol) (n : ℕ) :
    tapeOfList xs (.negSucc n) = none := rfl

/-- Appending one symbol writes precisely the cell after the existing word. -/
lemma tapeOfList_append_single (xs : List Symbol) (x : Symbol) :
    tapeOfList (xs ++ [x]) = Function.update (tapeOfList xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n => grind [tapeOfList]

/-- A cell of `tapeOfList xs` is blank exactly outside the positions `0, …, xs.length - 1`. -/
lemma tapeOfList_eq_none_iff (xs : List Symbol) (z : ℤ) :
    tapeOfList xs z = none ↔ z < 0 ∨ (xs.length : ℤ) ≤ z := by
  cases z <;> simp

/-- The blank tape holds the empty word. -/
@[simp]
lemma tapeOfList_nil : tapeOfList ([] : List Symbol) = fun _ => none := by
  funext z
  cases z <;> simp

/-- The cell at position `0` holds the first symbol of the word. -/
lemma tapeOfList_zero (xs : List Symbol) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The configuration whose work tape `i` holds exactly the word `ws i` with its head at the
start, in state `q` with output `out`. The input head defaults to the start of the input. -/
@[simps]
def wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol)
    (inputPos : Fin (input.length + 2) := 1) : Cfg k Symbol State input :=
  ⟨q, inputPos, fun i => tapeOfList (ws i), fun _ => 0, out⟩

/-- With no work tapes, a word configuration has no tape contents to specify. -/
@[simp]
lemma wordsCfg_noTapes (input : List Symbol) (q : Option State) (out : List Symbol)
    (pos : Fin (input.length + 2) := 1) :
    wordsCfg input q (k := 0) Fin.elim0 out pos =
      ⟨q, pos, fun _ _ => none, fun _ => 0, out⟩ :=
  Cfg.ext rfl rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl

/-- Remapping the state of a `wordsCfg` remaps its state and leaves the words alone. -/
@[simp]
lemma mapState_wordsCfg {State' : Type*} (φ : Option State → Option State')
    (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol)
    (pos : Fin (input.length + 2) := 1) :
    (wordsCfg input q ws out pos).mapState φ = wordsCfg input (φ q) ws out pos := rfl

/-- Changing the state of a `wordsCfg` leaves the words alone. -/
@[simp]
lemma withState_wordsCfg {State' : Type*} (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) (q' : Option State')
    (pos : Fin (input.length + 2) := 1) :
    (wordsCfg input q ws out pos).withState q' = wordsCfg input q' ws out pos := rfl

/-- Prepending a word to the output of a `wordsCfg` prepends it to the output word. -/
@[simp]
lemma prependOutput_wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out pre : List Symbol) (pos : Fin (input.length + 2) := 1) :
    (wordsCfg input q ws out pos).prependOutput pre = wordsCfg input q ws (pre ++ out) pos := rfl

/-- The initial configuration is the word configuration with blank tapes and no output. -/
lemma Cfg.init_eq_wordsCfg (q₀ : State) (input : List Symbol) :
    Cfg.init (k := k) q₀ input = wordsCfg input (some q₀) (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp [Cfg.init, wordsCfg]

/-- Read the first symbol of the unprocessed input suffix. -/
lemma inputSymbol_wordsCfg_cons {input rest : List Symbol} {n : ℕ} {b : Symbol}
    (h : input.drop n = b :: rest) (ws : Fin k → List Symbol)
    (q : Option State) (out : List Symbol) :
    (wordsCfg input q ws out ⟨min (n + 1) (input.length + 1), by omega⟩).inputSymbol = some b := by
  have hn : n < input.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_cons] at this
    omega
  rw [inputSymbolInner n (by simp [wordsCfg]; omega) hn]
  have := congrArg List.head? h
  simpa [List.getElem?_eq_getElem hn] using this

/-- At the end of the input suffix the head reads a blank. -/
lemma inputSymbol_wordsCfg_nil {input : List Symbol} {n : ℕ} (h : input.drop n = [])
    (ws : Fin k → List Symbol) (q : Option State) (out : List Symbol) :
    (wordsCfg input q ws out ⟨min (n + 1) (input.length + 1), by omega⟩).inputSymbol = none := by
  have hn : input.length ≤ n := List.drop_eq_nil_iff.mp h
  apply inputSymbol_eq_none_of_boundary
  right
  simp [wordsCfg, Nat.min_eq_right (by omega : input.length + 1 ≤ n + 1)]

lemma Action.apply_wordsCfg_stay (input : List Symbol) (q q' : Option State) (n : ℕ)
    (out : List Symbol) (b : Option Symbol) :
    (Action.mk 0 Fin.elim0 b q').apply
      (wordsCfg input q (k := 0) Fin.elim0 out
        ⟨min (n + 1) (input.length + 1), by omega⟩) =
      wordsCfg input q' (k := 0) Fin.elim0 (out ++ b.toList)
        ⟨min (n + 1) (input.length + 1), by omega⟩ := by
  apply Cfg.ext_zero_tapes <;> simp [wordsCfg, Action.apply]

lemma Action.apply_wordsCfg_right (input : List Symbol) (q q' : Option State) (n : ℕ)
    (out : List Symbol) (b : Option Symbol) :
    (Action.mk 1 Fin.elim0 b q').apply
      (wordsCfg input q (k := 0) Fin.elim0 out
        ⟨min (n + 1) (input.length + 1), by omega⟩) =
      wordsCfg input q' (k := 0) Fin.elim0 (out ++ b.toList)
        ⟨min (n + 1 + 1) (input.length + 1), by omega⟩ := by
  apply Cfg.ext_zero_tapes
  · rfl
  · apply Fin.ext
    have h := val_moveInputPos_eq
      (wordsCfg input q (k := 0) Fin.elim0 out
        ⟨min (n + 1) (input.length + 1), by omega⟩).inputPos (1 : SignType)
    simp only [wordsCfg, Action.apply, SignType.cast] at *
    omega
  · rfl

end Turing
