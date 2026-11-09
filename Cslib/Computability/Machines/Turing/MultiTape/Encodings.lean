/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Pair
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Induction

/-!
# Complexity of the default encodings

Direct machines implement delimited-word operations, tagging, copying, and first-cell tests.
Their time and zero-space bounds yield resource bounds for product projections, option
construction and extraction, and list inspection. First-component extraction stops at the
terminator, so its time depends only on the extracted word, independently of the suffix.

`head` and `getSome` operate on subtypes recording their preconditions; `headD` and `getD`
emit a fixed default on empty input. The general pairing combinator combines computations
with a common encoded input and independently chosen output encodings.
-/

public section

namespace Turing.MultiTapeTM.Encodings

open Turing Turing.MultiTapeTM Cslib.Encoding

-- A local abbreviation for the input position in the scanning invariants.
local notation "scanCfg" => fun input q n out =>
  wordsCfg input q (k := 0) Fin.elim0 out (Fin.mk (min (n + 1) (List.length input + 1)) (by omega))

/-- The control alternates between a marker and its data bit. -/
inductive Phase
  | marker | data
  deriving DecidableEq

instance : Finite Phase :=
  Finite.of_injective (fun | .marker => false | .data => true)
    (by intro a b; cases a <;> cases b <;> simp)

/-- Emit the tag in place, then copy the data bit and advance. EOF emits the delimiter. -/
def delimitTM : MultiTapeTM 0 Bool Phase :=
  ofTr .marker fun q s _ => match q, s with
    | .marker, some _ => ⟨0, Fin.elim0, some true, some .data⟩
    | .data, some b => ⟨1, Fin.elim0, some b, some .marker⟩
    | _, none => ⟨0, Fin.elim0, some false, none⟩

/-- Skip each true tag and copy its data bit. A false tag or EOF halts in place. -/
def undelimitTM : MultiTapeTM 0 Bool Phase :=
  ofTr .marker fun q s _ => match q, s with
    | .marker, some true => ⟨1, Fin.elim0, none, some .data⟩
    | .data, some b => ⟨1, Fin.elim0, some b, some .marker⟩
    | _, _ => ⟨0, Fin.elim0, none, none⟩

private lemma computes_of_run {State : Type*} {tm : MultiTapeTM 0 Bool State}
    {input out : List Bool}
    {t n : ℕ} (h : tm.runFrom (tm.initCfg input) t = scanCfg input none n out) :
    tm.ComputesInTimeAndSpace input out t 0 := by
  have hh := congrArg Cfg.state h
  exact ⟨⟨t, hh, by rw [h]; rfl⟩, runsInTime_of_halted hh, by simp⟩

private lemma delimit_run (w : List Bool) {input : List Bool} {n : ℕ}
    (h : input.drop n = w) (out : List Bool) :
    delimitTM.runFrom (scanCfg input (some Phase.marker) n out) (2 * w.length + 1) =
      scanCfg input none (n + w.length) (out ++ delimit w) := by
  induction w generalizing n out with
  | nil =>
    rw [show 2 * ([] : List Bool).length + 1 = 1 from rfl, runFrom_one,
      step_of_state rfl, inputSymbol_wordsCfg_nil h Fin.elim0, delimitTM, tr_ofTr,
      Action.apply_wordsCfg_stay]
    rfl
  | cons b w ih =>
    have hs := inputSymbol_wordsCfg_cons h Fin.elim0 (some Phase.marker) out
    have hs' := inputSymbol_wordsCfg_cons h Fin.elim0 (some Phase.data) (out ++ [true])
    have ht : input.drop (n + 1) = w := by
      rw [← List.drop_drop, h]
      rfl
    rw [show 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) by simp; omega,
      runFrom_add, runFrom_one, step_of_state rfl, hs, delimitTM, tr_ofTr,
      Action.apply_wordsCfg_stay]
    simp only [Option.toList_some]
    rw [runFrom_add, runFrom_one, step_of_state rfl, hs', tr_ofTr, Action.apply_wordsCfg_right]
    change delimitTM.runFrom _ _ = _
    rw [ih ht]
    simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Delimiting takes at most `2 * w.length + 1` steps and zero work space. -/
theorem delimit_computes (w : List Bool) :
    delimitTM.ComputesInTimeAndSpace w (delimit w) (2 * w.length + 1) 0 := by
  apply computes_of_run (n := w.length)
  have h := delimit_run w (input := w) (n := 0) (by simp) []
  simpa [wordsCfg_noTapes, MultiTapeNTM.initCfg, delimitTM, ofTr] using h

-- Extraction: the suffix remains unread when the false marker is reached.

private lemma undelimit_run (w suffix : List Bool) {input : List Bool} {n : ℕ}
    (h : input.drop n = delimit w ++ suffix) (out : List Bool) :
    undelimitTM.runFrom (scanCfg input (some Phase.marker) n out) (2 * w.length + 1) =
      scanCfg input none (n + 2 * w.length) (out ++ w) := by
  induction w generalizing n out with
  | nil =>
    have hs := inputSymbol_wordsCfg_cons h Fin.elim0 (some Phase.marker) out
    rw [show 2 * ([] : List Bool).length + 1 = 1 from rfl, runFrom_one,
      step_of_state rfl, hs, undelimitTM, tr_ofTr, Action.apply_wordsCfg_stay]
    simp
  | cons b w ih =>
    have hs := inputSymbol_wordsCfg_cons h Fin.elim0 (some Phase.marker) out
    have ht : input.drop (n + 1) = b :: (delimit w ++ suffix) := by
      rw [← List.drop_drop, h]
      rfl
    have hs' := inputSymbol_wordsCfg_cons ht Fin.elim0 (some Phase.data) out
    have ht' : input.drop (n + 1 + 1) = delimit w ++ suffix := by
      rw [← List.drop_drop, ht]
      rfl
    rw [show 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) by simp; omega,
      runFrom_add, runFrom_one, step_of_state rfl, hs, undelimitTM, tr_ofTr,
      Action.apply_wordsCfg_right]
    simp only [Option.toList_none, List.append_nil]
    rw [runFrom_add, runFrom_one, step_of_state rfl, hs', tr_ofTr, Action.apply_wordsCfg_right]
    change undelimitTM.runFrom _ _ = _
    rw [ih ht']
    simp [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Extract a delimited component in time independent of the suffix, using zero work space. -/
theorem undelimit_computes (w suffix : List Bool) :
    undelimitTM.ComputesInTimeAndSpace (delimit w ++ suffix) w (2 * w.length + 1) 0 := by
  apply computes_of_run (n := 2 * w.length)
  have h := undelimit_run w suffix (input := delimit w ++ suffix) (n := 0) (by simp) []
  simpa [wordsCfg_noTapes, MultiTapeNTM.initCfg, undelimitTM, ofTr] using h

private lemma undelimit_word_run (w : List Bool) {input : List Bool} {n : ℕ}
    (h : input.drop n = w) (out : List Bool) :
    ∃ m, undelimitTM.runFrom (scanCfg input (some Phase.marker) n out) (w.length + 1) =
      scanCfg input none m (out ++ undelimit w) := by
  induction w using List.twoStepInduction generalizing n out with
  | nil =>
    refine ⟨n, ?_⟩
    rw [show ([] : List Bool).length + 1 = 1 from rfl, runFrom_one, step_of_state rfl,
      inputSymbol_wordsCfg_nil h Fin.elim0, undelimitTM, tr_ofTr, Action.apply_wordsCfg_stay]
    simp [undelimit]
  | singleton b =>
    have ht : input.drop (n + 1) = [] := by rw [← List.drop_drop, h]; rfl
    cases b with
    | false =>
      refine ⟨n, ?_⟩
      rw [show [false].length + 1 = 1 + 1 from rfl, runFrom_add,
        runFrom_one (tm := undelimitTM) (scanCfg input (some Phase.marker) n out),
        step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0, undelimitTM, tr_ofTr,
        Action.apply_wordsCfg_stay, runFrom_one, step_of_halt rfl]
      simp [undelimit]
    | true =>
      refine ⟨n + 1, ?_⟩
      rw [show [true].length + 1 = 1 + 1 from rfl, runFrom_add,
        runFrom_one (tm := undelimitTM) (scanCfg input (some Phase.marker) n out),
        step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0, undelimitTM, tr_ofTr,
        Action.apply_wordsCfg_right, runFrom_one, step_of_state rfl,
        inputSymbol_wordsCfg_nil ht Fin.elim0, tr_ofTr, Action.apply_wordsCfg_stay]
      simp [undelimit]
  | cons_cons b c w ih _ =>
    cases b with
    | false =>
      refine ⟨n, ?_⟩
      rw [show (false :: c :: w).length + 1 = 1 + ((c :: w).length + 1) by simp; omega,
        runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0,
        undelimitTM, tr_ofTr, Action.apply_wordsCfg_stay]
      rw [runFrom_eq_of_halt _ _ (Nat.zero_le _) (τ := 0) rfl]
      simp [undelimit]
    | true =>
      have ht : input.drop (n + 1) = c :: w := by rw [← List.drop_drop, h]; rfl
      have ht' : input.drop (n + 1 + 1) = w := by rw [← List.drop_drop, ht]; rfl
      obtain ⟨m, hm⟩ := ih ht' (out ++ [c])
      refine ⟨m, ?_⟩
      rw [show (true :: c :: w).length + 1 = 1 + (1 + (w.length + 1)) by simp; omega,
        runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0,
        undelimitTM, tr_ofTr, Action.apply_wordsCfg_right]
      simp only [Option.toList_none, List.append_nil]
      rw [runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons ht Fin.elim0,
        tr_ofTr, Action.apply_wordsCfg_right]
      change undelimitTM.runFrom _ _ = _
      simp only [Option.toList_some]
      rw [hm]
      simp [undelimit, List.append_assoc]

/-- Extraction agrees with the pure operation on every Boolean word. An incomplete trailing
tag is ignored; missing terminators are treated as EOF. -/
theorem undelimit_computes_word (w : List Bool) :
    undelimitTM.ComputesInTimeAndSpace w (undelimit w) (w.length + 1) 0 := by
  obtain ⟨m, hm⟩ := undelimit_word_run w (input := w) (n := 0) (by simp) []
  apply computes_of_run (n := m)
  simpa [wordsCfg_noTapes, MultiTapeNTM.initCfg, undelimitTM, ofTr] using hm

private lemma computes_seq {State₁ State₂ : Type*} {tm₁ : MultiTapeTM 0 Bool State₁}
    {tm₂ : MultiTapeTM 0 Bool State₂} {input mid out : List Bool} {n m t₁ t₂ : ℕ}
    (h₁ : tm₁.runFrom (scanCfg input (some tm₁.q₀) 0 []) t₁ =
      scanCfg input none n mid)
    (h₂ : tm₂.runFrom (scanCfg input (some tm₂.q₀) n mid) t₂ =
      scanCfg input none m out) :
    (tm₁.seq tm₂).ComputesInTimeAndSpace input out (t₁ + t₂) 0 := by
  obtain ⟨t, ht, hr⟩ := exists_runFrom_seq h₁ rfl (by simpa [Cfg.withState] using h₂)
  have hinit : (scanCfg input (some tm₁.q₀) 0 []).mapState (handOver tm₂.q₀) =
      (tm₁.seq tm₂).initCfg input := by
    refine Cfg.ext_zero_tapes rfl ?_ rfl
    apply Fin.ext
    simp [wordsCfg_noTapes, MultiTapeNTM.initCfg]
  rw [hinit] at hr
  exact (computes_of_run (n := m) (by simpa [Cfg.mapState] using hr)).mono ht le_rfl

/-- The finitely many suffixes of a fixed word are the output states of its emitter. -/
abbrev EmitState (word : List Bool) : Type := {w : List Bool // w ∈ word.tails.toFinset}

private lemma emit_tail_mem {word w : List Bool} (hw : w ∈ word.tails.toFinset) :
    w.tail ∈ word.tails.toFinset := by
  simp only [List.mem_toFinset, List.mem_tails] at hw ⊢
  exact (List.tail_suffix w).trans hw

/-- Emit a fixed word without moving any head, halting on its last bit. -/
def emit (word : List Bool) : MultiTapeTM 0 Bool (EmitState word) :=
  ofTr ⟨word, by simp⟩ fun w _ _ =>
    ⟨0, Fin.elim0, w.val.head?, if w.val.tail = [] then none
      else some ⟨w.val.tail, emit_tail_mem w.property⟩⟩

private lemma emit_run (word w : List Bool) (hw : w ∈ word.tails.toFinset)
    (input : List Bool) (n : ℕ) (out : List Bool) :
    (emit word).runFrom (scanCfg input (some ⟨w, hw⟩) n out) (max 1 w.length) =
      scanCfg input none n (out ++ w) := by
  induction w generalizing out with
  | nil =>
    rw [show max 1 ([] : List Bool).length = 1 from rfl, runFrom_one, step_of_state rfl,
      emit, tr_ofTr, Action.apply_wordsCfg_stay]
    simp
  | cons b w ih =>
    cases w with
    | nil =>
      rw [show max 1 ([b] : List Bool).length = 1 from rfl, runFrom_one, step_of_state rfl,
        emit, tr_ofTr, Action.apply_wordsCfg_stay]
      simp
    | cons c w =>
      rw [show max 1 (b :: c :: w).length = 1 + max 1 (c :: w).length by simp; omega,
        runFrom_add, runFrom_one, step_of_state rfl, emit, tr_ofTr,
        ite_eq_right (by simp), Action.apply_wordsCfg_stay]
      change (emit word).runFrom _ _ = _
      change (emit word).runFrom
        (scanCfg input (some ⟨c :: w, emit_tail_mem hw⟩) n (out ++ [b])) _ = _
      simpa only [List.append_assoc, List.singleton_append] using
        ih (emit_tail_mem hw) (out ++ [b])

/-- Prepend a fixed word, then copy the input on the same tapes. -/
noncomputable def prepend (word : List Bool) := (emit word).seq (copy (Symbol := Bool))

theorem prepend_computes (word input : List Bool) :
    (prepend word).ComputesInTimeAndSpace input (word ++ input)
      (max 1 word.length + input.length + 1) 0 := by
  have h₁ := emit_run word word (by simp) input 0 []
  have h₂ := Copy.runFrom_suffix input (input := input) (n := 0) (by simp) word
  simpa [prepend, Nat.add_assoc] using computes_seq h₁ h₂

/-- Discard one input symbol and halt, leaving the head on its successor. -/
def skipFirst : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨1, Fin.elim0, none, none⟩

/-- Drop the first input symbol and copy the suffix. -/
noncomputable def dropFirst := skipFirst.seq (copy (Symbol := Bool))

theorem dropFirst_computes (b : Bool) (w : List Bool) :
    dropFirst.ComputesInTimeAndSpace (b :: w) w (w.length + 2) 0 := by
  have h₁ : skipFirst.runFrom (scanCfg (b :: w) (some ()) 0 []) 1 =
      scanCfg (b :: w) none 1 [] := by
    rw [runFrom_one, step_of_state rfl, skipFirst, tr_ofTr, Action.apply_wordsCfg_right]
    rfl
  have h₂ := Copy.runFrom_suffix w (input := b :: w) (n := 1) rfl []
  simpa only [dropFirst, List.nil_append, show 1 + (w.length + 1) = w.length + 2 by omega] using
    computes_seq (tm₁ := skipFirst) (tm₂ := copy) h₁ h₂

/-- Skip a delimited word, consuming its terminator before halting. -/
def skipDelimited : MultiTapeTM 0 Bool Phase :=
  ofTr .marker fun q s _ => match q, s with
    | .marker, some true => ⟨1, Fin.elim0, none, some .data⟩
    | .data, some _ => ⟨1, Fin.elim0, none, some .marker⟩
    | .marker, some false => ⟨1, Fin.elim0, none, none⟩
    | _, none => ⟨0, Fin.elim0, none, none⟩

/-- Skip the first delimited component, then copy the suffix. At EOF, halt in either phase. -/
noncomputable def dropDelimited : MultiTapeTM 0 Bool (Phase ⊕ Unit) :=
  let tm := skipDelimited.seq (copy (Symbol := Bool))
  ofTr tm.q₀ fun q inp work =>
    if inp.isNone then ⟨0, Fin.elim0, none, none⟩ else tm.tr q inp work

private lemma tr_dropDelimited (q : Phase ⊕ Unit) (s : Option Bool)
    (work : Fin 0 → Option Bool) :
    dropDelimited.tr q s work = match s with
      | none => ⟨0, Fin.elim0, none, none⟩
      | some b => match q with
        | .inl .marker => ⟨1, Fin.elim0, none,
            some (if b then .inl .data else .inr ())⟩
        | .inl .data => ⟨1, Fin.elim0, none, some (.inl .marker)⟩
        | .inr _ => ⟨1, Fin.elim0, some b, some (.inr ())⟩ := by
  rcases q with q | q <;> cases q <;> cases s with
  | none => simp [dropDelimited]
  | some b =>
    cases b <;>
      simp [dropDelimited, seq, combine, adaptedTr, skipDelimited, copy,
        MultiTapeNTM.Adapter.mapState]

private noncomputable def dropDelimited_copyHom {input : List Bool} :
    ((copy (Symbol := Bool)).stepRel input).Hom (dropDelimited.stepRel input) :=
  MultiTapeNTM.Follows.stepHom (state := Sum.inr)
    (adapter := .mapState (Option.map Sum.inr))
    (fun q heads a h => by
      rw [← tr_iff.mp h]
      apply tr_iff.mpr
      cases hs : heads.inputSymbol <;>
        simp [tr_dropDelimited, copy, hs, MultiTapeNTM.Adapter.mapState])
    (Cfg.mapState (Option.map Sum.inr)) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

private lemma dropDelimited_copy_run (w : List Bool) {input : List Bool} {n : ℕ}
    (h : input.drop n = w) (out : List Bool) :
    dropDelimited.runFrom (scanCfg input (some (.inr ())) n out) (w.length + 1) =
      scanCfg input none (n + w.length) (out ++ w) := by
  have hm := runFrom_map dropDelimited_copyHom (scanCfg input (some ()) n out)
    (w.length + 1)
  rw [Copy.runFrom_suffix w h out] at hm
  change dropDelimited.runFrom ((scanCfg input (some ()) n out).mapState _) _ =
    (scanCfg input none (n + w.length) (out ++ w)).mapState _ at hm
  simpa [Cfg.mapState] using hm

private lemma dropDelimited_word_run (w : List Bool) {input : List Bool} {n : ℕ}
    (h : input.drop n = w) (out : List Bool) :
    dropDelimited.runFrom (scanCfg input (some (.inl Phase.marker)) n out) (w.length + 1) =
      scanCfg input none (n + w.length) (out ++ Cslib.Encoding.dropDelimited w) := by
  induction w using List.twoStepInduction generalizing n with
  | nil =>
    rw [show ([] : List Bool).length + 1 = 1 from rfl, runFrom_one, step_of_state rfl,
      inputSymbol_wordsCfg_nil h Fin.elim0, tr_dropDelimited, Action.apply_wordsCfg_stay]
    simp [Cslib.Encoding.dropDelimited]
  | singleton b =>
    have ht : input.drop (n + 1) = [] := by rw [← List.drop_drop, h]; rfl
    rw [show [b].length + 1 = 1 + 1 from rfl, runFrom_add,
      runFrom_one (tm := dropDelimited) (scanCfg input (some (.inl Phase.marker)) n out),
      step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0]
    cases b <;>
      simp only [tr_dropDelimited, Bool.false_eq_true, ↓reduceIte,
        Action.apply_wordsCfg_right, Option.toList_none,
        List.append_nil] <;>
      rw [runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_nil ht Fin.elim0,
        tr_dropDelimited, Action.apply_wordsCfg_stay] <;>
      simp [Cslib.Encoding.dropDelimited]
  | cons_cons b c w ih _ =>
    have ht : input.drop (n + 1) = c :: w := by rw [← List.drop_drop, h]; rfl
    rw [show (b :: c :: w).length + 1 = 1 + ((c :: w).length + 1) by simp; omega,
      runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons h Fin.elim0]
    cases b with
    | false =>
      simp only [tr_dropDelimited, Bool.false_eq_true, ↓reduceIte,
        Action.apply_wordsCfg_right, Option.toList_none,
        List.append_nil]
      rw [dropDelimited_copy_run (c :: w) ht]
      simp only [Cslib.Encoding.dropDelimited]
      congr 1
      apply Fin.ext
      simp only [List.length_cons]
      omega
    | true =>
      have ht' : input.drop (n + 1 + 1) = w := by rw [← List.drop_drop, ht]; rfl
      simp only [tr_dropDelimited, ↓reduceIte,
        Action.apply_wordsCfg_right, Option.toList_none,
        List.append_nil]
      rw [show (c :: w).length + 1 = 1 + (w.length + 1) by simp; omega,
        runFrom_add, runFrom_one, step_of_state rfl, inputSymbol_wordsCfg_cons ht Fin.elim0,
        tr_dropDelimited, Action.apply_wordsCfg_right]
      simp only [Option.toList_none, List.append_nil]
      rw [ih ht']
      simp only [Cslib.Encoding.dropDelimited]
      congr 1
      apply Fin.ext
      simp only [List.length_cons]
      omega

/-- Dropping a component agrees with the pure operation on every Boolean word, including
missing terminators and incomplete tags. It takes one step per input bit and one final step. -/
theorem dropDelimited_computes_word (w : List Bool) :
    dropDelimited.ComputesInTimeAndSpace w (Cslib.Encoding.dropDelimited w) (w.length + 1) 0 := by
  apply computes_of_run (n := w.length)
  have h := dropDelimited_word_run w (input := w) (n := 0) (by simp) []
  simpa [wordsCfg_noTapes, MultiTapeNTM.initCfg, dropDelimited, seq, combine, skipDelimited, ofTr]
    using h

theorem dropDelimited_computes (w suffix : List Bool) :
    dropDelimited.ComputesInTimeAndSpace (delimit w ++ suffix) suffix
      (2 * w.length + suffix.length + 2) 0 := by
  have h := dropDelimited_computes_word (delimit w ++ suffix)
  rw [Cslib.Encoding.dropDelimited_delimit_append] at h
  apply h.mono _ le_rfl
  simp only [List.length_append, length_delimit]
  omega

/-- Decide a predicate of the first input symbol in one stationary halting step. -/
def peek (f : Option Bool → Option Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ inp _ => ⟨0, Fin.elim0, f inp, none⟩

theorem peek_computes (f : Option Bool → Option Bool) (input : List Bool) :
    (peek f).ComputesInTimeAndSpace input (f input.head?).toList 1 0 := by
  apply computes_of_run (n := 0)
  rw [runFrom_one, step_of_state rfl]
  have hs : ((peek f).initCfg input).inputSymbol = input.head? := by
    cases input <;> simp [MultiTapeNTM.initCfg, Cfg.inputSymbol]
  rw [hs, peek, tr_ofTr]
  apply Cfg.ext_zero_tapes <;> simp [MultiTapeNTM.initCfg, wordsCfg_noTapes, Action.apply]

/-- On empty input, emit `word`; otherwise run `tm` from the start of the input.
The dispatch takes one step and leaves every head in place. -/
noncomputable def onEmpty {State : Type*} (word : List Bool) (tm : MultiTapeTM 0 Bool State) :
    MultiTapeTM 0 Bool (Option (EmitState word ⊕ State)) :=
  ofTr none fun q inp work => match q with
    | none => ⟨0, Fin.elim0, none,
        some (some (if inp.isNone then .inl (emit word).q₀ else .inr tm.q₀))⟩
    | some (.inl q) =>
        { (emit word).tr q inp work with
          state := ((emit word).tr q inp work).state.map (some ∘ Sum.inl) }
    | some (.inr q) =>
        { tm.tr q inp work with state := (tm.tr q inp work).state.map (some ∘ Sum.inr) }

private noncomputable def onEmptyLeftHom {State : Type*} (word : List Bool)
    (tm : MultiTapeTM 0 Bool State) {input : List Bool} :
    ((emit word).stepRel input).Hom ((onEmpty word tm).stepRel input) :=
  MultiTapeNTM.Follows.stepHom (state := some ∘ Sum.inl)
    (adapter := .mapState (Option.map (some ∘ Sum.inl)))
    (fun q heads a h => by
      have ha := tr_iff.mp h
      change (emit word).tr q heads.inputSymbol heads.workTapeSymbols = a at ha
      apply tr_iff.mpr
      simp only [onEmpty, tr_ofTr, Function.comp_apply]
      rw [ha]
      rfl)
    (Cfg.mapState (Option.map (some ∘ Sum.inl))) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl)

private noncomputable def onEmptyRightHom {State : Type*} (word : List Bool)
    (tm : MultiTapeTM 0 Bool State) {input : List Bool} :
    (tm.stepRel input).Hom ((onEmpty word tm).stepRel input) :=
  MultiTapeNTM.Follows.stepHom (state := some ∘ Sum.inr)
    (adapter := .mapState (Option.map (some ∘ Sum.inr)))
    (fun q heads a h => by
      have ha := tr_iff.mp h
      change tm.tr q heads.inputSymbol heads.workTapeSymbols = a at ha
      apply tr_iff.mpr
      simp only [onEmpty, tr_ofTr, Function.comp_apply]
      rw [ha]
      rfl)
    (Cfg.mapState (Option.map (some ∘ Sum.inr))) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl)

private lemma onEmpty_step {State : Type*} (word : List Bool) (tm : MultiTapeTM 0 Bool State)
    (input : List Bool) :
    (onEmpty word tm).step ((onEmpty word tm).initCfg input) =
      scanCfg input
        (some (some (if input.head?.isNone then .inl (emit word).q₀ else .inr tm.q₀)))
        0 [] := by
  rw [step_of_state rfl]
  have hs : ((onEmpty word tm).initCfg input).inputSymbol = input.head? := by
    cases input <;> simp [MultiTapeNTM.initCfg, Cfg.inputSymbol]
  rw [hs, onEmpty, tr_ofTr]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, wordsCfg_noTapes, MultiTapeNTM.initCfg]

/-- The empty branch emits the default word without using work space. -/
theorem onEmpty_nil {State : Type*} (word : List Bool) (tm : MultiTapeTM 0 Bool State) :
    (onEmpty word tm).ComputesInTimeAndSpace [] word (1 + max 1 word.length) 0 := by
  apply computes_of_run (n := 0)
  rw [runFrom_add, runFrom_one, onEmpty_step]
  simp only [List.head?_nil, Option.isNone_none, ↓reduceIte]
  have h := runFrom_map (onEmptyLeftHom word tm)
    (scanCfg [] (some (emit word).q₀) 0 []) (max 1 word.length)
  rw [show (emit word).runFrom _ _ = scanCfg [] none 0 word by
    simpa [emit] using emit_run word word (by simp) [] 0 []] at h
  change (onEmpty word tm).runFrom
    ((scanCfg [] (some (emit word).q₀) 0 []).mapState _) _ =
      (scanCfg [] none 0 word).mapState _ at h
  simpa [Cfg.mapState] using h

/-- On nonempty input, dispatch adds one step to the selected computation. -/
theorem onEmpty_cons {State : Type*} (word : List Bool) (tm : MultiTapeTM 0 Bool State)
    (b : Bool) (input out : List Bool) {t : ℕ}
    (h : tm.ComputesInTimeAndSpace (b :: input) out t 0) :
    (onEmpty word tm).ComputesInTimeAndSpace (b :: input) out (1 + t) 0 := by
  obtain ⟨p, hh, hhalt, ho, ht, _⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h
  let q := p.map (onEmptyRightHom word tm)
  have hstep : (onEmpty word tm).Step ((onEmpty word tm).initCfg (b :: input)) q.head := by
    apply step_iff.mpr
    rw [onEmpty_step]
    change _ = (p.head.mapState (Option.map (some ∘ Sum.inr)))
    rw [hh]
    simp [wordsCfg_noTapes, MultiTapeNTM.initCfg, Cfg.init, Cfg.mapState]
  let final := q.cons ((onEmpty word tm).initCfg (b :: input)) hstep
  refine computesInTimeAndSpace_iff_exists_runPath.mpr ⟨final, by simp [final],
    (by simp only [final, RelSeries.last_cons]; change p.last.state.map _ = none; rw [hhalt]; rfl),
    (by simp only [final, RelSeries.last_cons]; exact ho),
    (by
      simp only [final, RelSeries.cons_length]
      change p.length + 1 ≤ 1 + t
      omega), ?_⟩
  simp [MultiTapeNTM.RunPath.space]

/-- Dropping a component from empty input halts immediately. -/
theorem dropDelimited_nil : dropDelimited.ComputesInTimeAndSpace [] [] 1 0 :=
  dropDelimited_computes_word []

end Turing.MultiTapeTM.Encodings

namespace Turing.MultiTapeTM

open Cslib.Encoding Turing.MultiTapeTM.Encodings

-- A local abbreviation for the input position in the scanning invariants.
local notation "scanCfg" => fun input q n out =>
  wordsCfg input q (k := 0) Fin.elim0 out (Fin.mk (min (n + 1) (List.length input + 1)) (by omega))


/-- Read the first component of a product in time independent of its second component. -/
theorem computableInTimeAndSpace_fst {α β : Type*}
    (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    ComputableInTimeAndSpace Prod.fst (encPair enc₁ enc₂) enc₁
      (fun p => 2 * (enc₁ p.1).length + 1) (fun _ => 0) :=
  ⟨0, Phase, inferInstance, undelimitTM, fun p => undelimit_computes (enc₁ p.1) (enc₂ p.2)⟩

/-- Read the head of a nonempty list in time independent of its tail. -/
theorem computableInTimeAndSpace_head {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace (fun l : {l : List α // l ≠ []} => l.val.head l.property)
      ((Function.Embedding.subtype (fun l : List α => l ≠ [])).trans (encList enc)) enc
      (fun l => 2 * (enc (l.val.head l.property)).length + 1) (fun _ => 0) := by
  refine ⟨0, Phase, inferInstance, undelimitTM, ?_⟩
  rintro ⟨l, hl⟩
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a l => exact undelimit_computes (enc a) (encList enc l)

/-- A pair consisting of an element and a list already has the encoding of their cons. -/
theorem computableInTimeAndSpace_cons {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc)
      (fun p => (encPair enc (encList enc) p).length + 1) (fun _ => 0) :=
  ⟨0, Unit, inferInstance, copy, fun p =>
    Copy.computesInTimeAndSpace (encPair enc (encList enc) p)⟩

/-- Read the second component by skipping the first delimited component, then copying. -/
theorem computableInTimeAndSpace_snd {α β : Type*}
    (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    ComputableInTimeAndSpace Prod.snd (encPair enc₁ enc₂) enc₂
      (fun p => (encPair enc₁ enc₂ p).length + 1) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, Encodings.dropDelimited, fun p => ?_⟩
  apply (dropDelimited_computes (enc₁ p.1) (enc₂ p.2)).mono _ le_rfl
  dsimp only
  rw [length_encPair]
  omega

/-- Adding the `some` tag takes one emission step followed by a copy. -/
theorem computableInTimeAndSpace_some {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace some enc (encOption enc)
      (fun a => (enc a).length + 2) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, prepend [true], fun a => ?_⟩
  apply (prepend_computes [true] (enc a)).mono _ le_rfl
  simp only [List.length_singleton, max_self]
  omega

/-- Remove the tag from an option known to be `some`. -/
theorem computableInTimeAndSpace_getSome {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace (fun o : {o : Option α // o.isSome} => o.val.get o.property)
      ((Function.Embedding.subtype (fun o : Option α => o.isSome)).trans (encOption enc)) enc
      (fun o => (enc (o.val.get o.property)).length + 2) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, dropFirst, ?_⟩
  rintro ⟨o, ho⟩
  cases o with
  | none => contradiction
  | some a => exact dropFirst_computes true (enc a)

/-- Read a list's tail by skipping its first delimited element and copying the rest. -/
theorem computableInTimeAndSpace_tail {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace List.tail (encList enc) (encList enc)
      (fun l => (encList enc l).length + 1) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, Encodings.dropDelimited, ?_⟩
  intro l
  cases l with
  | nil => exact dropDelimited_nil
  | cons a l =>
    apply (dropDelimited_computes (enc a) (encList enc l)).mono _ le_rfl
    simp only [encList_cons, List.length_append, length_delimit]
    omega

/-- Empty-list testing only inspects the first input cell. -/
theorem computableInTimeAndSpace_isEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace List.isEmpty (encList enc) encBool (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, peek (fun b => some b.isNone), ?_⟩
  intro l
  cases l with
  | nil => exact peek_computes _ []
  | cons a l =>
    simpa [delimit] using peek_computes (fun b => some b.isNone) (encList enc (a :: l))

/-- Testing whether an option is `some` only inspects the first input cell. -/
theorem computableInTimeAndSpace_isSome {α : Type*} (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace Option.isSome (encOption enc) encBool (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, peek (fun b => some b.isSome), ?_⟩
  intro o
  cases o with
  | none => exact peek_computes _ []
  | some a => simpa using peek_computes (fun b => some b.isSome) (true :: enc a)

/-- A total head operation: emit the default on `[]`, otherwise read one delimited element. -/
theorem computableInTimeAndSpace_headD {α : Type*} (enc : α ↪ List Bool) (default : α) :
    ComputableInTimeAndSpace (fun l => l.headD default) (encList enc) enc
      (fun l => if l.isEmpty then 1 + max 1 (enc default).length
        else 2 * (enc (l.headD default)).length + 2) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, onEmpty (enc default) undelimitTM, ?_⟩
  intro l
  cases l with
  | nil => exact onEmpty_nil _ _
  | cons a l =>
    have hn : encList enc (a :: l) ≠ [] := by simp
    obtain ⟨b, w, hw⟩ := List.exists_cons_of_ne_nil hn
    have h : undelimitTM.ComputesInTimeAndSpace (encList enc (a :: l)) (enc a)
        (2 * (enc a).length + 1) 0 := undelimit_computes (enc a) (encList enc l)
    rw [hw] at h
    have hc := onEmpty_cons (enc default) undelimitTM b w (enc a) h
    rw [hw]
    apply hc.mono _ le_rfl
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons]
    omega

/-- A total option projection: emit the default on `none`, otherwise remove the `some` tag. -/
theorem computableInTimeAndSpace_getD {α : Type*} (enc : α ↪ List Bool) (default : α) :
    ComputableInTimeAndSpace (fun o => o.getD default) (encOption enc) enc
      (fun o => if o.isSome then (enc (o.getD default)).length + 3
        else 1 + max 1 (enc default).length) (fun _ => 0) := by
  refine ⟨0, _, inferInstance, onEmpty (enc default) dropFirst, ?_⟩
  intro o
  cases o with
  | none => exact onEmpty_nil _ _
  | some a =>
    have hc := onEmpty_cons (enc default) dropFirst true (enc a) (enc a)
      (dropFirst_computes true (enc a))
    apply hc.mono _ le_rfl
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
    omega

end Turing.MultiTapeTM
