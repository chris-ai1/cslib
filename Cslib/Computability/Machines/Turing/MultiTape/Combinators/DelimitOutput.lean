/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Delimit
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option

/-!
# Delimiting the output of a machine

`delimitOutput tm` emits each output bit of `tm` as a true tag followed by that bit, then
emits a false terminator. Each original transition takes two steps; the second only emits the
pending bit. The work tapes follow the original run and use exactly the same cells.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State : Type*} {input : List Bool}

/-- Control for delimiting output: an original state (or the closing state `none`), or a
pending output bit together with the next original state. -/
abbrev DelimitOutputState (State : Type*) := Option State ⊕ (Option State × Option Bool)

/-- Delimit the output of `tm`, using two steps per original transition and one closing step. -/
noncomputable def delimitOutput (tm : MultiTapeTM k Bool State) :
    MultiTapeTM k Bool (DelimitOutputState State) :=
  ofTr (.inl (some tm.q₀)) fun q inp work => match q with
    | .inl (some q) =>
      let a := tm.tr q inp work
      { a with output := a.output.map (fun _ => true), state := some (.inr (a.state, a.output)) }
    | .inr (q, b) => ⟨0, fun _ => (none, 0), b, some (.inl q)⟩
    | .inl none => ⟨0, fun _ => (none, 0), some false, none⟩

namespace DelimitOutput

private def cfg (c : Cfg k Bool State input) : Cfg k Bool (DelimitOutputState State) input :=
  { c with state := some (.inl c.state), output := c.output.flatMap (fun b => [true, b]) }

private def pending (c : Cfg k Bool State input) (a : Action k Bool State) :
    Cfg k Bool (DelimitOutputState State) input :=
  { (a.apply c) with
    state := some (.inr (a.state, a.output))
    output := c.output.flatMap (fun b => [true, b]) ++ (a.output.map (fun _ => true)).toList }

private lemma step_active (tm : MultiTapeTM k Bool State) (c : Cfg k Bool State input)
    {q : State} (hq : c.state = some q) :
    tm.delimitOutput.step (cfg c) = pending c (tm.tr q c.inputSymbol c.workTapeSymbols) := by
  rw [step_of_state (q := Sum.inl (some q)) (by simp [cfg, hq]),
    delimitOutput, tr_ofTr]
  rfl

private lemma step_pending (tm : MultiTapeTM k Bool State) (c : Cfg k Bool State input)
    (a : Action k Bool State) :
    tm.delimitOutput.step (pending c a) = cfg (a.apply c) := by
  rw [step_of_state rfl, delimitOutput, tr_ofTr]
  cases ha : a.output <;> refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [ha, pending, cfg, Action.apply, List.flatMap_append, List.append_assoc]

private lemma step_close (tm : MultiTapeTM k Bool State) (c : Cfg k Bool State input)
    (hc : c.Halted) :
    tm.delimitOutput.step (cfg c) =
      { c with state := none, output := Cslib.Encoding.delimit c.output } := by
  rw [step_of_state (q := Sum.inl none) (by simp [cfg, hc]), delimitOutput, tr_ofTr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl <;> simp [cfg, Action.apply]

/-- Simulate a running path inside any fixed sets of allowed work-head positions. -/
private lemma lift_running (tm : MultiTapeTM k Bool State)
    (p : RelSeries (tm.runningStepRel input)) (S : Fin k → Finset ℤ)
    (hp : ∀ c ∈ p, ∀ i, c.workTapePos i ∈ S i) :
    ∃ q : tm.delimitOutput.RunPath input, q.head = cfg p.head ∧ q.last = cfg p.last ∧
      q.length ≤ 2 * p.length ∧ ∀ c ∈ q, ∀ i, c.workTapePos i ∈ S i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    exact ⟨.singleton _ (cfg c), rfl, rfl, le_rfl, fun _ ⟨n, hn⟩ i =>
      hn ▸ hp c ⟨0, rfl⟩ i⟩
  | snoc p c hc ih =>
    obtain ⟨q, hh, hl, ht, hmem⟩ := ih fun d hd => hp d (RelSeries.mem_snoc.mpr (.inl hd))
    obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp hc.1
    let a := tm.tr state p.last.inputSymbol p.last.workTapeSymbols
    have heq : a.apply p.last = c := (step_of_state hs).symm.trans (step_iff.mp hc.2)
    refine ⟨(q.snoc (pending p.last a) (by
      rw [hl]
      exact step_iff.mpr (step_active tm p.last hs))).snoc (cfg c) (by
      rw [RelSeries.last_snoc, ← heq]
      exact step_iff.mpr (step_pending tm p.last a)),
      by simpa using hh, by simp, by simp only [RelSeries.snoc_length]; omega, ?_⟩
    have hcpos := hp c (RelSeries.mem_snoc.mpr (.inr rfl))
    intro d hd i
    simp only [RelSeries.mem_snoc] at hd
    rcases hd with (hd | rfl) | rfl
    · exact hmem d hd i
    · simpa only [pending, heq] using hcpos i
    · exact hcpos i

end DelimitOutput

open DelimitOutput in
/-- Output delimiting doubles the running time, adds one closing step, and preserves space. -/
theorem ComputesInTimeAndSpace.delimitOutput {tm : MultiTapeTM k Bool State}
    {input output : List Bool} {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.delimitOutput.ComputesInTimeAndSpace input (Cslib.Encoding.delimit output)
      (2 * t + 1) s := by
  obtain ⟨p, hh, hhalt, ho, ht, hs⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h
  obtain ⟨pr, hhr, hlr, htr, hmemr⟩ := p.exists_running hhalt
  obtain ⟨q, hhq, hlq, htq, hmemq⟩ := lift_running tm pr p.visitedByTapeHead
    (fun c hc i => p.mem_visitedByTapeHead.mpr ⟨c, hmemr c hc, rfl⟩)
  let last : Cfg k Bool (DelimitOutputState State) input :=
    { p.last with state := none, output := Cslib.Encoding.delimit p.last.output }
  have hclose : tm.delimitOutput.Step q.last last := by
    apply step_iff.mpr
    rw [hlq, hlr]
    exact step_close tm p.last hhalt
  let final : tm.delimitOutput.RunPath input := q.snoc last hclose
  refine computesInTimeAndSpace_iff_exists_runPath.mpr ⟨final,
    (by simp only [final, RelSeries.head_snoc, hhq, hhr, hh]; rfl),
    (by simp only [final, RelSeries.last_snoc]; rfl),
    (by simpa only [final, RelSeries.last_snoc] using congrArg Cslib.Encoding.delimit ho),
    (by change q.length + 1 ≤ 2 * t + 1; omega), ?_⟩
  rw [show final.space = q.space from q.space_snoc_eq last hclose (by rw [hlq, hlr]; rfl)]
  exact (q.space_le_sum_card hmemq).trans hs

end Turing.MultiTapeTM
