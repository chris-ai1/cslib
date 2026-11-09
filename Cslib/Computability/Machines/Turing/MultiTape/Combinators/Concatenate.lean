/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum

/-!
# Concatenating the outputs of two machines on the same input

`concatenate tm₁ tm₂` runs the machines on disjoint groups of work tapes, rewinding the input
between them. The second machine starts on blank tapes and appends to the first machine's
output. Neither machine needs to clear its tapes or reset its heads before halting.
-/

public section

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol State₁ State₂ : Type*}

/-- Run two machines on the same input, concatenating their outputs and using disjoint
work tapes. -/
noncomputable def concatenate (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (tm₂ : MultiTapeTM k₂ Symbol State₂) :
    MultiTapeTM (k₁ + k₂) Symbol ((State₁ ⊕ RewindState) ⊕ State₂) :=
  ((tm₁.extendTapes (Fin.castAddEmb k₂)).seq
    ((rewindInput Symbol).extendTapes (noTapes (k₁ + k₂)))).seq
      (tm₂.extendTapes (Fin.natAddEmb k₁))

/-- Concatenating two computations preserves additive space bounds. Rewinding costs at most the
first computation's time plus two steps. The space estimate sums phase bounds, counting
stationary tape cells more than once; the additive term is conservative accounting. -/
theorem ComputesInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {input out₁ out₂ : List Symbol} {t₁ t₂ s₁ s₂ : ℕ}
    (h₁ : tm₁.ComputesInTimeAndSpace input out₁ t₁ s₁)
    (h₂ : tm₂.ComputesInTimeAndSpace input out₂ t₂ s₂) :
    (tm₁.concatenate tm₂).ComputesInTimeAndSpace input (out₁ ++ out₂)
      (2 * t₁ + t₂ + 2) (s₁ + s₂ + 2 * (k₁ + k₂)) := by
  obtain ⟨p₁, hh₁, hhalt₁, ho₁, ht₁, hs₁⟩ := h₁.exists_runPath
  obtain ⟨p₂, hh₂, hhalt₂, ho₂, ht₂, hs₂⟩ := h₂.exists_runPath
  let pa := p₁.map (embedHom tm₁ (Fin.castAddEmb k₂) (fun _ _ => none) (fun _ => 0))
  let c := pa.last
  obtain ⟨pr, hhr, hrlast, htr, hsr⟩ := exists_runPath_rewindInput c
  let pb := (p₂.map (tm₂.prependOutputHom out₁)).map
    (embedHom tm₂ (Fin.natAddEmb k₁) c.workTapes c.workTapePos)
  have hjoin : pb.head = pr.last.withState (some tm₂.q₀) := by
    simp [pb, hrlast, hh₂, c, pa, embed_natAddEmb, embed_castAddEmb,
      Cfg.prependOutput, Cfg.withState, MultiTapeNTM.initCfg, Cfg.init, Function.comp_def, ho₁]
  obtain ⟨par, hhar, hlar, htar, hsar⟩ := exists_runPath_seq_space_le (p₁ := pa) (p₂ := pr)
    (by change (embed _ p₁.last _ _).Halted; exact hhalt₁) hhr
  obtain ⟨p, hh, hl, ht, hsp⟩ := exists_runPath_seq_space_le (p₁ := par) (p₂ := pb)
    (by rw [hlar, hrlast]; rfl)
    (by simpa [hlar, hrlast, Cfg.withState, Cfg.mapState] using hjoin)
  apply computesInTimeAndSpace_of_runPath (p := p)
    (by
      simp only [hh, hhar, pa, RelSeries.head_map, embedHom_apply, hh₁, embed_init]
      rfl)
    (by simpa [hl, pb, Cfg.Halted, Cfg.mapState, embed, Cfg.prependOutput] using hhalt₂)
    (by simp [hl, pb, Cfg.mapState, embed, Cfg.prependOutput, ho₂])
  · have hin : c.inputPos.val ≤ 1 + p₁.length := by
      change (p₁ (Fin.last p₁.length)).inputPos.val ≤ _
      rw [runPath_apply_eq_runFrom, hh₁]
      exact inputPos_runFrom_le ..
    simp only [pa, pb, RelSeries.map_length] at htar ht
    omega
  · have hsPa : pa.space ≤ s₁ + k₂ :=
      (space_map_embedHom_le ..).trans (by omega)
    have hsPb : pb.space ≤ s₂ + k₁ :=
      (space_map_embedHom_le ..).trans (by change p₂.space + _ ≤ _; omega)
    omega

/-- Compute a function whose encoded output is the concatenation of two computed outputs.
The input encoding is shared; the output types and encodings may differ. -/
theorem ComputesFunInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Symbol} {enc₁ : β ↪ List Symbol} {enc₂ : γ ↪ List Symbol}
    {encOut : δ ↪ List Symbol}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : tm₁.ComputesFunInTimeAndSpace encIn enc₁ f₁ t₁ s₁)
    (h₂ : tm₂.ComputesFunInTimeAndSpace encIn enc₂ f₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    (tm₁.concatenate tm₂).ComputesFunInTimeAndSpace encIn encOut f
      (fun x => 2 * t₁ x + t₂ x + 2) (fun x => s₁ x + s₂ x + 2 * (k₁ + k₂)) := by
  intro x
  rw [henc]
  exact (h₁ x).concatenate (h₂ x)

/-- A function whose encoding concatenates two computed outputs is computable with linear time
and additive space overhead. The result function and encoding are specified by `henc`. -/
theorem ComputableInTimeAndSpace.concatenate {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {encOut : δ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : ComputableInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn enc₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInTimeAndSpace f encIn encOut (fun x => 2 * t₁ x + t₂ x + 2)
      (fun x => 3 * (s₁ x + s₂ x)) := by
  obtain ⟨k₁, State₁, _, tm₁, hm₁⟩ := h₁
  obtain ⟨k₂, State₂, _, tm₂, hm₂⟩ := h₂
  refine ⟨k₁ + k₂, _, inferInstance, tm₁.concatenate tm₂,
    (hm₁.concatenate hm₂ henc).mono (fun _ => le_rfl) ?_⟩
  intro x
  have hk₁ := (hm₁ x).2.2.le
  have hk₂ := (hm₂ x).2.2.le
  omega

end Turing.MultiTapeTM
