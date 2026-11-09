/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.DelimitOutput

/-!
# Pairing computations with a common input

`pair tm₁ tm₂` computes the default pair encoding of the two outputs. It delimits the first
output as it is produced, rewinds the input, then runs the second machine on separate work
tapes. The input is shared; the output encodings may differ. No intermediate word is stored
on a work tape, and neither component computation needs to restore its tapes before halting.
-/

public section

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {State₁ State₂ : Type*}

/-- Compute a delimited first result followed by a second result on the same input. -/
noncomputable def pair (tm₁ : MultiTapeTM k₁ Bool State₁) (tm₂ : MultiTapeTM k₂ Bool State₂) :=
  tm₁.delimitOutput.concatenate tm₂

/-- Pairing computations takes linear overhead in time and additive work space.
The conservative space estimate counts stationary tape cells in multiple sequential phases. -/
theorem ComputesInTimeAndSpace.pair {tm₁ : MultiTapeTM k₁ Bool State₁}
    {tm₂ : MultiTapeTM k₂ Bool State₂} {input out₁ out₂ : List Bool} {t₁ t₂ s₁ s₂ : ℕ}
    (h₁ : tm₁.ComputesInTimeAndSpace input out₁ t₁ s₁)
    (h₂ : tm₂.ComputesInTimeAndSpace input out₂ t₂ s₂) :
    (tm₁.pair tm₂).ComputesInTimeAndSpace input (Cslib.Encoding.delimit out₁ ++ out₂)
      (4 * t₁ + t₂ + 4) (s₁ + s₂ + 2 * (k₁ + k₂)) := by
  exact (h₁.delimitOutput.concatenate h₂).mono (by omega) le_rfl

/-- Pair two computed values, allowing different output encodings and resource bounds.
Both machines receive the same encoded input. In particular, pairing two computations with
zero work space still uses zero work space. -/
theorem ComputableInTimeAndSpace.pair {α β γ : Type*} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (h₂ : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ComputableInTimeAndSpace (fun x => (f x, g x)) encIn (Cslib.Encoding.encPair enc₁ enc₂)
      (fun x => 4 * t₁ x + t₂ x + 4) (fun x => 3 * (s₁ x + s₂ x)) := by
  obtain ⟨k₁, State₁, _, tm₁, hm₁⟩ := h₁
  obtain ⟨k₂, State₂, _, tm₂, hm₂⟩ := h₂
  refine ⟨k₁ + k₂, _, inferInstance, tm₁.pair tm₂, fun x => ?_⟩
  have hk₁ := (hm₁ x).2.2.le
  have hk₂ := (hm₂ x).2.2.le
  exact ((hm₁ x).pair (hm₂ x)).mono le_rfl (by dsimp only; omega)

/-- Cons the results of two computations on a common input, using the default list encoding. -/
theorem ComputableInTimeAndSpace.cons {α β : Type*} {f : α → β} {g : α → List β}
    {encIn : α ↪ List Bool} {enc : β ↪ List Bool} {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : ComputableInTimeAndSpace f encIn enc t₁ s₁)
    (h₂ : ComputableInTimeAndSpace g encIn (Cslib.Encoding.encList enc) t₂ s₂) :
    ComputableInTimeAndSpace (fun x => f x :: g x) encIn (Cslib.Encoding.encList enc)
      (fun x => 4 * t₁ x + t₂ x + 4) (fun x => 3 * (s₁ x + s₂ x)) := by
  obtain ⟨k, State, _, tm, h⟩ := h₁.pair h₂
  exact ⟨k, State, inferInstance, tm, h⟩

end Turing.MultiTapeTM
