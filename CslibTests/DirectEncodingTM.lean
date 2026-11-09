/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Encodings

open Cslib.Encoding Turing.MultiTapeTM Turing.MultiTapeTM.Encodings

example (w : List Bool) :
    delimitTM.ComputesInTimeAndSpace w (delimit w) (2 * w.length + 1) 0 :=
  delimit_computes w

example (suffix : List Bool) :
    undelimitTM.ComputesInTimeAndSpace (delimit [] ++ suffix) [] 1 0 :=
  undelimit_computes [] suffix

example : ComputableInTimeAndSpace Prod.fst (encPair encBits encBits) encBits
    (fun p => 2 * p.1.length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_fst _ _

-- An element code can be empty, and extraction need not inspect the following suffix.
example (suffix : List Bool) :
    Encodings.dropDelimited.ComputesInTimeAndSpace (delimit [] ++ suffix) suffix
      (suffix.length + 2) 0 := by
  simpa using dropDelimited_computes [] suffix

example : ComputableInTimeAndSpace Prod.snd (encPair encBits encBool) encBool
    (fun p => (encPair encBits encBool p).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_snd _ _

example : ComputableInTimeAndSpace some encBits (encOption encBits)
    (fun w => w.length + 2) (fun _ => 0) :=
  computableInTimeAndSpace_some _

example : ComputableInTimeAndSpace List.isEmpty (encList encBits) encBool
    (fun _ => 1) (fun _ => 0) :=
  computableInTimeAndSpace_isEmpty _

example : ComputableInTimeAndSpace Option.isSome (encOption encBits) encBool
    (fun _ => 1) (fun _ => 0) :=
  computableInTimeAndSpace_isSome _

example (default : List Bool) :
    ComputableInTimeAndSpace (fun l => l.headD default) (encList encBits) encBits
      (fun l => if l.isEmpty then 1 + max 1 default.length
        else 2 * (l.headD default).length + 2) (fun _ => 0) :=
  computableInTimeAndSpace_headD _ _

example (default : List Bool) :
    ComputableInTimeAndSpace (fun o => o.getD default) (encOption encBits) encBits
      (fun o => if o.isSome then (o.getD default).length + 3
        else 1 + max 1 default.length) (fun _ => 0) :=
  computableInTimeAndSpace_getD _ _

-- The machines share an input encoding, while their output types and encodings differ.
example : ComputableInTimeAndSpace (fun l : List (List Bool) => (l.isEmpty, l.tail))
    (encList encBits) (encPair encBool (encList encBits))
    (fun l => 4 * 1 + ((encList encBits l).length + 1) + 4) (fun _ => 0) := by
  simpa using (computableInTimeAndSpace_isEmpty encBits).pair
    (computableInTimeAndSpace_tail encBits)

-- Nonzero work-space bounds for the two components remain independent and additive.
example {α β γ : Type*} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (hf : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ComputableInTimeAndSpace (fun x => (f x, g x)) encIn (encPair enc₁ enc₂)
      (fun x => 4 * t₁ x + t₂ x + 4) (fun x => 3 * (s₁ x + s₂ x)) :=
  hf.pair hg

-- An incomplete trailing tag is discarded even when complete tagged bits precede it.
example : undelimitTM.ComputesInTimeAndSpace [true, false, true] [false] 4 0 := by
  simpa [undelimit] using undelimit_computes_word [true, false, true]

-- Without a terminator, dropping a component consumes the entire word.
example : Encodings.dropDelimited.ComputesInTimeAndSpace [true, false, true] [] 4 0 := by
  simpa [Cslib.Encoding.dropDelimited] using dropDelimited_computes_word [true, false, true]

example : Encodings.dropDelimited.ComputesInTimeAndSpace [] [] 1 0 := dropDelimited_nil

example : ComputableInTimeAndSpace List.tail (encList encBits) (encList encBits)
    (fun l => (encList encBits l).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_tail _
