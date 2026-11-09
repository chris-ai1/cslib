/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Logic.Embedding.Basic
public import Cslib.Computability.Encoding.Delimit

/-!
# Default encodings

Embeddings for products, options, and lists into Boolean words.
Products delimit their first component; lists delimit each element. Options use the empty
word for `none` and prefix `some` with `true`. These choices work even for empty element codes.
-/

@[expose] public section

namespace Cslib.Encoding

variable {α β : Type*}

/-- A Boolean is encoded by its single bit. -/
def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => (List.cons.inj h).1⟩

/-- Boolean words already are codes. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

@[simp] theorem encBool_apply (b : Bool) : encBool b = [b] := rfl

@[simp] theorem encBits_apply (w : List Bool) : encBits w = w := rfl

/-- A product is the delimited first component followed by the second component. -/
def encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨fun p => delimit (enc₁ p.1) ++ enc₂ p.2, fun _ _ h =>
    Prod.ext (enc₁.injective (delimit_append_inj h).1)
      (enc₂.injective (delimit_append_inj h).2)⟩

/-- The empty word represents `none`; `some a` is `true` followed by the code of `a`. -/
def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by
    rintro (_ | a) (_ | b) h <;> simp_all⟩

/-- A list is the concatenation of the delimited codes of its elements. -/
def encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (delimit ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' =>
        rw [enc.injective (delimit_append_inj h).1, ih _ (delimit_append_inj h).2]⟩

@[simp] theorem encPair_apply (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    encPair enc₁ enc₂ p = delimit (enc₁ p.1) ++ enc₂ p.2 := rfl

@[simp] theorem encOption_none (enc : α ↪ List Bool) : encOption enc none = [] := rfl

@[simp] theorem encOption_some (enc : α ↪ List Bool) (a : α) :
    encOption enc (some a) = true :: enc a := rfl

@[simp] theorem encList_nil (enc : α ↪ List Bool) : encList enc [] = [] := rfl

@[simp] theorem encList_cons (enc : α ↪ List Bool) (a : α) (l : List α) :
    encList enc (a :: l) = delimit (enc a) ++ encList enc l := rfl

theorem length_encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (encPair enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

@[simp] theorem length_encOption (enc : α ↪ List Bool) (o : Option α) :
    (encOption enc o).length = o.elim 0 (fun a => (enc a).length + 1) := by
  cases o <;> simp

@[simp] theorem length_encList (enc : α ↪ List Bool) (l : List α) :
    (encList enc l).length = (l.map fun a => 2 * (enc a).length + 1).sum := by
  induction l <;> simp_all

/-- Delimiters account for at least one bit per list element, even for empty element codes. -/
theorem length_le_length_encList (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  induction l <;> simp_all; omega

end Cslib.Encoding
