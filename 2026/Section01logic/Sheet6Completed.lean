/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  assumption

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => intro hRifP _
             apply hRifP
             assumption
  | inr h => intro _ hRifQ
             apply hRifQ
             assumption

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · intro hRifP _
    apply hRifP
    assumption
  · intro _ hRifQ
    apply hRifQ
    assumption

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · intro hRifP _
    apply hRifP at h
    assumption
  · intro _ hRifQ
    apply hRifQ
    assumption

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  obtain h | h := hPoQ
  . right
    assumption
  . left
    assumption

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hPoQoR
  obtain h | h := hPoQoR
  . obtain h' | h' := h
    . left
      assumption
    . right
      left
      assumption
  . right
    right
    assumption
  intro hPoQoR
  obtain h | h := hPoQoR
  . left
    left
    assumption
  . obtain h' | h' := h
    . left
      right
      assumption
    . right
      assumption

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hRifP hSifQ hPoQ
  obtain h | h := hPoQ
  . left
    apply hRifP
    assumption
  . right
    apply hSifQ
    assumption

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hQifP hPoR
  obtain h | h := hPoR
  . left
    apply hQifP
    assumption
  . right
    assumption

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPiffR hQiffS
  constructor
  intro hPoQ
  obtain h | h := hPoQ
  . rw [hPiffR] at h
    left
    assumption
  . rw [hQiffS] at h
    right
    assumption
  intro hRoS
  obtain h | h := hRoS
  . cases' hPiffR with _ hRifP
    left
    apply hRifP at h
    assumption
  . cases' hQiffS with _ hSifQ
    apply hSifQ at h
    right
    assumption

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hnPoQ
  constructor
  intro hP
  apply hnPoQ
  left
  assumption
  intro hQ
  apply hnPoQ
  right
  assumption
  intro hnPnQ hPoQ
  obtain h | h := hPoQ
  . cases' hnPnQ with hnP _
    apply hnP
    assumption
  . cases' hnPnQ with _ hnQ
    apply hnQ
    assumption

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro hnPoQ
  by_cases h : P
  right
  intro hQ
  apply hnPoQ
  exact ⟨h,hQ⟩
  left
  assumption
  intro hnPonQ hPQ
  cases' hPQ with hP hQ
  obtain h | h := hnPonQ <;> (apply h ; assumption)
