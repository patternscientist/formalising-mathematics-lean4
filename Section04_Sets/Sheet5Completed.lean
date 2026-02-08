/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
ext a
constructor
intro h
cases' h with ha ha'
exact ha
exact ha'
intro h
left
exact h


example : A ∩ A = A := by
  ext a
  constructor
  intro h
  cases' h with ha _
  exact ha
  intro h
  constructor
  exact h
  exact h

example : A ∩ ∅ = ∅ := by
  ext a
  constructor
  intro h
  cases' h with _ har
  exact har
  intro h
  constructor
  exfalso
  exact h
  exact h




example : A ∪ univ = univ := by
  ext a
  constructor
  intro h
  cases' h with _ har
  triv
  exact har
  intro _
  right
  triv

example : A ⊆ B → B ⊆ A → A = B := by
  intro hab hba
  ext w
  constructor
  intro hwa
  rw [subset_def] at hab
  specialize hab w hwa
  exact hab
  intro wb
  rw [subset_def] at hba
  specialize hba w wb
  exact hba

example : A ∩ B = B ∩ A := by
  ext c
  constructor
  intro hcab
  cases' hcab with hca hcb
  exact ⟨hcb,hca⟩
  intro hcba
  cases' hcba with hcb hca
  exact ⟨hca,hcb⟩

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext d
  constructor
  intro hdabc
  cases' hdabc with hda hdbc
  cases' hdbc with hdb hdc
  exact ⟨⟨hda,hdb⟩,hdc⟩
  intro hdabc
  constructor
  cases' hdabc with hdab _
  cases' hdab with hda _
  exact hda
  cases' hdabc with hdab hdc
  cases' hdab with _ hdb
  exact ⟨hdb,hdc⟩

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext d
  constructor
  intro hdabc
  cases' hdabc with hda hdbc
  left
  left
  exact hda
  cases' hdbc with hdb hdc
  left
  right
  exact hdb
  right
  exact hdc
  intro hdabc
  cases' hdabc with hdab hdc
  cases' hdab with hda hdb
  left
  exact hda
  right
  left
  exact hdb
  right
  right
  exact hdc

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext d
  constructor
  intro hdabc
  cases' hdabc with hda hdbc
  constructor
  left
  exact hda
  left
  exact hda
  cases' hdbc with hdb hdc
  constructor
  right
  exact hdb
  right
  exact hdc
  intro hdabac
  cases' hdabac with hdab hdac
  cases' hdab with hda1 hdb
  cases' hdac with hda2 hdac
  left
  exact hda1
  left
  exact hda1
  cases' hdac with hda hdc
  left
  exact hda
  right
  exact ⟨hdb,hdc⟩

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext d
  constructor
  intro hdabc
  cases' hdabc with hda hdbc
  cases' hdbc with hdb hdc
  left
  exact ⟨hda,hdb⟩
  right
  exact ⟨hda,hdc⟩
  intro hdabac
  cases' hdabac with hdab hdac
  cases' hdab with hda hdb
  constructor
  exact hda
  left
  exact hdb
  cases' hdac with hda hdc
  constructor
  exact hda
  right
  exact hdc
