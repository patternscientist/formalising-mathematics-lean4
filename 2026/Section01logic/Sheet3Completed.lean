/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  change True → False at h
  apply h
  trivial

example : False → ¬True := by
  intro h
  change True → False
  intro _
  exact h

example : ¬False → True := by
  intro _
  trivial

example : True → ¬False := by
  intro _
  change False → False
  intro h
  exact h

example : False → ¬P := by
  intro h
  change P → False
  intro _
  exact h

example : P → ¬P → False := by
  intro hP hnP
  change P → False at hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP
  change (P→False)→False
  intro hPF
  apply hPF
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  change P → False
  intro hP
  change Q → False at hnQ
  apply hPQ at hP
  apply hnQ
  exact hP


example : ¬¬False → False := by
  intro hnnF
  change (False→False)→False at hnnF
  apply hnnF
  intro hF
  exact hF

example : ¬¬P → P := by -- this isn't true constructively,
-- which is a clue `by_cases` will be needed @patternscientist
  intro hnnP
  change (P→False)→False at hnnP
  by_cases h : P
  exact h
  exfalso
  apply hnnP at h
  exact h

example : (¬Q → ¬P) → P → Q := by
  intro hnQnP hP
  by_cases h : Q
  exact h
  exfalso
  apply hnQnP at h
  apply h
  exact hP
