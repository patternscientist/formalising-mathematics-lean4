/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPQ hPR hQR
  cases' hPQ with hP hQ
  exact hPR hP
  exact hQR hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPQ
  cases' hPQ with hP hQ
  right
  exact hP
  left
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hPQR
  cases' hPQR with hPQ hR
  cases' hPQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR
  intro hPQR
  cases' hPQR with hP hQR
  left
  left
  exact hP
  cases' hQR with hQ hR
  left
  right
  exact hQ
  right
  exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPQ
  cases' hPQ with hP hQ
  left
  exact hPR hP
  right
  exact hQS hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPR
  cases' hPR with hP hR
  left
  exact hPQ hP
  right
  exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  rw [hPR]
  rw [hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hnPQ
  constructor
  intro hP
  apply hnPQ
  left
  exact hP
  intro hQ
  apply hnPQ
  right
  exact hQ
  intro hnPnQ hPQ
  cases' hPQ with hP hQ
  cases' hnPnQ with hnP hnQ
  apply hnP
  exact hP
  cases' hnPnQ with hnP hnQ
  apply hnQ
  exact hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by --- this one was trickiest; I had to come back to it after a day or two
  constructor
  intro hnPQ
  by_cases hP : P
  by_cases hQ : Q
  exfalso
  exact hnPQ ⟨hP,hQ⟩
  right
  exact hQ
  left
  exact hP
  intro hnPnQ hPQ
  cases' hPQ with hP hQ
  cases' hnPnQ with hnP hnQ
  exact hnP hP
  exact hnQ hQ
  done
