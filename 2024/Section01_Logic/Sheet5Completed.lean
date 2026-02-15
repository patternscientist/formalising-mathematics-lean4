/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPQ
  rw [hPQ]
  intro hQP
  rw [hQP]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  rwa [hPQ]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hPQ
  cases' hPQ with hP hQ
  exact ⟨hQ,hP⟩
  intro hQP
  cases' hQP with hQ hP
  exact ⟨hP,hQ⟩
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by --- implicitly meaning ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R)
  constructor
  intro hPQR
  cases' hPQR with hPQ hR
  cases' hPQ with hP hQ
  exact ⟨hP,hQ,hR⟩
  intro hPQR
  cases' hPQR with hP hQR
  cases' hQR with hQ hR
  exact ⟨⟨hP,hQ⟩,hR⟩
  done

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  triv
  intro hPT
  cases' hPT with hP _
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor
  intro hF
  constructor
  exfalso
  exact hF
  exact hF
  intro hPF
  cases' hPF with _ hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  rw [hPQ]
  rw [hRS]
  done

example : ¬(P ↔ ¬P) := by
  intro hPiffnP
  cases' hPiffnP with hPnP hnPP
  by_cases h : P
  exact (hPnP h) h
  apply h
  apply hnPP
  exact h
  done
