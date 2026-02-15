/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
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

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPQ
  rw [hPQ]
  intro hQP
  rw [hQP]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  constructor
  intro hP
  rw [hPQ, hQR] at hP
  exact hP
  intro hR
  rw [hPQ, hQR]
  exact hR
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hPQ
  cases' hPQ with hP hQ
  constructor
  exact hQ
  exact hP
  intro hQP
  constructor
  cases' hQP with _ hP
  exact hP
  cases' hQP with hQ _
  exact hQ

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hPQR
  cases' hPQR with hPQ hR
  cases' hPQ with hP hQ
  constructor
  assumption
  constructor <;> assumption
  intro hPQR
  cases' hPQR with hP hQR
  cases' hQR with hQ hR
  constructor
  constructor <;> assumption
  assumption

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  assumption
  trivial
  intro hPT
  cases' hPT with hP _
  assumption

example : False ↔ P ∧ False := by
  constructor
  intro h
  constructor
  exfalso
  assumption
  assumption
  intro hPF
  cases' hPF with _ h
  assumption

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPiffQ hRiffS
  constructor
  intro hPR
  constructor
  cases' hPiffQ with hPoifQ _
  cases' hPR with hP _
  apply hPoifQ
  assumption
  cases' hRiffS with hRoifS _
  cases' hPR with _ hR
  apply hRoifS
  assumption
  intro hQS
  constructor
  cases' hPiffQ with _ hPifQ
  cases' hQS with hQ _
  apply hPifQ
  assumption
  cases' hRiffS with _ hRifS
  cases' hQS with _ hR
  apply hRifS
  assumption


example : ¬(P ↔ ¬P) := by
  intro hPiffnP
  cases' hPiffnP with hPoifnP hPifnP
  change P→P→False at hPoifnP
  apply hPoifnP
  apply hPifnP
  intro hP
  change (P→False)→P at hPifnP
  apply hPoifnP at hP
  apply hPifnP at hP
  apply hPoifnP
  assumption
  assumption
  apply hPifnP
  intro hP
  apply hPoifnP at hP
  apply hPifnP at hP
  apply hPoifnP <;> assumption
