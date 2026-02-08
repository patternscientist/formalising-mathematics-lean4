/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

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
  intro hnT
  apply hnT
  triv
  done

example : False → ¬True := by
  intro hF
  change True → False
  intro _
  exact hF
  done

example : ¬False → True := by --- This one was the trickest! A non-constructive proof...
  intro _
  triv
  done

/- I didn't see the simple solution and instead got stuck, moved on, circled back, and then
  came up with the following unnecessarily-complicated alternative solution before realizing obvious:

example : ¬False → True := by --- This one was the trickest! A non-constructive proof...
  intro hnF
  by_contra hnT --- using by_contra...
  by_cases hF : False --- and by_cases!
  exact hnF hF
  apply hnT
  triv
  done
-/
example : True → ¬False := by
  intro _
  change False → False
  intro hF
  exact hF
  done

example : False → ¬P := by
  intro hF _
  exact hF
  done

example : P → ¬P → False := by
  intro hP hnP
  exact hnP hP
  done

example : P → ¬¬P := by
  intro hP hPF
  exact hPF hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  change P → False
  intro hP
  exact hnQ (hPQ hP)
  done

example : ¬¬False → False := by
  intro hnnF
  apply hnnF
  intro hF
  exact hF
  done

example : ¬¬P → P := by
  intro hnnP
  by_cases h : P --- this proof is non-constructive!
  exact h
  exfalso
  exact hnnP h
  done

example : (¬Q → ¬P) → P → Q := by
  intro hnQnP hP
  by_cases h : Q --- this proof is also non-constructive
  exact h
  exfalso
  exact (hnQnP h) hP
  done
