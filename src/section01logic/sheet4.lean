/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro pq, exact pq.left,
end

example : P ∧ Q → Q :=
begin
  simp,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  simp,
end

example : P → Q → P ∧ Q :=
begin
  intro p, intro q,
  split, exact p, exact q,
  
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro pq, split, exact pq.right, exact pq.left,
end

example : P → P ∧ true :=
begin
  simp,
end

example : false → P ∧ false :=
begin
  simp,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intro pq, intro qr, split, exact pq.left, exact qr.right,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro pqr, intro p, intro q, 
  apply pqr, split, exact p, exact q,
end



