/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  simp,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro pq, 
  rw pq,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split; {
  intro pq, rw pq,
  }
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro pq, intro qr, rw pq,exact qr,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split; {
    intro pq,
    split, exact pq.right, exact pq.left,
  }
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
    intro pqr, split, 
      exact pqr.left.left, 
      split, exact pqr.left.right, exact pqr.right,
    intro pqr, split,
      split, exact pqr.left, exact pqr.right.left, exact pqr.right.right,
end

example : P ↔ (P ∧ true) :=
begin
  simp,
end

example : false ↔ (P ∧ false) :=
begin
  simp,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro pq, intro rs, split; {
    intro pr, split, 
      rw ← pq, exact pr.left,
      rw ← rs, exact pr.right,
  }
end

example : ¬ (P ↔ ¬ P) :=
begin
  simp,
end
