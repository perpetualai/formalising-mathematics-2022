/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro p, left, exact p,
end

example : Q → P ∨ Q :=
begin
  intro q, right, exact q,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro pq, intro pr, intro qr, 
  cases pq with p q, 
    apply pr, exact p,
    apply qr, exact q,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro pq, cases pq with p q,
    right, exact p,
    left, exact q,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
    intro pqr,  cases pqr with pq  r,
      cases pq with p q, left, exact p, right,left,exact q,
      right, right,exact r,
    intro pqr, rcases pqr with ( p | q | r),
      left, left, exact p, 
      left, right, exact q, 
      right, exact r,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intro pr, intro qs, intro pq, cases pq with p q,
    left, apply pr, exact p,
    right, apply qs, exact q, 
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intro pq, intro pr, cases pr with p r, 
    left, apply pq, exact p, 
    right, exact r,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intro pr, intro qs, split, 
    intro pq, cases pq with p q, 
      left, rw ←pr, exact p,
      right, rw ←qs, exact q,
    intro rs, cases rs with r s, 
      left, rw pr, exact r, 
      right, rw qs, exact s, 
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split, 
    intro npq, split, 
      intro p, apply npq, left, exact p,
      intro q, apply npq, right, exact q,
    intro nqp, intro pq, rcases nqp with ⟨np, nq⟩,  cases pq with p q,
      apply np, exact p,
      apply nq, exact q,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
    show ¬P ∨ ¬Q → ¬(P ∧ Q),
      intro npq, intro pq, cases npq with np nq,
        apply np, exact pq.left,
        apply nq, exact pq.right,
    show ¬(P ∧ Q) → ¬P ∨ ¬Q,
      intro npq, by_cases p : P,
        right, intro q, apply npq, split, exact p, exact q,
        left, exact p,
end
