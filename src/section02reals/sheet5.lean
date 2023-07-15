/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tendsto` from a previous sheet
import algebra.group.basic

-- you can maybe do this one now
theorem tendsto_neg {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  rw tendsto at *,
  intros ep epc, specialize ha ep epc,
  cases ha with b lmt, use b,
  intros vn vnc, specialize lmt vn vnc,
  have ns: ∀ u v : ℝ , - u - (-v) = -(u - v), norm_num,
  rw ns, 
  have absn: ∀ w : ℝ , | -w|=|w|, exact abs_neg,
  rw absn,exact lmt,
end

/-
`tendsto_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful. 
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsto_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  rw tendsto at *,
  intros ep epc,
  have epch: ep/2 > 0, linarith,
  specialize ha (ep/2) epch, specialize hb (ep/2) epch,
  cases ha with ba la, cases hb with bb lb,
  use max ba bb,
  intros vn vnc,
  have ban : ba ≤ vn, exact le_of_max_le_left vnc,
  have bbn : bb ≤ vn, exact le_of_max_le_right vnc,
  specialize la vn ban, specialize lb vn bbn,
  have asq: ∀ w x y z:ℝ , w+x-(y+z) = (w-y)+(x-z), exact add_sub_comm,
  rw asq,
  --have trig : ∀ p q:ℝ , | p + q | ≤ |p|+|q|, exact abs_add,
  have trig2: |a vn - t + (b vn - u)| ≤ |a vn - t| + |b vn - u|, apply abs_add,
  linarith,
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n - b n) (t - u) :=
begin
  rw tendsto at *,
  intros ep epc,
  have epch: ep/2 > 0, linarith,
  specialize ha (ep/2) epch, specialize hb (ep/2) epch,
  cases ha with ba la, cases hb with bb lb,
  use max ba bb,
  intros vn vnc,
  have ban : ba ≤ vn, exact le_of_max_le_left vnc,
  have bbn : bb ≤ vn, exact le_of_max_le_right vnc,
  specialize la vn ban, specialize lb vn bbn,
  have asq: ∀ w x y z:ℝ , w-x-(y-z) = (w-y)-(x-z), ring_nf, norm_num,
  rw asq, 
  --have trig : ∀ p q:ℝ , | p - q | ≤ |p|+|q|, exact abs_sub,
  have trig2: |a vn - t - (b vn - u)| ≤ |a vn - t| + |b vn - u|, apply abs_sub,
  linarith,
end

