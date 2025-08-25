--*

-- vim:fmr=--*,-->
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.CauSeq.Basic

namespace TechScanning



-->

----------------------------------------------------------------------
-- Chapter 1: How does a proof look like in Lean?
----------------------------------------------------------------------

--* First look at a proof

example
  {a : ℝ}
  (h : a = 5) -- assume that x = 5, and call this assumption `h`.
  : a = 5     -- want to show that x = 5.
  := h        -- `h` precisely finishes the proof.



-->

--* A shorter version
-- (just with all the whitespace gone)

example {a : ℝ} (h : a = 5) : a = 5 := h



-->

--* Naming theorems for later use

-- We can name the theorems so we can use them later.

theorem add_pos (a b : ℝ) (ha : a > 0) (hb : b > 0) : a + b > 0 := sorry



-->

--* Using our own theorems

example {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c > 0 := sorry



-->

----------------------------------------------------------------------
-- Chapter 2: What makes Lean a proof *assistant* ?
----------------------------------------------------------------------

-- It can help *find* proofs:

--* Manual Proof

-- Here, `Even` is of type (ℕ → Prop). It takes in a natural number and returns
-- a Proposition (that it's even). In other words, it is telling us if the
-- number is even.
example {x y : ℕ} (hx : Even (x^2)) (hxx : Even (x^2) → Even x) (hy : y = 2)
  : y = 2 ∧ Even x := sorry



-->

--* Find proof using Lean's features (apply?):
example {x y : ℕ} (hx : Even (x^2)) (hxx : Even (x^2) → Even x) (hy : y = 2)
  : y = 2 ∧ Even x :=  sorry



-->

--* Automated Theorem Proving (aesop/simp_all):
-- (aesop = Automated Extensible Search for Obvious Proofs)
example {x y : ℕ} (hx : Even (x^2)) (hxx : Even (x^2) → Even x) (hy : y = 2)
  : y = 2 ∧ Even x := sorry



-->

--* Automated Theorem Proving (grind):
-- This example was shown on their website @ https://lean-lang.org/
example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y  →
    7*x - 9*y > 4 := by grind



-->

--* It can smartly apply theorems.
-- Often, we *rewrite* the goal of the proof to a simpler form to help us along
-- Lean helps with that.
example {n : ℕ} : n * (n + 2) ≤ (n + 1) ^ 2 := by

  -- `pow_two` is from MathLib.
  -- It claims (and proves) that a ^ 2 = a * a.
  -- Lean will smartly try to use it to rewrite current goal.
  rw [pow_two]

  -- expand the RHS.
  rw [add_one_mul] -- (a + 1) * b = a * b + b
  rw [mul_add_one] -- a * (b + 1) = a * b + a
  rw [<-add_assoc] -- a + b + c = a + (b + c)
                   -- Notice the lack of brackets in the LHS. This is because
                   -- in code, operations are always left-associative.

  -- expand the LHS.
  rw [mul_add]     -- a * (b + c) = a * b + a * c
  rw [mul_two]     -- n * 2 = n + n
  rw [<-add_assoc] -- a + b + c = a + (b + c)

  -- try `apply?`
  -- try `simp?`
  -- try `simp`
  sorry



-->

----------------------------------------------------------------------
-- Chapter 3: Expressing more complex arguments
----------------------------------------------------------------------

-- Lean allows for lots of ways to go about proving things.
-- For every proof I can write in English, there is a way to write it in Lean.

--* Example (1 of 3): Without Loss of Generality
example {a : ℝ} (ha : a ≥ 0) (hε : ∀ ε > 0, a < ε) : a = 0 := by
  -- Without Loss of Generality, assume that a > 0.
  wlog h : a > 0
    -- But first, we have to show that if ¬a > 0, the proof works.
  · exact (ha.eq_of_not_lt h).symm

  -- Now, we can move on, assuming that `h : a > 0`. We shall prove by contradiction.
  by_contra

  -- Since 0 < a, we can substitute `a` into `hε` above.
  specialize hε a h

  -- Now, `hε` states that `a < a`, and that is the contradiction we need.
  exact hε.false



-->

--* Example (1 of 3): Splitting cases with `if`
example {a : ℝ} (ha : a ≥ 0) (hε : ∀ ε > 0, a < ε) : a = 0 := by
  if h : a = 0 then
  · exact h
  else
  · by_contra
    push_neg at h
    have hpos : a > 0 := ha.lt_of_ne h.symm
    specialize hε a hpos
    exact hε.false



-->

--* Example (1 of 3): Splitting cases with `cases`
example {a : ℝ} (ha : a ≥ 0) (hε : ∀ ε > 0, a < ε) : a = 0 := by
  cases lt_or_eq_of_le ha with
  | inr heq => exact heq.symm
  | inl hlt =>
  by_contra
  specialize hε a hlt
  exact hε.false



-->

--* Example (2 of 3): `suffices` ...
example {n : ℕ} (hn : Even n) : Even (3 * n ^ 2) := by
  -- It suffices to show that `n ^ 2` is Even. That's because any number times
  -- and even number is still even. We _can_ express this too!

  suffices h : Even (n ^ 2) by
    -- Here, we have to show _why_ it is sufficient that `n ^ 2` is Even, by
    -- completing the proof with the assumption that `n ^ 2` is Even first.
    sorry

  -- Out here, since we've already declare that it suffices to show that `n ^ 2`
  -- is Even, we do just that. Show that `n ^ 2` is Even.

  sorry



-->

--* Example (3 of 3): `obtain` for ∃ statements.
example
  -- Amazing and Brilliant are statements that depend on some natural number.
  {Amazing Brilliant : ℕ → Prop}

  -- There exists (∃) a integer K such that for all (∀) n ≥ K,
  -- we have that `Amazing n` is true (or simply, that n is Amazing).
  --
  -- Take for example that 6 is a possible value for K. Then
  -- 6, 7, 8, ... are all Amazing. We make no promises on
  -- the Amazingness of 1, 2, ..., 5.
  --
  -- But we don't know if K = 6 or not. We just know that such a K exists.
  (hA : ∃ K, ∀ n ≥ K, Amazing n)

  -- Same with Q.
  (hB : ∃ K, ∀ n ≥ K, Brilliant n)

  -- Want to show: There exists some integer K such that for all n ≥ K, both
  -- `P n` and `Q n` are true.
  : ∃ K, ∀ n ≥ K, Amazing n ∧ Brilliant n := by

  -- Intuitive solution: Set K to be the max of the two.
  --      1  2  3  4  5  6  7  8  9  ...
  --                  | -> onwards all Amazing
  --                           | -> onwards all Brilliant
  --
  --                           ↑ use this as our K.

  obtain ⟨K₁, hK₁ : ∀ n ≥ K₁, Amazing n⟩ := hA
  obtain ⟨K₂, hK₂ : ∀ n ≥ K₂, Brilliant n⟩ := hB
  let K := max K₁ K₂

  use K

  intro n hn

  have hnK₁ : n ≥ K₁ := by exact le_of_max_le_left hn
  have hnK₂ : n ≥ K₂ := by exact le_of_max_le_right hn

  have hA' : Amazing n := hK₁ n hnK₁
  have hB' : Brilliant n := hK₂ n hnK₂
  exact ⟨hA', hB'⟩



-->

--* Example (3 of 3): try using `apply?` on the same example
example
  {Amazing Brilliant : ℕ → Prop}
  (hA : ∃ K, ∀ n ≥ K, Amazing n)
  (hB : ∃ K, ∀ n ≥ K, Brilliant n)
  : ∃ K, ∀ n ≥ K, Amazing n ∧ Brilliant n := by
  sorry



-->
