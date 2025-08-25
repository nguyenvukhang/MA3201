import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Push

universe u

def ker {α β : Type*} [Zero β] (f : α → β) := {x | f x = 0}

/-- An integral domain is simply a commutative ring with no zero divisors. -/
class IntegralDomain (R : Type u) extends CommRing R, NoZeroDivisors R

variable {α : Type u}

section ZeroDivisorBasic

variable [Mul α] [Zero α]

-- Note that in MA3201, ZeroDivisors are also defined to be non-zero.
def ZeroDivisor (a : α) : Prop :=
  a ≠ 0 ∧ ∃ b : α, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)

lemma ZeroDivisor.not {a : α} (h : ¬ZeroDivisor a) :
  a ≠ 0 → ∀ b, b ≠ 0 → a * b ≠ 0 ∧ b * a ≠ 0 := by
  rewrite [ZeroDivisor] at h
  push_neg at h
  exact h

-- example [Ring α] : -0 = (0 : α) := neg_zero

lemma ZeroDivisor.not_of_noZeroDivisors [NoZeroDivisors α] {a : α} :
  ¬ZeroDivisor a := by
  rw [ZeroDivisor]
  push_neg at ⊢
  exact fun ha b hb => ⟨mul_ne_zero ha hb, mul_ne_zero hb ha⟩

end ZeroDivisorBasic

/-- In a Ring (possibly non-unital), the additive inverse of a zero divisor is
again a zero divisor. -/
lemma ZeroDivisor.neg [NonUnitalRing α] {a : α} (h : ZeroDivisor a) : ZeroDivisor (-a) := by
  obtain ⟨ha₀, b, hb₀, hmul⟩ := h
  refine ⟨neg_ne_zero.mpr ha₀, b, hb₀, ?_⟩
  rcases hmul with hab | hba
  · exact Or.inl (by rw [neg_mul, hab, neg_zero])
  · exact Or.inr (by rw [mul_neg, hba, neg_zero])

structure IsGroup [MulOneClass α] (s : Set α) where
  one_mem : 1 ∈ s
  inv_mem : ∀ a ∈ s, ∃ b ∈ s, a * b = 1 ∧ b * a = 1
  mul_assoc : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * b * c = a * (b * c)
  mul_close : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s

structure IsAddGroup [AddZeroClass α] (s : Set α) where
  zero_mem : 0 ∈ s
  neg_mem : ∀ a ∈ s, ∃ b ∈ s, a + b = 0 ∧ b + a = 0
  add_assoc : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + b + c = a + (b + c)
  add_mem : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s
