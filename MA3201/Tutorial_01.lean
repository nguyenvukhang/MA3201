import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Subring.Order

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

import Mathlib.Data.Real.Pi.Irrational

import MA3201.Defs

section Intro

variable {R : Type*} [Ring R]

-- First, we note that in any ring, 1 = 0 iff the ring is trivial:
example : (0 : R) ≠ 1 ↔ Nontrivial R := ⟨(nontrivial_of_ne 0 1 ·), λ _ ↦ zero_mem_nonunits.mp not_isUnit_zero⟩

end Intro

namespace Tutorial01

namespace Q1'1

-- This is false. Consider the Ring (ℤ × ℤ):

example : Ring (ℤ × ℤ) := Prod.instRing

-- Then now consider the subring S of ℤ × ℤ, where the second element is restricted
-- to just zero. Clearly, it forms a ring:

instance S : NonUnitalSubring (ℤ × ℤ) where
  carrier   := { (n, 0) | n : ℤ}
  mul_mem'  := fun ⟨a, h⟩ ⟨b, g⟩ => h ▸ g ▸ Set.mem_setOf_eq ▸ ⟨a * b, rfl⟩
  add_mem'  := fun ⟨a, h⟩ ⟨b, g⟩ => h ▸ g ▸ Set.mem_setOf_eq ▸ ⟨a + b, rfl⟩
  zero_mem' := Set.mem_setOf_eq ▸ ⟨0, rfl⟩
  neg_mem'  := fun ⟨a, h⟩ => h ▸ Set.mem_setOf_eq ▸ ⟨-a, rfl⟩

-- So then I propose this (multiplicative) identity on S.
def ONE : S := ⟨((1 : ℤ), (0 : ℤ)), Set.mem_setOf_eq ▸ ⟨1, rfl⟩⟩

-- This proves that it is indeed the multiplicative identity of S.
example : ∀ a : S, a * ONE = a ∧ ONE * a = a := by
  intro ⟨a, z, h⟩
  subst h
  dsimp only [ONE]
  constructor
  · ext : 2
    · simp only [NonUnitalSubring.val_mul, Prod.mk_mul_mk, mul_one, mul_zero]
    · simp only [NonUnitalSubring.val_mul, Prod.mk_mul_mk, mul_one, mul_zero]
  · ext : 2
    · simp only [NonUnitalSubring.val_mul, Prod.mk_mul_mk, one_mul, mul_zero]
    · simp only [NonUnitalSubring.val_mul, Prod.mk_mul_mk, one_mul, mul_zero]

-- However, it is clearly not the multiplicative identity of ℤ × ℤ:
example : ¬∀ a : ℤ × ℤ, a * ONE = a ∧ ONE * a = a := by
  push_neg
  use (0, 1)
  intro _
  dsimp only [ONE]
  rw [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact not_eq_of_beq_eq_false rfl

end Q1'1

namespace Q1'2

-- This is false. Consider the ring of Mₙₓₙ(ℤ/2ℤ).

abbrev M₂ := Matrix (Fin 2) (Fin 2) (ZMod 2)

-- Firstly, it is clearly a finite ring. In particular, it has cardinality 2^4 = 16.
example : Ring M₂ := Matrix.instRing
example : Finite M₂ := Matrix.instFinite (ZMod 2)
example : Fintype.card M₂ = 16 := rfl

-- Next, this ring has an identity, namely [1, 0; 0, 1].
def I : M₂ := !![1, 0; 0, 1]

-- We prove here that it is, indeed, the identity of the ring.
example : ∀ A : M₂, A = A * I ∧ A = I * A := by
  dsimp only [I]
  refine fun A => ⟨?_, ?_⟩
  all_goals
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
  aesop

-- However, multiplication is not commutative:
example : ∃ A B : M₂, A * B ≠ B * A := by
  use !![0, 1; 0, 0], !![0, 0; 1, 0]
  simp
  exact not_eq_of_beq_eq_false rfl

-- Since integral domains are defined to be __commutative__ rings with no zero
-- divisors, and M₂ is shown to not be commutative, we have that M₂ is not an
-- integral domain, thus completing our counter example.

end Q1'2

namespace Q1'3

variable {R : Type*}

example [CommRing R] (s : Subring R) : CommRing s := by
  exact s.toCommRing

example [Ring R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s := by
  exact Subring.instNoZeroDivisorsSubtypeMem s

end Q1'3

namespace Q1'4

variable {R : Type*}

example [Ring R] (a : R) (h : a ≠ 0) : -a ≠ 0 := by simp_all only [ne_eq, neg_eq_zero, not_false_eq_true]
example [Ring R] (a b : R) : -a * b = -(a * b) := neg_mul a b

example [Ring R] (h : ∃ x : R, ZeroDivisor x) : ∃ a b : R, ZeroDivisor a ∧ ZeroDivisor b ∧ ¬ZeroDivisor (a + b) := by
  obtain ⟨a, ha⟩ := h
  use a, -a
  refine ⟨ha, ha.neg, ?_⟩
  rw [add_neg_cancel a, ZeroDivisor]
  simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true]

end Q1'4

namespace Q1'5

-- 2 ∈ ℤ/4ℤ is a zero divisor, but its product is zero, and hence is not a zero
-- divisor
example : 2 * 2 = (0 : ZMod 4) := rfl

end Q1'5

namespace Q1'6

-- { r + sπ : r, s ∈ ℚ } is NOT a subring of ℝ because in particular it is not
-- closed under multiplication. We shall show that π ∈ S, but π * π ∉ S. Note
-- that this requires assuming that π is transcendental over ℚ, which is a well-
-- known fact, except it's just not formalized in Lean's Mathlib yet.

open Real

-- Assumption: that π is transcendental over ℚ.
private lemma transcendental_pi : Transcendental ℚ π := sorry

def S : Set ℝ := { x | ∃ r s : ℚ, x = r + s * π }

example : π ∈ S := ⟨0, 1, by rw [Rat.cast_zero, Rat.cast_one, one_mul, zero_add]⟩

-- This together with π ∈ S shows that S is not closed under multiplication.
-- Hence it's not a subring.
example : π * π ∉ S := by
  by_contra h
  obtain ⟨r, s, h⟩ := Set.mem_setOf.mpr h
  have hr₀ : r ≠ 0 := by
    by_contra hr₀
    rw [hr₀, Rat.cast_zero, zero_add] at h
    field_simp [pi_ne_zero] at h
    exact irrational_pi.ne_rat s h
  rw [eq_comm, <-sub_eq_zero, <-sq] at h

  open Polynomial in
  have : IsAlgebraic ℚ π := by
    let p : Polynomial ℚ := C r + C s * X - X ^ 2
    refine ⟨p, ?_, ?_⟩
    · have : p.coeff 0 = r := by simp only [p, coeff_sub, coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, mul_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, sub_zero]
      have h : p.coeff 0 ≠ 0 := by
        rw [this]
        exact Rat.cast_ne_zero.mpr hr₀
      contrapose h
      push_neg at h ⊢
      exact h ▸ rfl
    · have peq : (aeval · p) = λ x : ℝ ↦ r + s * x - x ^ 2 := by
        funext x
        rw [map_sub, map_add, map_mul, map_pow]
        simp only [aeval_C, aeval_X, eq_ratCast]
      exact (congrFun peq π) ▸ h
  refine transcendental_pi this

end Q1'6

namespace Q1'7

-- False. In particular, multiplication is not commutative on this ring F, and
-- so it cannot be a field.

end Q1'7

namespace Q1'8

-- False. Consider ℚ(√2) := { r + s√2 | r, s ∈ ℚ }. Here we shall prove that it
-- is a Subfield of ℝ.

private def Q := { x : ℝ | ∃ p q : ℚ, x = p + √2 * q }

private lemma sqrt₂ : √2 * √2 = 2 := Real.mul_self_sqrt (zero_le_two)

private lemma l₀ {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : 1 / (a + √2 * b) = (a - √2 * b) / (a^2 - 2 * b^2) := by
  have h₀ : a - √2 * b ≠ 0 := by
    by_contra h'
    rw [sub_eq_zero] at h'
    have h₂ : Irrational √2 := irrational_sqrt_two
    if hb₀ : b = 0 then
      rw [hb₀, Rat.cast_zero, mul_zero, Rat.cast_eq_zero] at h'
      subst hb₀
      exact h.resolve_right (· rfl) h'
    else
    push_neg at hb₀
    have : √2 * b ≠ ↑a := (h₂.mul_ratCast hb₀).ne_rat a
    exact this h'.symm
  -- conv => lhs; rw [<-div_mul_cancel_right₀ (1 / (a + √2 * b)) h₀]
  conv => lhs; rw [<-mul_div_cancel_right₀ (1 / (a + √2 * b)) h₀, mul_div_assoc, mul_comm, mul_one_div, div_right_comm, div_div]
  refine congrArg ((a - √2 * b) / ·) ?_
  rw [right_distrib, mul_sub, mul_sub]
  have : √2 * ↑b * (√2 * ↑b) = 2 * b ^ 2 := by
    nth_rw 1 [mul_comm √2 b]
    rw [<-mul_assoc]
    rw [mul_assoc (b : ℝ) √2 √2, sqrt₂, mul_comm, <-mul_assoc, <-sq, mul_comm]
  rw [this, <-add_sub_assoc]
  refine congrArg (· - (2 * (b : ℝ) ^ 2)) ?_
  rw [<-sq, sub_add, sub_eq_self, sub_eq_zero, mul_comm]

noncomputable def Q2 : Subfield ℝ := {
  carrier := { x | ∃ (r s : ℚ), x = r + √2 * s}
  zero_mem' := by use 0, 0; simp
  one_mem' := by use 1, 0; simp
  add_mem' {a b} := by
    refine fun ⟨r₁, s₁, h₁⟩ ⟨r₂, s₂, h₂⟩ => ⟨r₁ + r₂, s₁ + s₂, ?_⟩
    simp only [Rat.cast_add, Rat.cast_mul]
    rw [left_distrib]
    rw [add_comm (√2 * s₁) (√2 * s₂), <-add_assoc, add_assoc (r₁ : ℝ) r₂ (√2 * s₂)]
    rw [<-h₂, add_assoc, add_comm b (√2 * s₁), <-add_assoc, <-h₁]
  neg_mem' {a} := by
    refine fun ⟨r, s, h⟩ => ⟨-r, -s, ?_⟩
    simp only [Rat.cast_neg]
    rw [h, neg_add, neg_mul_eq_mul_neg]
  mul_mem' {a b} := by
    refine fun ⟨r₁, s₁, h₁⟩ ⟨r₂, s₂, h₂⟩ => ⟨r₁ * r₂ + 2 * s₁ * s₂, s₁ * r₂ + r₁ * s₂, ?_⟩
    subst h₁ h₂
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    set r₁ : ℝ := ↑r₁; set s₁ : ℝ := ↑s₁; set r₂ : ℝ := ↑r₂; set s₂ : ℝ := ↑s₂
    rw [left_distrib, right_distrib, right_distrib]
    simp only [<-add_assoc, <-mul_assoc]
    rw [mul_comm r₁ √2]
    have : √2 * s₁ * √2 * s₂ = 2 * s₁ * s₂ := by rw [mul_comm √2 s₁, mul_assoc s₁ √2 √2, sqrt₂, mul_comm s₁ 2]
    rw [this, mul_assoc √2 s₁ r₂, mul_assoc √2 r₁ s₂, add_assoc (r₁ * r₂) (√2 * (s₁ * r₂)) (√2 * (r₁ * s₂)), <-left_distrib]
    exact add_right_comm (r₁ * r₂) (√2 * (s₁ * r₂ + r₁ * s₂)) (2 * s₁ * s₂)
  inv_mem' a := by
    intro ⟨r, s, h⟩
    if h₀ : a = 0 then rw [h₀, inv_zero]; use 0, 0; simp else
    have hrs₀ : r ≠ 0 ∨ s ≠ 0 := by
      by_contra h'
      push_neg at h'
      rw [h'.1, h'.2, Rat.cast_zero, mul_zero, add_zero] at h
      exact h₀ h
    rw [inv_eq_one_div a]
    let q := r^2 - 2 * s^2
    use r / q, -s / q
    simp only [Rat.cast_div, Rat.cast_neg]
    rw [h, l₀ hrs₀]
    have : q = (r : ℝ)^2 - 2 * (s : ℝ)^2 := by simp only [Rat.cast_sub, Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, q]
    rw [<-this, <-Mathlib.Tactic.RingNF.add_neg]
    rw [add_div]
    refine congrArg ((r : ℝ) / q + ·) ?_
    rw [neg_div, neg_div, mul_neg, mul_div_assoc]
}

end Q1'8

namespace Q2'a

-- An example of (R, S) where R has an identity but S does not:
-- R := ℤ, S := 2ℤ.

example : Ring ℤ := Int.instRing

example : ∃ x : ℤ, x = 1 := exists_eq

def Twoℤ : NonUnitalSubring ℤ :=  {
  carrier := { 2 * n | n : ℤ }
  zero_mem' := ⟨0, rfl⟩
  add_mem' {a b} ha hb := by
    obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; subst hx hy
    rw [<-left_distrib]
    exact ⟨x + y, rfl⟩
  neg_mem' {a} ha := by
    obtain ⟨x, hx⟩ := ha; subst hx
    rw [<-mul_neg]
    exact ⟨-x, rfl⟩
  mul_mem' {a b} ha hb := by
    obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; subst hx hy
    rw [mul_assoc]
    exact ⟨x * (2 * y), rfl⟩
}

example : 1 ∉ Twoℤ := by
  by_contra h
  obtain ⟨a, ha⟩ := h
  exact (ha ▸ Int.not_even_one) (even_two_mul a)

end Q2'a

namespace Q2'b

-- An example of (R, S) where S has an identity but R does not:
-- R := ℤ × 2ℤ, S := { (z, 0) | z ∈ ℤ }.
--
-- S's identity is (1, 0), but R has no identity because 2ℤ has no identity.

variable {R S : Type*} [Ring R] [Ring S] [Ring (R × S)]

example {r : R} {s : S}
  (hr : ∀ a : R, a * r = a ∧ r * a = a)
  (hs : ∀ a : S, a * s = a ∧ s * a = a)
  : ∀ a : R × S, a * (r, s) = a ∧ (r, s) * a = a := by
  intro (a, b)
  refine ⟨?_, ?_⟩
  · exact Prod.ext_iff.mpr ⟨(hr a).1, (hs b).1⟩
  · exact Prod.ext_iff.mpr ⟨(hr a).2, (hs b).2⟩

end Q2'b

namespace Q2'c

-- An example of (R, S) where S is commutative but R is not:
-- R := ℤ × (M₂ₓ₂(ℤ)), S := { (z, 0) | z ∈ ℤ }.
--
-- S is clearly commutative since it operates just as the ring ℤ does, which is
-- commutative. In fact, we can define a bijection that preserves ring structure
-- from ℤ to S.

-- R is not commutative since matrix operations are not commutative.

end Q2'c

namespace Q3

variable {R : Type*} [CommRing R]

namespace Twisted

private def add' (a b : R) : R := a + b - 1
private def mul' (a b : R) : R := a + b - a * b

-- We use  ⊕ᵣ and  ⊗ᵣ  because ⊕ and ⊗ have already been reserved by Lean's
-- standard library.
scoped infixl:65 " ⊕ᵣ " => Twisted.add'
scoped infixl:70 " ⊗ᵣ " => Twisted.mul'

-- This proves that 1 is the additive identity.
lemma add_identity' : ∀ a : R, a ⊕ᵣ 1 = a ∧ 1 ⊕ᵣ a = a := by
  intro a
  exact ⟨add_sub_cancel_right a 1, (@sub_eq_iff_eq_add' R _ (1 + a) 1 a).mpr rfl⟩

lemma add_inv' : ∀ a : R, ∃ b : R, a ⊕ᵣ b = 1 ∧ b ⊕ᵣ a = 1 := by
  intro a
  use 1 + 1 - a
  simp only [add']
  exact ⟨by ring_nf, by ring_nf⟩

lemma add_assoc' (a b c : R) : (a ⊕ᵣ b) ⊕ᵣ c = a ⊕ᵣ (b ⊕ᵣ c) := by simp only [add']; ring_nf

lemma add_comm' (a b : R) : a ⊕ᵣ b = b ⊕ᵣ a := by simp only [add', add_comm]

-- Thus far, we've shown that (R, ⊕, ⊗) is an abelian group in ⊕.

lemma mul_assoc' (a b c : R) : (a ⊗ᵣ b) ⊗ᵣ c = a ⊗ᵣ (b ⊗ᵣ c) := by simp only [mul']; ring_nf

example {a b c : R} : (a - b) * c = a * c - b * c := sub_mul a b c
example {a b c : R} : a - b - c = a - c - b := sub_right_comm a b c
example {a b c : R} : a - b + c = a + c - b := sub_add_eq_add_sub a b c


lemma right_distrib' (a b c : R) : (a ⊕ᵣ b) ⊗ᵣ c = a ⊗ᵣ c ⊕ᵣ b ⊗ᵣ c := by
  simp only [add', mul']
  ring_nf

lemma left_distrib'  (a b c : R) : mul' a (add' b c) = add' (mul' a b) (mul' a c) := by
  simp only [add', mul']
  ring_nf

-- Thus far, we've shown that (R, ⊕, ⊗) is a ring with identity. All that's left
-- is to show that multiplication ⊗ is commutative!

lemma mul_comm' (a b : R) : mul' a b = mul' b a := by simp only [mul']; rw [add_comm, mul_comm]

-- QED.

end Twisted

end Q3

namespace Q4

variable {K : Type*} [Field K]
  {v : Kˣ → ℤ}

example {a b : Kˣ} : (a : K) * b = ↑(a * b) := by rw [Units.val_mul]
example {a b : Kˣ} (h : (a : K) = b) : a = b := Units.eq_iff.mp h
example {a : Kˣ} : a⁻¹ = (a : K)⁻¹ := Units.val_inv_eq_inv_val a

noncomputable def ζ {K : Type*} [Field K] {x : K} (h : IsUnit x) : Kˣ :=
  let h := isUnit_iff_exists.mp h
  { val := x, inv := h.choose, val_inv := h.choose_spec.1, inv_val := h.choose_spec.2 }

structure DiscreteValuation (K : Type*) [Field K] where
  v : Kˣ → ℤ
  h₁ : ∀ a b : Kˣ, v (a * b) = v a + v b
  h₂ : Function.Surjective v
  h₃ : ∀ a b : Kˣ, (h : IsUnit (M := K) (a + b)) → min (v a) (v b) ≤ v (ζ h)

instance (K : Type*) [Field K] : CoeFun (DiscreteValuation K) (fun _ => Kˣ → ℤ) where
  coe := DiscreteValuation.v

lemma DiscreteValuation.l₁ (v : DiscreteValuation K) : v 1 = 0 :=
  let h : v 1 = v 1 + v 1 := by nth_rw 1 [<-one_mul 1]; exact v.h₁ 1 1
  left_eq_add.mp h

lemma DiscreteValuation.l₂ (v : DiscreteValuation K) : v (-1) = 0 := by
  have : (1 : Kˣ) = -1 * -1 := by rw [neg_mul_neg, mul_one]
  have : v 1 = v (-1) + v (-1) := by
    conv => lhs; rw [this]
    exact v.h₁ (-1) (-1)
  rw [l₁] at this
  exact add_self_eq_zero.mp this.symm

lemma DiscreteValuation.l₃  (v : DiscreteValuation K) (x : Kˣ) : v x⁻¹ + v x = 0 := by rw [<-h₁, inv_mul_cancel x]; exact v.l₁

-- Q4, part (a)
def DiscreteValuation.valRing (v : DiscreteValuation K) : Subring K := by

  let carrier := { y : K | (∃ x : Kˣ, 0 ≤ v x ∧ x = y) ∨ y = 0 }

  have zero_mem' : 0 ∈ carrier := Set.mem_union_right _ rfl

  have add_mem' {a b : K} (ha : a ∈ carrier) (hb : b ∈ carrier) : a + b ∈ carrier := by
    if      ha₀ : a = 0 then rw [ha₀, zero_add b]; exact hb
    else if hb₀ : b = 0 then rw [hb₀, add_zero a]; exact ha
    else if hab₀ : a + b = 0 then rw [hab₀]; exact zero_mem' else
    obtain ⟨s, hs₀, hs⟩ := ha.resolve_right ha₀
    obtain ⟨t, ht₀, ht⟩ := hb.resolve_right hb₀
    obtain ⟨x, hx⟩ := Ne.isUnit hab₀
    refine Or.inl ⟨x, ?_, hx⟩
    have hxst : x = (s : K) + t := by rw [hs, ht]; exact hx
    have hust : IsUnit ((s : K) + t) := Ne.isUnit <| by rewrite [hs, ht]; exact hab₀
    have : v x = v (ζ hust) := congrArg v <| Units.eq_iff.mp hxst
    rw [this]
    exact Int.le_trans (le_min hs₀ ht₀) (v.h₃ s t hust)

  have mul_mem' {a b : K} (ha : a ∈ carrier) (hb : b ∈ carrier) : a * b ∈ carrier := by
    if      ha₀ : a = 0 then rw [ha₀, zero_mul b]; exact zero_mem'
    else if hb₀ : b = 0 then rw [hb₀, mul_zero a]; exact zero_mem'
    else if hab₀ : a * b = 0 then rw [hab₀]; exact zero_mem' else
    obtain ⟨s, hs₀, hs⟩ := ha.resolve_right ha₀
    obtain ⟨t, ht₀, ht⟩ := hb.resolve_right hb₀
    let st := s * t
    obtain ⟨x, hx⟩ := Ne.isUnit hab₀
    refine Or.inl ⟨x, ?_, hx⟩
    have hxst : x = (s : K) * t := by rw [hs, ht]; exact hx
    have hxst : x = s * t := Units.eq_iff.mp hxst
    rw [hxst, v.h₁ s t]
    exact Int.add_nonneg hs₀ ht₀

  exact {
    carrier := carrier
    zero_mem' := zero_mem'
    one_mem' := by
      refine Or.inl ⟨1, ?_, rfl⟩
      have : v 1 = v 1 + v 1 := by nth_rw 1 [<-one_mul 1]; exact v.h₁ 1 1
      rw [left_eq_add.mp this]
    neg_mem' {a} h := by
      if h₀ : a = 0 then exact Set.mem_union_right _ <| neg_eq_zero.mpr h₀ else
      obtain ⟨c, hc₀, hca⟩ := h.resolve_right h₀
      refine Or.inl ⟨-c, ?_, by rw [<-hca]; rfl⟩
      have : -c = -1 * c := Units.eq_iff.mp (by rw [neg_one_mul])
      rw [this, v.h₁ (-1) c, l₂, zero_add]
      exact hc₀
    add_mem' := add_mem'
    mul_mem' := mul_mem'
  }
-- Q4, part (b)
example (v : DiscreteValuation K) {x : K} (h₀ : x ≠ 0) : x ∈ (v.valRing) ∨ x⁻¹ ∈ v.valRing := by
  set R := v.valRing
  refine or_iff_not_imp_left.mpr fun hni => ?_
  let ⟨a, ha⟩ := h₀.isUnit

  have ha' : a⁻¹ = x⁻¹ := by
    rw [Units.val_inv_eq_inv_val a]
    exact congrArg (·⁻¹) ha

  refine Or.inl ⟨a⁻¹, ?_, ha'⟩

  have hx₀ : v a < 0 := by
    by_contra h
    rw [<-ha] at hni
    push_neg at h
    exact hni <| Or.inl ⟨a, h, rfl⟩

  have hx₁ : v a⁻¹ + v a = 0 := v.l₃ a

  exact eq_neg_of_add_eq_zero_left hx₁ ▸ Int.neg_nonneg_of_nonpos hx₀.le

-- Q4, part (b), clarification: the "either" tends to represent mutual exclusion.
-- Turns out, we do __not__ have mutual exclusion in this case, since 1 ∈ K, but
-- both 1 ∈ R and 1⁻¹ ∈ R.
example (v : DiscreteValuation K) : ∃ x : K, x ≠ 0 ∧ (x ∈ v.valRing ∧ x⁻¹ ∈ v.valRing) := by
  set R := v.valRing
  have h₀ : (1 : K) = 1⁻¹ := one_eq_inv.mpr rfl
  have h₁ : 1 ∈ R := R.one_mem
  exact ⟨1, one_ne_zero, h₁, h₀ ▸ h₁⟩

-- Q4, part (c). When we say x ∈ R is a unit, we mean that x is a unit in R (in
-- particular, not in K).
example (v : DiscreteValuation K) {x : Kˣ} (hx : ↑x ∈ v.valRing) : v x = 0 ↔ (∃ e ∈ v.valRing, e * x = 1 ∧ x * e = 1) := by
  set R := v.valRing
  constructor
  · intro (h : v x = 0)
    use x⁻¹
    refine ⟨?_, x.inv_mul', x.mul_inv'⟩
    refine Or.inl ?_
    refine ⟨x⁻¹, ?_, Units.val_inv_eq_inv_val x⟩
    have hx₁ : v x + v x⁻¹ = 0 := v.l₃ x⁻¹
    rw [h, zero_add] at hx₁
    exact Int.le_of_eq hx₁.symm
  · intro ⟨e, he, hex, hxe⟩

    if he₀ : e = 0 then
      rw [he₀, mul_zero] at hxe
      have : ¬Nontrivial K := by
        contrapose hxe
        push_neg at hxe ⊢
        exact one_ne_zero.symm
      by_contra
      exact this (Field.instIsLocalRing K).toNontrivial
    else

    obtain ⟨a, ha, hax⟩ := hx.resolve_right x.ne_zero
    rw [Units.eq_iff.mp hax] at ha
    -- at this point, we have 0 ≤ v(x).

    have hx₀ : (x : K) ≠ 0 := x.ne_zero

    push_neg at he₀
    obtain ⟨ε, hεe⟩ := he₀.isUnit
    rw [<-hεe, <-Units.val_mul, Units.val_eq_one] at hxe hex

    -- In a division ring (or just a division monoid, the inverse is unique.
    -- So if x is a unit because ∃ e, xe = 1 = ex, then e = x⁻¹.
    have : ε = x⁻¹ := eq_inv_of_mul_eq_one_left hex
    have hεx : ε = x⁻¹ := eq_inv_of_mul_eq_one_right hxe

    have : ↑x⁻¹ ∈ R := by rw [<-hεe, hεx] at he; exact he
    obtain ⟨a', ha', ha'x⟩ := this.resolve_right x⁻¹.ne_zero
    rw [Units.eq_iff.mp ha'x] at ha'
    -- at this point, we have 0 ≤ v(x⁻¹).

    have h : v x + v x⁻¹ = 0 := by rw [<-v.l₁, <-v.h₁, mul_inv_cancel]

    rw [eq_neg_of_add_eq_zero_right h] at ha'
    have ha' : v x ≤ 0 := Int.zero_le_neg_iff.mp ha'

    exact Int.le_antisymm ha' ha
end Q4

namespace Q5
open Q4

private lemma l₀ {p : ℕ} [Fact (Nat.Prime p)] (z : ℤ) : padicValRat p (p ^ z) = z := by
  if h₀ : z ≥ 0 then
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = z := CanLift.prf z h₀
    have : padicValRat p (↑p ^ z) = padicValNat p (p ^ n) := by
      have : p ^ n = (p : ℚ) ^ (n : ℤ) := by
        subst hn
        rw [zpow_natCast]
      rw [<-hn, <-this]
      have : (p : ℚ) ^ n = ↑(p ^ n) := (Nat.cast_pow p n).symm
      rw [this]
      exact padicValRat.of_nat
    rw [this, <-hn]
    refine congrArg Nat.cast ?_
    exact padicValNat.prime_pow n
  else
  push_neg at h₀
  have : -z ≥ 0 := le_of_lt <| Int.neg_pos_of_neg h₀
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = -z := CanLift.prf (-z) this
  have : (p : ℚ) ^ z = ((p : ℚ) ^ n)⁻¹ := by
    rw [<-Int.neg_neg z, <-inv_zpow', <-hn, zpow_natCast]
    exact inv_pow (p : ℚ) n
  rw [this]
  have : -(n : ℤ) = z := by simp_all only [Int.neg_nonneg, neg_neg]
  rw [<-this]
  exact padicValRat.self_pow_inv n

-- Here, we use φ in the place of ν because ν is almost impossible to discern
-- from v in code. We shall now prove that it is a Discrete Valuation on ℚ.
def φ (p : ℕ) [Fact (Nat.Prime p)] : DiscreteValuation ℚ where
  v := λ x : ℚˣ ↦ padicValRat p x
  h₁ a b := padicValRat.mul a.ne_zero b.ne_zero
  h₂ z := by
    let pz := (p : ℚ) ^ z
    have : pz ≠ 0 := by
      refine zpow_ne_zero z ?_
      have h : p ≠ 0 := NeZero.ne p
      contrapose h
      push_neg at h ⊢
      exact Rat.natCast_eq_zero.mp h
    obtain ⟨pz, hpz⟩ : IsUnit pz := Ne.isUnit this
    use pz
    change padicValRat p ↑pz = z
    rw [hpz]
    exact (l₀ z)
  h₃ a b hab := by
    have : (a : ℚ) + b ≠ 0 := hab.ne_zero
    let ⟨ab, habibi⟩ := hab
    if h : padicValRat p a < padicValRat p b then
      refine inf_le_of_left_le ?_
      exact padicValRat.le_padicValRat_add_of_le hab.ne_zero h.le
    else
    push_neg at h
    refine inf_le_of_right_le ?_
    have : (a : ℚ) + b = b + a := Rat.add_comm a b

    have hba : IsUnit (M := ℚ) (b + a) := by rw [add_comm]; exact hab

    let ⟨ab, hab'⟩ := hab
    let ⟨ba, hba'⟩ := hba

    have habba : ab = ba := Units.eq_iff.mp <| by rw [hab', hba', add_comm]

    have : padicValRat p (ζ hab) = padicValRat p (ζ hba) := by
      subst habba
      exact congrArg (padicValRat p) this
    have : padicValRat p (ζ hab)  = padicValRat p (ζ hba) := this
    change padicValRat p b ≤ padicValRat p _
    rw [this]
    refine padicValRat.le_padicValRat_add_of_le ?_ h
    rw [add_comm]
    exact hab.ne_zero

-- At this point, we've shown that v (as defined in Q5) is a discrete valuation
-- on ℚ. It then follows immediately that we have the valuation ring. For this,
-- we use the results proven in Q4:
example : Subring ℚ := by
  have : Fact (Nat.Prime 7) := { out := Nat.prime_seven }
  exact (φ 7).valRing

-- The valuation ring R on vₚ follows immediately from Q4's results.
example {p : ℕ} [Fact (Nat.Prime p)]
  : (φ p).valRing = { y : ℚ | (∃ x : ℚˣ, 0 ≤ φ p x ∧ x = y) ∨ y = 0 } := rfl
-- In other words, { x ∈ ℚˣ | 0 ≤ vₚ(x) }
