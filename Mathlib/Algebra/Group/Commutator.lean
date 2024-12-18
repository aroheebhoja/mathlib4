/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Bracket
import Mathlib.Algebra.Group.Basic
-- import Mathlib.Algebra.Group.Conj

/-!
# The bracket on a group given by commutator.
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

/-- The commutator of two elements `g₁` and `g₂`. -/
instance commutatorElement {G : Type*} [Group G] : Bracket G G :=
  ⟨fun g₁ g₂ ↦ g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

theorem commutatorElement_def {G : Type*} [Group G] (g₁ g₂ : G) :
    ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl

example {G : Type*} [Group G] (g₁ g₂ : G) : g₁ * g₂ * g₁⁻¹ = ⁅g₁, g₂⁆ * g₂ := by
  rw [commutatorElement_def, inv_mul_cancel_right]

example {G : Type*} [Group G] (g₁ g₂ : G) : ⁅g₂, g₁⁆ = ⁅g₁, g₂⁆⁻¹ := by
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

example {G : Type*} [Group G] (g₁ g₂ g₃ : G) :
  ⁅g₁, g₂ * g₃⁆ = ⁅g₁, g₂⁆ * (g₂ * ⁅g₁, g₃⁆ * g₂⁻¹) := by
  simp only [commutatorElement_def, ← mul_assoc]
  rw [inv_mul_cancel_right, inv_mul_cancel_right]
  rw [mul_inv_rev, ← mul_assoc]

example {G : Type*} [Group G] (g₁ g₂ g₃ : G) :
  ⁅g₃ * g₁, g₂⁆ = g₃ * ⁅g₁, g₂⁆ * g₃⁻¹ * ⁅g₃, g₂⁆ := by
  simp only [commutatorElement_def, ← mul_assoc]
  rw [inv_mul_cancel_right, inv_mul_cancel_right]
  rw [mul_inv_rev, ← mul_assoc]

example {G : Type*} [Group G] (g₁ g₂ : G) : ⁅g₁, g₂⁻¹⁆ = g₂⁻¹ * ⁅g₂, g₁⁆ * g₂ := by
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, ← mul_assoc]
  simp only [inv_mul_cancel, one_mul]

example {G : Type*} [Group G] (g₁ g₂ : G) : ⁅g₁⁻¹, g₂⁆ = g₁⁻¹ * ⁅g₂, g₁⁆ * g₁ := by
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, ← mul_assoc]
  rw [inv_mul_cancel_right]
