import Mathlib.RingTheory.QuotientNoetherian
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic


open Classical

open BigOperators Polynomial

universe u v w

-- variable {R : Type u} [CommRing R]

open Ideal DoubleQuot Polynomial
/--
theorem complicatedFromGauss (I : Ideal R) (f : R[X])  (proof1 : ¬ ∃ (g h : (R ⧸ I)[X]), g * h = Polynomial.map (Ideal.Quotient.mk I) f) : Irreducible f := by 
  contrapose proof1
  simp
  simp at proof1

  sorry
--Polynomial.Monic.irreducible_of_irreducible_map
--/
-- x^3 + x + 1 has no rational roots
noncomputable def f : ℤ[X] := Polynomial.X ^ 3 + Polynomial.X + 1



variable (φ := Int.castRingHom (ZMod 2))
theorem thisPolyNoRatRoots [CommSemiring ℤ]: ¬ ∃ (x : ℚ),  (f.map (Int.castRingHom ℚ)).eval x = 0 := by
  -- have fprim : f.IsPrimitive := by 
  --   simp
  let phi := Int.castRingHom (ZMod 2)
  apply @Classical.by_contradiction
  simp
  intro x
  rw [← Polynomial.IsRoot.def]
  rw [← Polynomial.dvd_iff_isRoot]
  rw [dvd_iff_exists_eq_mul_left]
  have fIrr : Irreducible f := by
    have _ : IsDomain (ZMod 2) := by 
      apply ZMod.instIsDomainZModToSemiringToDivisionSemiringToSemifieldInstFieldZMod 2
    
    apply (Polynomial.Monic.irreducible_of_irreducible_map phi)
    unfold Monic
    unfold Polynomial.leadingCoeff
    have deg3 : natDegree f = 3 := by 
      sorry
    sorry
    unfold f
    simp
    apply Irreducible.mk
    rw [Polynomial.Monic.isUnit_iff]
    simp
    have fac1 : ((Polynomial.X :(ZMod 2)[X]) ^ 3 + X) = (X ^ 2 + 1)*X := by
      ring
    rw [fac1]
    simp
    rw [not_or]
    apply And.intro
    
    . 
      apply Polynomial.X_pow_add_C_ne_zero
      simp
    . apply Polynomial.X_ne_zero
    
    . sorry
    
    . 
      intros a b h
      have tempname : natDegree (a) + natDegree (b) = 3 := by
        rw [← Polynomial.natDegree_mul]
        rw [← h]
        have fz2deg3 : natDegree ((X : (ZMod 2)[X])^3 + X + 1) = 3 := by
          sorry
        apply fz2deg3
        intro lies
        rw [lies] at h
        simp at h
        have fac1 : ((Polynomial.X :(ZMod 2)[X]) ^ 3 + X) = (X ^ 2 + 1)*X := by
          ring
        rw [fac1] at h
        have something : 0 = (1 :((ZMod 2)[X])) + 1 := by
          ring
          apply Eq.symm
          simp
          sorry
          -- rw [Polynomial.C_eq_zero]
          -- rw [ZMod.eq_iff_modEq_nat]
          -- rw [ZMod.eq_zero_iff_even]
        sorry
        sorry
      sorry
    
  --have deg3 : Polynomial. (Polynomial.map (Int.castRingHom ℚ f))
  --rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  sorry
--Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast


-- theorem PigeonholeNatOrds (n : Nat) : ∀ f: ({m : ℕ // m ≤ Nat.succ n} -> {m : ℕ // m < Nat.succ n}), ¬ Function.Injective f := by
--   unfold Function.Injective
--   simp
--   induction n with
--   | zero =>
--     intros f
--     apply Exists.intro 0
--     simp
--     apply Exists.intro 1
--     simp
--     have olt1 : 0 < 1 := by
--       apply Nat.zero_lt_one
--     have olteq1 : 0 ≤ Nat.succ Nat.zero := by
--       apply Nat.zero_le
--     have lhs : f { val := 0, property := olteq1} = ⟨0, olt1⟩ := by
--       simp
--       have j := Subtype.property (f { val := 0, property := olteq1})
--       simp at j
--       conv at j => 
--         rhs 
--         rw [← Nat.one_eq_succ_zero]
      
--       rw [Nat.lt_one_iff] at j
--       apply Subtype.eq
--       apply j
      
--     have rhs : f { val := 1, property := Nat.succ_pos Nat.zero} = ⟨0, olt1⟩ := by
--       simp
--       have j := Subtype.property (f { val := 1, property := Nat.succ_pos Nat.zero})
--       simp at j
--       conv at j => 
--         rhs 
--         rw [← Nat.one_eq_succ_zero]
--       rw [Nat.lt_one_iff] at j
--       apply Subtype.eq
--       apply j
--     rw [lhs, rhs]

--   | succ n ih =>
--     intro f
--     apply by_contradiction
--     simp
--     intro x
--     sorry 