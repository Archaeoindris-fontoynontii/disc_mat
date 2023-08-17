import Mathlib.Data.Nat.Basic
import Mathlib.Init.Function
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
import Mathlib.Algebra.Associated
import Mathlib.Data.Polynomial.FieldDivision

import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Zmod.Parity
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

import Mathlib.Analysis.SpecialFunctions.Pow.Real

def hello := "world"



theorem mododdPlusOddisEven (n m : ℕ) (hn : n%2 = 1) (hm : m%2 = 1) : (n+m) % 2 = 0 := by
  rw [Nat.add_mod]
  rw [hn, hm]
  simp -- (1+1) %2 = 0

theorem oddPlusOddisEven (n m : ℕ) (hn : Odd n) (hm : Odd m) : Even (n+m) := by
  rw [Odd] at hn
  rw [Odd] at hm
  rw [Even] 
  let ⟨k1,hk1⟩ := hn 
  let ⟨k2,hk2⟩ := hm
  apply Exists.intro (k1+k2+1)
  rw [hk1, hk2]
  ring
  
theorem oddPlusOddisEven2 (n m : ℕ) (hn : Odd n) (hm : Odd m) : Even (n+m) := by
  rw [Odd] at hn
  rw [Odd] at hm
  rw [Even] 
  match hn with
  | Exists.intro k1 hk1 =>
    match hm with
    | ⟨k2,hk2⟩ =>
      apply Exists.intro (k1+k2+1)
      rw [hk1, hk2]
      ring

theorem fourDvdEvenSquared (n : ℕ) (hn : Even n) : 4 ∣ n*n := by
  rw [Even] at hn
  let ⟨r, hr⟩ := hn
  rw [hr]
  ring_nf
  apply Nat.dvd_mul_left

-- For integer \(n\text{,}\) if \(n^3 + 5\) is odd, then \(n\) is even
theorem oddCubedPlusFiveisEven (n : ℕ) (hn : Odd (n*n*n + 5)) : Even n := by
  apply by_contradiction
  rw [← Nat.odd_iff_not_even]
  intro H
  have n3o : (Odd (n*n*n)) := by
    have n2o := Nat.odd_mul.mpr (And.intro H H)
    rw [Nat.odd_mul]
    apply And.intro n2o H
  have odd5 : Odd 5 := by simp
  have hnNot : Even (n*n*n + 5) := oddPlusOddisEven (n*n*n) 5 n3o odd5
  rw [Nat.even_iff_not_odd] at hnNot
  contradiction
  



theorem noSmallestPosQ (q : ℚ) (h : q > 0) : ∃ (r : ℚ), r > 0 ∧ r < q := by
  have h2 : q/2 > 0 := by
    apply div_pos h
    simp
  apply Exists.intro (q/2)
  apply And.intro
  apply h2
  apply div_lt_self h
  simp

theorem mulsFour (z : ℤ) : ∃ (n : ℕ), z*4 = 1 + ((-1)^n)*(2*n - 1) := by
  cases z with 
  | ofNat m => 
    have goal : ((∃ (n : ℕ), Int.ofNat m * 4 = 1 + (-1) ^ n * (2 * ↑n - 1) ∧ (Even n))) := by
      induction m with
      | zero => 
        apply Exists.intro 0
        simp
      | succ m ih =>
        let ⟨i, hi⟩ := ih
        apply Exists.intro (i+2)
        rw [Nat.even_add]
        simp
        apply And.intro
        rw [pow_add]
        simp
        rw [mul_add]
        rw [sub_eq_add_neg]
        rw [add_assoc]
        rw [add_comm (2*2)]
        rw [← add_assoc]
        rw [mul_add]
        rw [mul_comm]
        rw [mul_add]
        rw [mul_comm]
        rw [← sub_eq_add_neg]
        rw [← add_assoc]
        rw [← hi.left]
        have n1powi : ((-(1 : ℤ)) ^ i = 1) := by
          rw [neg_one_pow_eq_one_iff_even]
          apply hi.right
          simp
        rw [n1powi]
        simp
        
        apply hi.right
    let ⟨n,goal2⟩ := goal
    apply Exists.intro n
    apply goal2.left 
  | negSucc m =>
    have goal : ((∃ (n : ℕ), (Int.negSucc m) * 4 = 1 + (-1) ^ n * (2 * ↑n - 1) ∧ (Odd n))) := by
      induction m with
      | zero => 
        apply Exists.intro 3
        simp
      | succ m ih =>
        let ⟨i, hi⟩ := ih
        apply Exists.intro (i+2)
        simp
        apply And.intro
        rw [pow_add]
        simp
        rw [mul_add]
        rw [sub_eq_add_neg]
        rw [add_assoc]
        rw [add_comm (2*2)]
        rw [← add_assoc]
        rw [mul_add]
        rw [mul_comm]
        rw [← sub_eq_add_neg]
        rw [← add_assoc]
        rw [← hi.left]
        have n1powi : ((-(1 : ℤ)) ^ i = -1) := by
          apply Odd.neg_one_pow
          apply hi.right
        rw [n1powi]
        simp
        rw [Int.negSucc_coe]
        rw [Int.negSucc_coe]
        simp
        ring
        
        -- odd goal

        rw [Nat.even_add]
        simp
        rw [← Nat.odd_iff_not_even]
        apply hi.right
    let ⟨n,goal2⟩ := goal
    apply Exists.intro n
    apply goal2.left

theorem rationalPlusIrrationalIsIrrational (q : ℚ) (r : ℝ) (h2 : Irrational r) : Irrational (q + r) := by 
  contrapose h2
  unfold Irrational
  simp
  unfold Irrational at h2
  simp at h2
  let ⟨y, hy⟩ := h2
  use y-q
  simp
  rw [hy] 
  simp

theorem problemI : {k : ℤ | k % (6:ℤ) = 3} ⊆ {m : ℤ | m % 3 = 0} := by
  simp
  intro a
  have h3eq3mod6 : (3:ℤ) = 3 % (6:ℤ) := by
    simp
  rw [h3eq3mod6]
  rw [← Int.ModEq]
  rw [Int.modEq_iff_add_fac]
  simp
  rw [← h3eq3mod6]
  intros x h
  use -2*x+1
  ring
  rw [h]
  ring
  
theorem pascalsFormula (n : ℕ) (k : ℕ) : (n.choose k) + (n.choose (k+1)) = ((n+1).choose (k+1)) := by
  rfl

theorem existsIrrPowIrrEqRat : ∃ (a b : ℝ), (Irrational a ∧ Irrational b ) ∧ (¬Irrational (a^b)):= by
  have irrOrNotIrrSqrt2powSqrt2 := em (Irrational (Real.sqrt 2 ^ Real.sqrt 2))
  cases irrOrNotIrrSqrt2powSqrt2 with
  | inl isIrr => 
    apply Exists.intro (Real.sqrt 2 ^ Real.sqrt 2)
    apply Exists.intro (Real.sqrt 2)
    apply And.intro
    apply And.intro
    apply isIrr
    apply irrational_sqrt_two
    rw [← Real.rpow_mul (Real.sqrt_nonneg 2)]
    rw [Real.mul_self_sqrt zero_le_two]
    rw [Real.rpow_two]
    rw [Real.sq_sqrt zero_le_two]
    rw [irrational_iff_ne_rational]
    push_neg
    apply Exists.intro 2
    apply Exists.intro 1
    rw [Int.int_cast_ofNat, Int.cast_one, div_one]
  | inr isRat =>
    apply Exists.intro (Real.sqrt 2)
    apply Exists.intro (Real.sqrt 2)
    rw [and_self]
    apply And.intro
    apply irrational_sqrt_two
    apply isRat

theorem impliesProof (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  rw [Imp.swap]
  rw [imp_not_comm]
  rw [not_not]
  exact h