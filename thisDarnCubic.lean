import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GroupPower.Lemmas

lemma dvd_coprime_implies_natAbs_one (a b : ℤ) (h : a ∣ b) (h2 : (Int.gcd a b) = 1) : Int.natAbs a = 1 := by
  have beq1xb : b = b * 1:= by simp
  rw [beq1xb] at h
  -- show a | 1
  have tempname := (Int.dvd_of_dvd_mul_right_of_gcd_one h h2)
  rw [← Int.natAbs_dvd_natAbs] at tempname
  simp at tempname
  exact tempname

theorem x3x1norat : ¬ ∃ (x : ℚ), x*x * x + x + 1=0 := by
  simp
  intro x
  apply @Classical.by_contradiction
  simp
  rw [Rat.add_def,Rat.add_def]
  simp
  rw [Rat.mul_def, Rat.mul_def]
  unfold Rat.normalize
  simp
  have gcd1 : Nat.gcd (Int.natAbs (x.num * x.num)) (x.den * x.den) = 1 := by
    have h1 := x.reduced
    have h2 := Nat.coprime.pow 2 2 h1
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ] at h2
    simp at h2
    rw [← Int.natAbs_mul] at h2
    apply h2
  have gcd2 : Nat.gcd (Int.natAbs (x.num * x.num * x.num)) (x.den * x.den * x.den) = 1 := by
    have h1 := x.reduced
    have h2 := Nat.coprime.pow 3 3 h1
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ] at h2
    simp at h2
    rw [← Int.natAbs_mul, ← Int.natAbs_mul] at h2
    apply h2
  
  rw [gcd1]
  simp
  rw [gcd2]
  simp
  have dnz := x.den_nz
  have asdf: Nat.gcd (Int.natAbs (x.num * x.num * x.num * ↑x.den + x.num * (↑x.den * ↑x.den * ↑x.den))) (x.den * x.den * x.den * x.den) = x.den := by
    rw [← mul_assoc, ← Int.add_mul]
    rw [Int.natAbs_mul]
    simp
    rw [Nat.gcd_mul_right]
    conv => 
      rhs
      rw [← (one_mul x.den)]
    rw [mul_right_cancel_iff_of_pos (Nat.pos_of_ne_zero dnz)]
    rw [← Nat.coprime]
    rw [mul_comm]
    rw [← mul_add]
    rw [Int.natAbs_mul]
    rw [Nat.coprime_mul_iff_left]
    apply And.intro
    . ring
      apply Nat.coprime.pow_right 3 x.reduced
    have num2nneg : 0 ≤ x.num * x.num := by
      ring
      apply sq_nonneg
    have den2nneg : (0:ℤ)  ≤ ↑x.den * ↑x.den := by
      ring
      apply sq_nonneg
    rw [Int.natAbs_add_nonneg num2nneg den2nneg]
    rw [Int.natAbs_mul, Int.natAbs_mul]
    conv => rhs ; ring
    apply Nat.coprime.pow_right 3
    simp
    ring
    apply Nat.coprime.pow_left 2 x.reduced
  rw [asdf]
  simp
  have dnz2 : (↑x.den ≠ (0:ℤ)) := by
    contrapose dnz
    simp at dnz
    simp
    apply dnz
  rw [Int.mul_ediv_cancel (↑x.den * ↑x.den * ↑x.den) dnz2]
  rw [← Int.mul_assoc,← Int.add_mul,Int.mul_div_cancel]
  simp
  intro num
  
  have dendvdnum3: ((↑x.den) ∣ (x.num * x.num * x.num)) := by
    have bla : ((↑x.den) ∣ (0: ℤ)) := by simp
    rw [← num] at bla
    rw [Int.add_assoc] at bla  
    rw [Int.dvd_iff_dvd_of_dvd_add bla]
    rw [←Int.mul_assoc, ←Int.add_mul]
    apply Int.dvd_mul_left
  have numdvdden3: ((x.num) ∣ (↑x.den * ↑x.den * ↑x.den)) := by
    have bla : ((x.num) ∣ (0 : ℤ)) := by simp
    rw [← num] at bla
    rw [Int.mul_assoc, ←Int.mul_add] at bla
    rw [← Int.dvd_iff_dvd_of_dvd_add bla]
    apply Int.dvd_mul_right
  
  have bado := x.reduced
  conv at dendvdnum3 => ring
  conv at numdvdden3 => ring
  have numden3gcd1 : Int.gcd x.num ((x.den : ℤ)^3) = 1:= by
    rw [Int.gcd_eq_natAbs, Int.natAbs_pow]
    simp
    apply bado
  have numNatAbseq1 := dvd_coprime_implies_natAbs_one x.num ((x.den : ℤ)^3) numdvdden3 numden3gcd1
  have dennum3gcd1 : Int.gcd (x.den:ℤ) (x.num^3) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_pow]
    simp
    rw [Nat.coprime_comm]
    apply bado 
  have deneq1 := dvd_coprime_implies_natAbs_one (x.den:ℤ) (x.num^3) dendvdnum3 dennum3gcd1
  simp at deneq1
  rw [deneq1] at num
  let l := x.num
  have leqxnum : l = x.num := by simp
  rw [← leqxnum] at numNatAbseq1
  rw [← leqxnum] at num
  match l with
  | Int.ofNat m => 
    simp at numNatAbseq1
    rw [numNatAbseq1] at num
    simp at num
  | Int.negSucc m => 
    simp at numNatAbseq1
    rw [numNatAbseq1] at num
    simp at num
  . apply dnz2
