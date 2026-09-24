import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Data.Nat.Cast.Field

open Filter

/-!
# Exercise 73

Semantic formalization of `proof_gap/exercise_73/{1,...,12}.txt`.
-/

namespace ProofGap.Exercise73

noncomputable section

def omega (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), 1 / (Nat.factorial j : ℝ)

def RatRep (e : ℝ) (m : ℤ) (n : ℕ) : Prop :=
  0 < n ∧ e = (m : ℝ) / (n : ℝ)

def IsInteger (x : ℝ) : Prop :=
  ∃ z : ℤ, x = (z : ℝ)

def RemainderData (e : ℝ) (θ : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    e = omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ)) ∧
    0 < θ n ∧ θ n < 1

/-- Source: `proof_gap/exercise_73/1.txt`; the factorial sum and denominator data are explicit. -/
theorem gap1
    (e : ℝ) (m : ℤ) (n : ℕ)
    (hrat : RatRep e m n)
    (hremainder : ∃ θ : ℕ → ℝ, RemainderData e θ) :
    ∃ θ : ℕ → ℝ,
      (m : ℝ) / (n : ℝ) =
        omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ)) := by
  rcases hrat with ⟨hn, he⟩
  rcases hremainder with ⟨θ, hθ⟩
  exact ⟨θ, he.symm.trans (hθ n hn).1⟩

/-- Source: `proof_gap/exercise_73/2.txt`; use the same remainder witness. -/
theorem gap2
    (e : ℝ) (θ : ℕ → ℝ)
    (hθ : RemainderData e θ) :
    ∀ n : ℕ, 0 < n → 0 < θ n := by
  intro n hn
  exact (hθ n hn).2.1

/-- Source: `proof_gap/exercise_73/3.txt`; use the same remainder witness. -/
theorem gap3
    (e : ℝ) (θ : ℕ → ℝ)
    (hθ : RemainderData e θ) :
    ∀ n : ℕ, 0 < n → θ n < 1 := by
  intro n hn
  exact (hθ n hn).2.2

/-- Source: `proof_gap/exercise_73/4.txt`. -/
theorem gap4
    (m : ℤ) (n : ℕ) (θ : ℕ → ℝ)
    (hn : 0 < n)
    (hid :
      (m : ℝ) / (n : ℝ) =
        omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ))) :
    (Nat.factorial n : ℝ) * ((m : ℝ) / (n : ℝ)) =
    (Nat.factorial n : ℝ) * omega n + θ n / (n : ℝ) := by
  rw [hid]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Source: `proof_gap/exercise_73/5.txt`; integer membership is an explicit witness. -/
theorem gap5
    (m : ℤ) (n : ℕ)
    (hn : 0 < n) :
    IsInteger ((Nat.factorial n : ℝ) * ((m : ℝ) / (n : ℝ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨(Nat.factorial k : ℤ) * m, ?_⟩
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Source: `proof_gap/exercise_73/6.txt`. -/
theorem gap6
    (n : ℕ) :
    IsInteger ((Nat.factorial n : ℝ) * omega n) := by
  let z : ℤ := ∑ j ∈ Finset.range (n + 1),
    ((Nat.factorial n / Nat.factorial j : ℕ) : ℤ)
  refine ⟨z, ?_⟩
  unfold omega z
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  have hd : Nat.factorial j ∣ Nat.factorial n :=
    Nat.factorial_dvd_factorial hjn
  change (Nat.factorial n : ℝ) * (1 / (Nat.factorial j : ℝ)) =
    ((Nat.factorial n / Nat.factorial j : ℕ) : ℝ)
  rw [Nat.cast_div_charZero hd]
  field_simp

/-- Source: `proof_gap/exercise_73/7.txt`; θ is no longer a disconnected existential. -/
theorem gap7
    (n : ℕ) (θ : ℕ → ℝ)
    (hn : 0 < n)
    (hθ : 0 < θ n) :
    0 < θ n / (n : ℝ) := by
  exact div_pos hθ (by positivity)

/-- Source: `proof_gap/exercise_73/8.txt`; θ is no longer a disconnected existential. -/
theorem gap8
    (n : ℕ) (θ : ℕ → ℝ)
    (hn : 0 < n)
    (hθ : θ n < 1) :
    θ n / (n : ℝ) < 1 := by
  have hnR : (0 : ℝ) < n := by positivity
  rw [div_lt_one hnR]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Source: `proof_gap/exercise_73/9.txt`. -/
theorem gap9 :
    (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_73/10.txt`; an integer cannot differ from an integer by a number in `(0,1)`. -/
theorem gap10
    (A B r : ℝ)
    (hA : IsInteger A)
    (hB : IsInteger B)
    (heq : A = B + r)
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    False := by
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  have her : r = ((a - b : ℤ) : ℝ) := by
    calc
      r = (a : ℝ) - (b : ℝ) := by linarith
      _ = ((a - b : ℤ) : ℝ) := by push_cast; ring
  have hz0 : (0 : ℤ) < a - b := by
    exact_mod_cast (show (0 : ℝ) < ((a - b : ℤ) : ℝ) by simpa [← her])
  have hz1 : a - b < (1 : ℤ) := by
    exact_mod_cast (show ((a - b : ℤ) : ℝ) < 1 by simpa [← her])
  omega

/-- Source: `proof_gap/exercise_73/11.txt`; exclude every integer fraction representation. -/
theorem gap11
    (e : ℝ)
    (hcontra : ∀ m : ℤ, ∀ n : ℕ, 0 < n → RatRep e m n → False) :
    ∀ m : ℤ, ∀ n : ℕ, 0 < n →
      e ≠ (m : ℝ) / (n : ℝ) := by
  intro m n hn heq
  exact hcontra m n hn ⟨hn, heq⟩

/-- Source: `proof_gap/exercise_73/12.txt`; standard Mathlib irrationality. -/
theorem gap12
    (e : ℝ)
    (hnotrat : ∀ m : ℤ, ∀ n : ℕ, 0 < n →
      e ≠ (m : ℝ) / (n : ℝ)) :
    Irrational e := by
  rw [irrational_iff_ne_rational]
  intro a b hb
  by_cases hbpos : 0 < b
  · have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hbpos.le
    have hnat : 0 < b.toNat := by omega
    have hcast : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
      norm_cast
    simpa [hcast] using hnotrat a b.toNat hnat
  · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
    have hbcast : ((-b).toNat : ℤ) = -b :=
      Int.toNat_of_nonneg (by omega)
    have hnat : 0 < (-b).toNat := by omega
    have hcast : (((-b).toNat : ℕ) : ℝ) = (-b : ℤ) := by
      norm_cast
    have h := hnotrat (-a) (-b).toNat hnat
    simpa [hcast] using h

end

end ProofGap.Exercise73
