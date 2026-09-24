import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise428

open scoped BigOperators

noncomputable section

def geometricSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun i => x ^ i)
def f (m n : ℕ) (x : ℝ) : ℝ :=
  (m : ℝ) / (1 - x ^ m) - (n : ℝ) / (1 - x ^ n)
def value (m n : ℕ) : ℝ := ((m : ℝ) - n) / 2
def intermediateValue (m l : ℕ) : ℝ :=
  -(((m : ℝ) * l * (l - 1) / 2 +
      (m : ℝ) * l * (m + 1) / 2) / ((m : ℝ) * (m + l)))
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_428/1.txt`. -/
private def quotientSum : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, x => quotientSum k x + geometricSum k x

private theorem geometricSum_succ (k : ℕ) (x : ℝ) :
    geometricSum (k + 1) x = geometricSum k x + x ^ k := by
  simp [geometricSum, Finset.sum_range_succ]

private theorem finiteGeometricSum_at_one (k : ℕ) :
    geometricSum k 1 = (k : ℝ) := by
  simp [geometricSum]

private theorem pow_eq_one_add_mul_geometricSum (k : ℕ) (x : ℝ) :
    x ^ k = 1 + (x - 1) * geometricSum k x := by
  induction k with
  | zero => simp [geometricSum]
  | succ k ih =>
      calc
        x ^ (k + 1) = x ^ k * x := by rw [pow_succ]
        _ = x ^ k + (x - 1) * x ^ k := by ring
        _ = (1 + (x - 1) * geometricSum k x) +
              (x - 1) * x ^ k :=
          congrArg (fun z : ℝ => z + (x - 1) * x ^ k) ih
        _ = 1 + (x - 1) * (geometricSum k x + x ^ k) := by ring
        _ = 1 + (x - 1) * geometricSum (k + 1) x := by
          rw [geometricSum_succ]

private theorem geometricSum_expand (k : ℕ) (x : ℝ) :
    geometricSum k x =
      (k : ℝ) + (x - 1) * quotientSum k x := by
  induction k with
  | zero => simp [geometricSum, quotientSum]
  | succ k ih =>
      calc
        geometricSum (k + 1) x = geometricSum k x + x ^ k :=
          geometricSum_succ k x
        _ = ((k : ℝ) + (x - 1) * quotientSum k x) + x ^ k :=
          congrArg (fun z : ℝ => z + x ^ k) ih
        _ = ((k : ℝ) + (x - 1) * quotientSum k x) +
              (1 + (x - 1) * geometricSum k x) :=
          congrArg
            (fun z : ℝ => (k : ℝ) + (x - 1) * quotientSum k x + z)
            (pow_eq_one_add_mul_geometricSum k x)
        _ = ((k + 1 : ℕ) : ℝ) +
              (x - 1) * (quotientSum k x + geometricSum k x) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        _ = ((k + 1 : ℕ) : ℝ) +
              (x - 1) * quotientSum (k + 1) x := by
          rfl

private theorem quotientSum_one (k : ℕ) :
    quotientSum k 1 = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp [quotientSum]
  | succ k ih =>
      rw [quotientSum, ih]
      simp [finiteGeometricSum_at_one, Nat.cast_succ]
      ring

private theorem geometricSum_continuousAt (k : ℕ) :
    ContinuousAt (geometricSum k) 1 := by
  induction k with
  | zero =>
      simpa [geometricSum] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 1)
  | succ k ih =>
      have hfun : geometricSum (k + 1) =
          fun x : ℝ => geometricSum k x + x ^ k := by
        funext x
        exact geometricSum_succ k x
      rw [hfun]
      exact ih.add (continuousAt_id.pow k)

private theorem quotientSum_continuousAt (k : ℕ) :
    ContinuousAt (quotientSum k) 1 := by
  induction k with
  | zero =>
      simpa [quotientSum] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 1)
  | succ k ih =>
      simpa [quotientSum] using
        ih.add (geometricSum_continuousAt k)

private theorem cancel_div_left (a b c : ℝ) (ha : a ≠ 0) :
    (a * b) / (a * c) = b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc
    a * b * (c⁻¹ * a⁻¹) = (a * a⁻¹) * (b * c⁻¹) := by ring
    _ = b * c⁻¹ := by simp [ha]

theorem gap1 (m n : ℕ) (hmn : m = n) :
    HasLimitAt (f m n) 1 0 := by
  subst n
  have hf : f m m = fun _ : ℝ => 0 := by
    funext x
    unfold f
    simp
  unfold HasLimitAt
  rw [hf]
  exact tendsto_const_nhds

/-- Source: `proof_gap/exercise_428/2.txt`; bind the difference witness. -/
theorem gap2 (m n : ℕ) (hmn : m < n) :
    ∃ l : ℕ, 0 < l ∧ m + l = n := by
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  omega

/-- Source: `proof_gap/exercise_428/3.txt`; replace ellipses by geometric sums and require nonzero denominators. -/
theorem gap3 (m n : ℕ) : ∀ x, x ≠ 1 →
    geometricSum m x ≠ 0 → geometricSum n x ≠ 0 →
    f m n x =
      ((m : ℝ) * geometricSum n x - (n : ℝ) * geometricSum m x) /
        ((1 - x) * geometricSum m x * geometricSum n x) := by
  intro x hx hgm hgn
  have hxsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hmfac :
      1 - x ^ m = (1 - x) * geometricSum m x := by
    rw [pow_eq_one_add_mul_geometricSum]
    ring
  have hnfac :
      1 - x ^ n = (1 - x) * geometricSum n x := by
    rw [pow_eq_one_add_mul_geometricSum]
    ring
  unfold f
  rw [hmfac, hnfac]
  field_simp [hxsub, hgm, hgn]

/-- Source: `proof_gap/exercise_428/4.txt`; use the bound difference `l` and a closed intermediate value. -/
theorem gap4 (m n l : ℕ) (hm : 0 < m) (hl : 0 < l) (h : m + l = n) :
    HasLimitAt (f m n) 1 (intermediateValue m l) := by
  subst n
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hmlR : ((m + l : ℕ) : ℝ) ≠ 0 := by positivity
  have hden :
      geometricSum m 1 * geometricSum (m + l) 1 ≠ 0 := by
    simpa only [finiteGeometricSum_at_one] using
      (mul_ne_zero hmR hmlR)
  let q : ℝ → ℝ := fun x =>
    -(((m : ℝ) * quotientSum (m + l) x -
        ((m + l : ℕ) : ℝ) * quotientSum m x) /
      (geometricSum m x * geometricSum (m + l) x))
  have hqcont : ContinuousAt q 1 := by
    dsimp [q]
    exact
      ((((continuousAt_const :
            ContinuousAt (fun _ : ℝ => (m : ℝ)) 1).mul
          (quotientSum_continuousAt (m + l))).sub
        ((continuousAt_const :
            ContinuousAt (fun _ : ℝ => ((m + l : ℕ) : ℝ)) 1).mul
          (quotientSum_continuousAt m))).div
        ((geometricSum_continuousAt m).mul
          (geometricSum_continuousAt (m + l))) hden).neg
  have hq1 : q 1 = intermediateValue m l := by
    dsimp [q, intermediateValue]
    simp [quotientSum_one, finiteGeometricSum_at_one, Nat.cast_add]
    field_simp [hmR, hmlR]
    ring
  have ht : Filter.Tendsto q
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (intermediateValue m l)) := by
    rw [← hq1]
    exact hqcont.tendsto.mono_left inf_le_left
  have hdenEventually :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        geometricSum m x * geometricSum (m + l) x ≠ 0 :=
    Filter.Eventually.filter_mono inf_le_left
      (((geometricSum_continuousAt m).mul
        (geometricSum_continuousAt (m + l))).eventually_ne hden)
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hdenEventually] with x hx hxden
  have hx1 : x ≠ 1 := by simpa using hx
  have hxsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hgm : geometricSum m x ≠ 0 :=
    (mul_ne_zero_iff.mp hxden).1
  have hgn : geometricSum (m + l) x ≠ 0 :=
    (mul_ne_zero_iff.mp hxden).2
  dsimp [q]
  rw [gap3 m (m + l) x hx1 hgm hgn]
  have hnum :
      (m : ℝ) * geometricSum (m + l) x -
          ((m + l : ℕ) : ℝ) * geometricSum m x =
        (1 - x) *
          (-((m : ℝ) * quotientSum (m + l) x -
            ((m + l : ℕ) : ℝ) * quotientSum m x)) := by
    rw [geometricSum_expand, geometricSum_expand]
    simp only [Nat.cast_add]
    ring
  rw [hnum]
  simpa only [mul_assoc, neg_div] using
    (cancel_div_left (1 - x)
      (-((m : ℝ) * quotientSum (m + l) x -
        ((m + l : ℕ) : ℝ) * quotientSum m x))
      (geometricSum m x * geometricSum (m + l) x) hxsub).symm

/-- Source: `proof_gap/exercise_428/5.txt`. -/
theorem gap5 (m n l : ℕ) (hm : 0 < m) (hl : 0 < l) (h : m + l = n) :
    HasLimitAt (f m n) 1 (intermediateValue m l) := by
  exact gap4 m n l hm hl h

/-- Source: `proof_gap/exercise_428/6.txt`. -/
theorem gap6 (m n l : ℕ) (hm : 0 < m) (hl : 0 < l) (h : m + l = n) :
    intermediateValue m l =
      -(((m : ℝ) * l * (l - 1) / 2 +
        (m : ℝ) * l * (m + 1) / 2) / ((m : ℝ) * n)) := by
  subst n
  simp [intermediateValue, Nat.cast_add]

/-- Source: `proof_gap/exercise_428/7.txt`. -/
theorem gap7 (m n l : ℕ) (hm : 0 < m) (hl : 0 < l) (h : m + l = n) :
    intermediateValue m l =
      -((m : ℝ) * l * (m + l) / (2 * m * n)) := by
  subst n
  unfold intermediateValue
  simp only [Nat.cast_add]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hsumR : (m : ℝ) + (l : ℝ) ≠ 0 := by positivity
  field_simp [hmR, hsumR]
  ring

/-- Source: `proof_gap/exercise_428/8.txt`. -/
theorem gap8 (m n l : ℕ) (hm : 0 < m) (hl : 0 < l) (h : m + l = n) :
    intermediateValue m l = value m n := by
  subst n
  unfold intermediateValue value
  simp only [Nat.cast_add]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hsumR : (m : ℝ) + (l : ℝ) ≠ 0 := by positivity
  field_simp [hmR, hsumR]
  ring

/-- Source: `proof_gap/exercise_428/9.txt`. -/
theorem gap9 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m < n) :
    HasLimitAt (f m n) 1 (value m n) := by
  obtain ⟨l, hl, h⟩ := gap2 m n hmn
  rw [← gap8 m n l hm hl h]
  exact gap4 m n l hm hl h

/-- Source: `proof_gap/exercise_428/10.txt`. -/
theorem gap10 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (f m n) 1 (value m n) := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact gap9 m n hm hn hmn
  · subst n
    simpa [value] using (gap1 m m rfl)
  · have ht : HasLimitAt (fun x : ℝ => -f n m x) 1 (-value n m) :=
      (gap9 n m hn hm hnm).neg
    have hf : (fun x : ℝ => -f n m x) = f m n := by
      funext x
      unfold f
      ring
    have hv : -value n m = value m n := by
      unfold value
      ring
    rw [hf, hv] at ht
    exact ht

end

end ProofGap.Exercise428
