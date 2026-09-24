import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3106

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval Topology

def delta (a b : ℝ) (n : ℕ) : ℝ :=
  (b - a) / n

def samplePoint (a b : ℝ) (n i : ℕ) : ℝ :=
  a + i * delta a b n

def sampleValue (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  f (samplePoint a b n i)

def productSequence (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n,
    (1 + delta a b n * sampleValue f a b n i)

def riemannSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    sampleValue f a b n i * delta a b n

def totalLogRemainder (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  Real.log (productSequence f a b n) - riemannSum f a b n

def RiemannAdmissible (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  IntervalIntegrable f volume a b ∧
  (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.uIcc a b, |f x| ≤ M) ∧
  Tendsto (riemannSum f a b) atTop (𝓝 (∫ x in a..b, f x))

/--
Exercise 3106, gap 1; factor positivity and the logarithm
identity hold eventually, which is all the limit argument uses.
-/
private theorem eventual_sample_control (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.Icc 1 n,
        |sampleValue f a b n i| ≤ M ∧
        |delta a b n * sampleValue f a b n i| ≤ (1 : ℝ) / 2 := by
  rcases hf.2.1 with ⟨M, hM, hfM⟩
  refine ⟨M, hM, ?_⟩
  have hdelta : Tendsto (delta a b) atTop (nhds 0) := by
    simpa [delta] using
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hscaled :
      Tendsto (fun n : ℕ => |delta a b n| * M) atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using hdelta.norm.mul_const M
  have hsmall :
      ∀ᶠ n : ℕ in atTop, |delta a b n| * M < (1 : ℝ) / 2 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hnsmall
  intro i hi
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
  have hiReal0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hiReal : (i : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hi).2
  let t : ℝ := (i : ℝ) / (n : ℝ)
  have ht0 : 0 ≤ t := div_nonneg hiReal0 (le_of_lt hnReal)
  have ht1 : t ≤ 1 := (div_le_one hnReal).2 hiReal
  have hpoint : samplePoint a b n i = a + t * (b - a) := by
    dsimp [samplePoint, delta, t]
    ring
  have hxmem : samplePoint a b n i ∈ Set.uIcc a b := by
    rw [hpoint]
    rcases le_total a b with hab | hba
    · have hd : 0 ≤ b - a := sub_nonneg.mpr hab
      have hmul0 : 0 ≤ t * (b - a) := mul_nonneg ht0 hd
      have hmulle : t * (b - a) ≤ b - a := by
        simpa using mul_le_mul_of_nonneg_right ht1 hd
      have hp : a ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ b := by
        constructor <;> nlinarith
      simpa [Set.uIcc, hab] using hp
    · have hd : b - a ≤ 0 := sub_nonpos.mpr hba
      have hmul0 : t * (b - a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0 hd
      have hmulle : b - a ≤ t * (b - a) := by
        have := mul_le_mul_of_nonpos_right ht1 hd
        nlinarith
      have hp : b ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ a := by
        constructor <;> nlinarith
      simpa [Set.uIcc, hba] using hp
  have hv : |sampleValue f a b n i| ≤ M := by
    simpa [sampleValue] using hfM (samplePoint a b n i) hxmem
  refine ⟨hv, ?_⟩
  calc
    |delta a b n * sampleValue f a b n i| =
        |delta a b n| * |sampleValue f a b n i| := abs_mul _ _
    _ ≤ |delta a b n| * M :=
      mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    _ ≤ (1 : ℝ) / 2 := le_of_lt hnsmall

private theorem abs_log_one_plus_sub_self_le_two_sq
    {x : ℝ} (hx : |x| ≤ (1 : ℝ) / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hxl : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
  have hy : 0 < 1 + x := by
    nlinarith
  have hlogle : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hy
    linarith
  have hinvpos : 0 < (1 + x)⁻¹ := inv_pos.mpr hy
  have hinvlog := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at hinvlog
  have hfrac :
      x - Real.log (1 + x) ≤ x ^ 2 / (1 + x) := by
    calc
      x - Real.log (1 + x) = x + (-Real.log (1 + x)) := by ring
      _ ≤ x + ((1 + x)⁻¹ - 1) := by
        simpa [add_comm] using (add_le_add_left hinvlog x)
      _ = x ^ 2 / (1 + x) := by
        field_simp [ne_of_gt hy] <;> ring
  have hyhalf : (1 : ℝ) / 2 ≤ 1 + x := by
    nlinarith
  have hone : (1 : ℝ) ≤ 2 * (1 + x) := by
    nlinarith
  have hfrac' : x ^ 2 / (1 + x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ hy).2
    have hm := mul_le_mul_of_nonneg_left hone (sq_nonneg x)
    calc
      x ^ 2 = x ^ 2 * 1 := by ring
      _ ≤ x ^ 2 * (2 * (1 + x)) := hm
      _ = (2 * x ^ 2) * (1 + x) := by ring
  calc
    |Real.log (1 + x) - x| = x - Real.log (1 + x) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlogle)]
      ring
    _ ≤ x ^ 2 / (1 + x) := hfrac
    _ ≤ 2 * x ^ 2 := hfrac'

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (productSequence f a b n) =
        ∑ i ∈ Finset.Icc 1 n,
          Real.log (1 + delta a b n * sampleValue f a b n i) := by
  rcases eventual_sample_control f a b hf with ⟨M, hM, hcontrol⟩
  filter_upwards [hcontrol] with n hn
  let g : ℕ → ℝ := fun i =>
    1 + delta a b n * sampleValue f a b n i
  have hgpos : ∀ i ∈ Finset.Icc 1 n, 0 < g i := by
    intro i hi
    have hneg := (abs_le.mp (hn i hi).2).1
    dsimp [g]
    nlinarith
  have hlog : ∀ s : Finset ℕ, (∀ i ∈ s, 0 < g i) →
      Real.log (s.prod g) = s.sum (fun i => Real.log (g i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simp
    | @insert x s hx ih =>
        intro hs
        have hxpos : 0 < g x := hs x (Finset.mem_insert_self x s)
        have hspos : 0 < s.prod g := by
          exact Finset.prod_pos fun i hi =>
            hs i (Finset.mem_insert_of_mem hi)
        rw [Finset.prod_insert hx, Finset.sum_insert hx,
          Real.log_mul (ne_of_gt hxpos) (ne_of_gt hspos),
          ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))]
  simpa [productSequence, g] using hlog (Finset.Icc 1 n) hgpos

/--
Exercise 3106, gap 2; make the uniform per-factor
`O(δₙ²)` remainder explicit.
-/
theorem gap2 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ i ∈ Finset.Icc 1 n,
        |Real.log (1 + delta a b n * sampleValue f a b n i) -
            sampleValue f a b n i * delta a b n| ≤
          C * (delta a b n) ^ 2 := by
  rcases eventual_sample_control f a b hf with ⟨M, hM, hcontrol⟩
  rcases eventually_atTop.1 hcontrol with ⟨N, hN⟩
  refine ⟨2 * M ^ 2, mul_nonneg (by norm_num) (sq_nonneg M), N, ?_⟩
  intro n hn i hi
  have hbounds := hN n hn i hi
  have hv : |sampleValue f a b n i| ≤ M := hbounds.1
  have hsmall :
      |delta a b n * sampleValue f a b n i| ≤ (1 : ℝ) / 2 :=
    hbounds.2
  have hvprod :
      0 ≤ (M - |sampleValue f a b n i|) *
        (M + |sampleValue f a b n i|) :=
    mul_nonneg (sub_nonneg.mpr hv)
      (add_nonneg hM (abs_nonneg _))
  have hvsq : (sampleValue f a b n i) ^ 2 ≤ M ^ 2 := by
    nlinarith [hvprod, sq_abs (sampleValue f a b n i)]
  calc
    |Real.log (1 + delta a b n * sampleValue f a b n i) -
        sampleValue f a b n i * delta a b n| =
        |Real.log (1 + delta a b n * sampleValue f a b n i) -
          delta a b n * sampleValue f a b n i| := by
            rw [mul_comm]
    _ ≤ 2 * (delta a b n * sampleValue f a b n i) ^ 2 :=
      abs_log_one_plus_sub_self_le_two_sq hsmall
    _ = (2 * (sampleValue f a b n i) ^ 2) * (delta a b n) ^ 2 := by
      ring
    _ ≤ (2 * M ^ 2) * (delta a b n) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hvsq (by norm_num))
        (sq_nonneg _)

/--
Exercise 3106, gap 3; summing `n` uniform quadratic
remainders gives a function-level `O(1/n)` estimate.
-/
theorem gap3 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    (fun n : ℕ => totalLogRemainder f a b (n + 1))
      =O[atTop] (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  rcases gap2 f a b hf with ⟨C, hC, N, hrem⟩
  rcases eventually_atTop.1 (gap1 f a b hf) with ⟨Nlog, hlog⟩
  apply Asymptotics.IsBigO.of_bound (C * (b - a) ^ 2)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop Nlog] with n hn hnlog
  simp only [Real.norm_eq_abs]
  rw [totalLogRemainder, hlog (n + 1) (by omega), riemannSum,
    ← Finset.sum_sub_distrib]
  calc
    |Finset.sum (Finset.Icc 1 (n + 1)) (fun i =>
        Real.log
            (1 + delta a b (n + 1) * sampleValue f a b (n + 1) i) -
          sampleValue f a b (n + 1) i * delta a b (n + 1))| ≤
        Finset.sum (Finset.Icc 1 (n + 1)) (fun i =>
          |Real.log
              (1 + delta a b (n + 1) * sampleValue f a b (n + 1) i) -
            sampleValue f a b (n + 1) i * delta a b (n + 1)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Finset.Icc 1 (n + 1))
          (fun _ => C * (delta a b (n + 1)) ^ 2) := by
      exact Finset.sum_le_sum fun i hi => hrem (n + 1) (by omega) i hi
    _ = (((n + 1 : ℕ) : ℝ)) * (C * (delta a b (n + 1)) ^ 2) := by
      simp
    _ = (C * (b - a) ^ 2) * |1 / (((n + 1 : ℕ) : ℝ))| := by
      have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      rw [abs_of_pos (one_div_pos.mpr hnpos)]
      unfold delta
      field_simp [ne_of_gt hnpos]

/-- Exercise 3106, gap 4; use the right-endpoint Riemann-sum premise. -/
theorem gap4 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    Tendsto
      (fun n => Real.log (productSequence f a b n))
      atTop (𝓝 (∫ x in a..b, f x)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hrecip0 :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hrecip :
      Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hrecip0
  rcases (gap3 f a b hf).exists_pos with ⟨c, hcpos, hc⟩
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖totalLogRemainder f a b (n + 1)‖ ≤
          c * ‖1 / (((n + 1 : ℕ) : ℝ))‖ := hc.bound
  have hupper :
      Tendsto (fun n : ℕ => c * ‖1 / (((n + 1 : ℕ) : ℝ))‖)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrecip.norm
  have hlower :
      Tendsto (fun n : ℕ => -(c * ‖1 / (((n + 1 : ℕ) : ℝ))‖))
        atTop (nhds 0) := by
    simpa using hupper.neg
  have hremainder :
      Tendsto (fun n : ℕ => totalLogRemainder f a b (n + 1))
        atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper
      (hbound.mono fun n hn => by
        rw [Real.norm_eq_abs] at hn ⊢
        exact (neg_le_neg hn).trans (neg_abs_le _))
      (hbound.mono fun n hn => by
        rw [Real.norm_eq_abs] at hn ⊢
        exact (le_abs_self _).trans hn)
  have hsum :
      Tendsto (fun n : ℕ => riemannSum f a b (n + 1)) atTop
        (nhds (∫ x in a..b, f x)) :=
    (tendsto_add_atTop_iff_nat 1).2 hf.2.2
  simpa [totalLogRemainder] using hremainder.add hsum

/-- Exercise 3106, gap 5; exponentiate the logarithmic limit. -/
theorem gap5 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    Tendsto (productSequence f a b) atTop
      (𝓝 (Real.exp (∫ x in a..b, f x))) := by
  rcases eventual_sample_control f a b hf with ⟨M, hM, hcontrol⟩
  have heq :
      (fun n => productSequence f a b n) =ᶠ[atTop]
        (fun n => Real.exp (Real.log (productSequence f a b n))) := by
    filter_upwards [hcontrol] with n hn
    have hfactor : ∀ i ∈ Finset.Icc 1 n,
        0 < 1 + delta a b n * sampleValue f a b n i := by
      intro i hi
      have hneg := (abs_le.mp (hn i hi).2).1
      nlinarith
    have hprod : 0 < productSequence f a b n := by
      unfold productSequence
      exact Finset.prod_pos hfactor
    exact (Real.exp_log hprod).symm
  have hexp :
      Tendsto
        (fun n => Real.exp (Real.log (productSequence f a b n)))
        atTop (nhds (Real.exp (∫ x in a..b, f x))) :=
    (Real.continuous_exp.tendsto _).comp (gap4 f a b hf)
  exact (tendsto_congr' heq).2 hexp

/-- Exercise 3106, gap 6; unfold the finite product sequence. -/
theorem gap6 (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannAdmissible f a b) :
    Tendsto
      (fun n : ℕ =>
        ∏ i ∈ Finset.Icc 1 n,
          (1 + delta a b n * f (a + i * delta a b n)))
      atTop (𝓝 (Real.exp (∫ x in a..b, f x))) := by
  simpa [productSequence, sampleValue, samplePoint] using gap5 f a b hf

end

end ProofGap.Exercise3106
