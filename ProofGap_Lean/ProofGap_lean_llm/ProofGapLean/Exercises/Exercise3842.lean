import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

namespace ProofGap.Exercise3842

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def betaIntegrand (t x y : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, betaIntegrand t x y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun u => f u y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun v => f x v) y

def iterPartialX : ℕ → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  | 0, f => f
  | n + 1, f => partialX (iterPartialX n f)

def iterPartialY : ℕ → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  | 0, f => f
  | n + 1, f => partialY (iterPartialY n f)

private def momentIntegrand (i j : ℕ) (x y t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1) *
    Real.log t ^ i * Real.log (1 - t) ^ j

private def momentIntegral (i j : ℕ) (x y : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, momentIntegrand i j x y t

private theorem momentAEStronglyMeasurable
    (i j : ℕ) (x y : ℝ) :
    AEStronglyMeasurable (momentIntegrand i j x y)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hr₁ :
      ContinuousOn (fun t : ℝ => Real.rpow t (x - 1))
        (Ioo (0 : ℝ) 1) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hr₂ :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) (y - 1))
        (Ioo (0 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun t ht => Or.inl (sub_ne_zero.mpr ht.2.ne'))
  have hl₁ :
      ContinuousOn (fun t : ℝ => Real.log t) (Ioo (0 : ℝ) 1) :=
    Real.continuousOn_log.mono (fun t ht => ht.1.ne')
  have hl₂ :
      ContinuousOn (fun t : ℝ => Real.log (1 - t))
        (Ioo (0 : ℝ) 1) := by
    intro t ht
    have hg : ContinuousAt (fun u : ℝ => 1 - u) t :=
      continuousAt_const.sub continuousAt_id
    exact ((Real.continuousAt_log (sub_ne_zero.mpr ht.2.ne')).comp hg).continuousWithinAt
  have hc :
      ContinuousOn (momentIntegrand i j x y) (Ioo (0 : ℝ) 1) := by
    simpa only [momentIntegrand] using
      (((hr₁.mul hr₂).mul (hl₁.pow i)).mul (hl₂.pow j))
  exact hc.aestronglyMeasurable measurableSet_Ioo

private theorem log_weight_bound
    {t a : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ha : 0 < a) (n : ℕ) :
    Real.rpow t (a * (n + 1) - 1) * |Real.log t| ^ n ≤
      (1 / a) ^ n * Real.rpow t (a - 1) := by
  have hlog :
      |Real.log t * Real.rpow t a| ≤ 1 / a :=
    (Real.abs_log_mul_self_rpow_lt t a ht ht1 ha).le
  have hpow :
      |Real.log t * Real.rpow t a| ^ n ≤ (1 / a) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hlog n
  have hrpos : 0 < Real.rpow t (a - 1) :=
    Real.rpow_pos_of_pos ht _
  have habsr : |Real.rpow t a| = Real.rpow t a :=
    abs_of_pos (Real.rpow_pos_of_pos ht a)
  have hpowr :
      Real.rpow t a ^ n = Real.rpow t (a * (n : ℝ)) := by
    exact (Real.rpow_mul_natCast ht.le a n).symm
  have hadd :
      Real.rpow t (a * (n : ℝ)) * Real.rpow t (a - 1) =
        Real.rpow t (a * (n : ℝ) + (a - 1)) := by
    exact (Real.rpow_add ht _ _).symm
  calc
    Real.rpow t (a * (n + 1) - 1) * |Real.log t| ^ n =
        |Real.log t * Real.rpow t a| ^ n *
          Real.rpow t (a - 1) := by
      rw [abs_mul, habsr, mul_pow, hpowr]
      calc
        Real.rpow t (a * (n + 1) - 1) *
            |Real.log t| ^ n =
          Real.rpow t (a * (n : ℝ) + (a - 1)) *
            |Real.log t| ^ n := by
          congr 1
          push_cast
          ring
        _ = (Real.rpow t (a * (n : ℝ)) * Real.rpow t (a - 1)) *
            |Real.log t| ^ n := by rw [hadd]
        _ = |Real.log t| ^ n * Real.rpow t (a * (n : ℝ)) *
            Real.rpow t (a - 1) := by ring
    _ ≤ (1 / a) ^ n * Real.rpow t (a - 1) :=
      mul_le_mul_of_nonneg_right hpow hrpos.le

private theorem betaKernel_integrableOn
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun t : ℝ => Real.rpow t (a - 1) *
        Real.rpow (1 - t) (b - 1))
      (Ioo (0 : ℝ) 1) := by
  let f : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((a : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((b : ℂ) - 1)
  have hfInterval : IntervalIntegrable f volume 0 1 := by
    exact Complex.betaIntegral_convergent
      (by simpa using ha) (by simpa using hb)
  have hf : IntegrableOn f (Ioo (0 : ℝ) 1) := by
    exact hfInterval.def'.mono_set (by
      rw [uIoc_of_le zero_le_one]
      exact Ioo_subset_Ioc_self)
  have hfre : IntegrableOn (fun t => (f t).re) (Ioo (0 : ℝ) 1) := by
    exact hf.re
  refine hfre.congr_fun ?_ measurableSet_Ioo
  intro t ht
  have hta :
      (t : ℂ) ^ ((a : ℂ) - 1) =
        (Real.rpow t (a - 1) : ℂ) := by
    rw [show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow ht.1.le (a - 1)).symm
  have htb :
      (1 - (t : ℂ)) ^ ((b : ℂ) - 1) =
        (Real.rpow (1 - t) (b - 1) : ℂ) := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
    rw [show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le) (b - 1)).symm
  dsimp [f]
  rw [hta, htb]
  simp

private theorem momentIntegrable
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (i j : ℕ) :
    IntegrableOn (momentIntegrand i j x y) (Ioo (0 : ℝ) 1) := by
  let a : ℝ := x / ((i : ℝ) + 1)
  let b : ℝ := y / ((j : ℝ) + 1)
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have ha : 0 < a := div_pos hx hi
  have hb : 0 < b := div_pos hy hj
  have hax : a * ((i : ℝ) + 1) = x := by
    dsimp [a]
    exact div_mul_cancel₀ x hi.ne'
  have hby : b * ((j : ℝ) + 1) = y := by
    dsimp [b]
    exact div_mul_cancel₀ y hj.ne'
  let C : ℝ := (1 / a) ^ i * (1 / b) ^ j
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdom :
      IntegrableOn
        (fun t : ℝ => C *
          (Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)))
        (Ioo (0 : ℝ) 1) :=
    (betaKernel_integrableOn ha hb).const_mul C
  refine hdom.mono' ?_ ?_
  · exact momentAEStronglyMeasurable i j x y
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hsub0 : 0 < 1 - t := sub_pos.mpr ht.2
    have hsub1 : 1 - t ≤ 1 := by linarith
    have hleft := log_weight_bound ht0 ht1 ha i
    have hright := log_weight_bound hsub0 hsub1 hb j
    rw [hax] at hleft
    rw [hby] at hright
    have hleft0 :
        0 ≤ Real.rpow t (x - 1) * |Real.log t| ^ i :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (pow_nonneg (abs_nonneg _) _)
    have hright0 :
        0 ≤ Real.rpow (1 - t) (y - 1) *
          |Real.log (1 - t)| ^ j :=
      mul_nonneg (Real.rpow_nonneg hsub0.le _) (pow_nonneg (abs_nonneg _) _)
    have hrx : 0 ≤ Real.rpow t (x - 1) :=
      Real.rpow_nonneg ht0.le _
    have hry : 0 ≤ Real.rpow (1 - t) (y - 1) :=
      Real.rpow_nonneg hsub0.le _
    rw [momentIntegrand, Real.norm_eq_abs]
    simp only [abs_mul, abs_pow]
    rw [abs_of_nonneg hrx, abs_of_nonneg hry]
    calc
      Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1) *
            |Real.log t| ^ i * |Real.log (1 - t)| ^ j =
          (Real.rpow t (x - 1) * |Real.log t| ^ i) *
            (Real.rpow (1 - t) (y - 1) *
              |Real.log (1 - t)| ^ j) := by ring
      _ ≤ ((1 / a) ^ i * Real.rpow t (a - 1)) *
            ((1 / b) ^ j * Real.rpow (1 - t) (b - 1)) :=
        mul_le_mul hleft hright hright0
          (mul_nonneg (pow_nonneg (by positivity) _)
            (Real.rpow_nonneg ht0.le _))
      _ = C *
          (Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) := by
        dsimp [C]
        ring

private theorem hasDerivAt_momentIntegral_fst
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (i j : ℕ) :
    HasDerivAt (fun u => momentIntegral i j u y)
      (momentIntegral (i + 1) j x y) x := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let s : Set ℝ := Ioi (x / 2)
  let F : ℝ → ℝ → ℝ := fun u t => momentIntegrand i j u y t
  let F' : ℝ → ℝ → ℝ := fun u t => momentIntegrand (i + 1) j u y t
  let bound : ℝ → ℝ :=
    fun t => ‖momentIntegrand (i + 1) j (x / 2) y t‖
  have hs : s ∈ 𝓝 x := by
    exact Ioi_mem_nhds (by linarith)
  have hF_meas :
      ∀ᶠ u in 𝓝 x, AEStronglyMeasurable (F u) μ := by
    apply Filter.Eventually.of_forall
    intro u
    exact momentAEStronglyMeasurable i j u y
  have hF_int : Integrable (F x) μ :=
    momentIntegrable hx hy i j
  have hF'_meas : AEStronglyMeasurable (F' x) μ :=
    momentAEStronglyMeasurable (i + 1) j x y
  have hbound_int : Integrable bound μ := by
    exact (momentIntegrable (half_pos hx) hy (i + 1) j).norm
  have hbound :
      ∀ᵐ t ∂μ, ∀ u ∈ s, ‖F' u t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    intro u hu
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hsub0 : 0 < 1 - t := sub_pos.mpr ht.2
    have hrpow :
        Real.rpow t (u - 1) ≤ Real.rpow t (x / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by
        change x / 2 < u at hu
        linarith)
    have hQ :
        0 ≤ Real.rpow (1 - t) (y - 1) *
          |Real.log t| ^ (i + 1) * |Real.log (1 - t)| ^ j := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hsub0.le _)
          (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg (abs_nonneg _) _)
    have hru : 0 ≤ t ^ (u - 1 : ℝ) :=
      Real.rpow_nonneg ht0.le _
    have hrx : 0 ≤ t ^ (x / 2 - 1 : ℝ) :=
      Real.rpow_nonneg ht0.le _
    have hry : 0 ≤ (1 - t) ^ (y - 1 : ℝ) :=
      Real.rpow_nonneg hsub0.le _
    dsimp [F', bound, momentIntegrand]
    simp only [abs_mul, abs_pow]
    rw [abs_of_nonneg hru, abs_of_nonneg hrx, abs_of_nonneg hry]
    calc
      Real.rpow t (u - 1) * Real.rpow (1 - t) (y - 1) *
            |Real.log t| ^ (i + 1) * |Real.log (1 - t)| ^ j =
          Real.rpow t (u - 1) *
            (Real.rpow (1 - t) (y - 1) *
              |Real.log t| ^ (i + 1) *
                |Real.log (1 - t)| ^ j) := by ring
      _ ≤ Real.rpow t (x / 2 - 1) *
            (Real.rpow (1 - t) (y - 1) *
              |Real.log t| ^ (i + 1) *
                |Real.log (1 - t)| ^ j) :=
        mul_le_mul_of_nonneg_right hrpow hQ
      _ = Real.rpow t (x / 2 - 1) *
            Real.rpow (1 - t) (y - 1) *
              |Real.log t| ^ (i + 1) *
                |Real.log (1 - t)| ^ j := by ring
  have hdiff :
      ∀ᵐ t ∂μ, ∀ u ∈ s, HasDerivAt (F · t) (F' u t) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    intro u hu
    have hd₀ := ((hasDerivAt_id u).sub_const 1).const_rpow ht.1
    have hd₁ := hd₀.mul_const (Real.rpow (1 - t) (y - 1))
    have hd₂ := hd₁.mul_const (Real.log t ^ i)
    have hd := hd₂.mul_const (Real.log (1 - t) ^ j)
    have hfun :
        (fun v => F v t) =
          (fun v =>
            Real.rpow t (v - 1) *
              Real.rpow (1 - t) (y - 1) *
                Real.log t ^ i * Real.log (1 - t) ^ j) := by
      funext v
      rfl
    change HasDerivAt (fun v => F v t) (F' u t) u
    rw [hfun]
    apply hd.congr_deriv
    dsimp [F', momentIntegrand]
    rw [pow_succ]
    ring
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) (μ := μ)
      hs hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [momentIntegral, F, F', μ] using hmain.2

private theorem hasDerivAt_momentIntegral_snd
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (i j : ℕ) :
    HasDerivAt (fun v => momentIntegral i j x v)
      (momentIntegral i (j + 1) x y) y := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let s : Set ℝ := Ioi (y / 2)
  let F : ℝ → ℝ → ℝ := fun v t => momentIntegrand i j x v t
  let F' : ℝ → ℝ → ℝ := fun v t => momentIntegrand i (j + 1) x v t
  let bound : ℝ → ℝ :=
    fun t => ‖momentIntegrand i (j + 1) x (y / 2) t‖
  have hs : s ∈ 𝓝 y := by
    exact Ioi_mem_nhds (by linarith)
  have hF_meas :
      ∀ᶠ v in 𝓝 y, AEStronglyMeasurable (F v) μ := by
    apply Filter.Eventually.of_forall
    intro v
    exact momentAEStronglyMeasurable i j x v
  have hF_int : Integrable (F y) μ :=
    momentIntegrable hx hy i j
  have hF'_meas : AEStronglyMeasurable (F' y) μ :=
    momentAEStronglyMeasurable i (j + 1) x y
  have hbound_int : Integrable bound μ := by
    exact (momentIntegrable hx (half_pos hy) i (j + 1)).norm
  have hbound :
      ∀ᵐ t ∂μ, ∀ v ∈ s, ‖F' v t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    intro v hv
    have ht0 : 0 < t := ht.1
    have hsub0 : 0 < 1 - t := sub_pos.mpr ht.2
    have hsub1 : 1 - t ≤ 1 := by linarith
    have hrpow :
        Real.rpow (1 - t) (v - 1) ≤
          Real.rpow (1 - t) (y / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hsub0 hsub1 (by
        change y / 2 < v at hv
        linarith)
    have hQ :
        0 ≤ Real.rpow t (x - 1) *
          |Real.log t| ^ i * |Real.log (1 - t)| ^ (j + 1) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht0.le _)
          (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg (abs_nonneg _) _)
    have hrv : 0 ≤ (1 - t) ^ (v - 1 : ℝ) :=
      Real.rpow_nonneg hsub0.le _
    have hry : 0 ≤ (1 - t) ^ (y / 2 - 1 : ℝ) :=
      Real.rpow_nonneg hsub0.le _
    have hrx : 0 ≤ t ^ (x - 1 : ℝ) :=
      Real.rpow_nonneg ht0.le _
    dsimp [F', bound, momentIntegrand]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow]
    rw [abs_of_nonneg hrv, abs_of_nonneg hry, abs_of_nonneg hrx]
    calc
      Real.rpow t (x - 1) * Real.rpow (1 - t) (v - 1) *
            |Real.log t| ^ i * |Real.log (1 - t)| ^ (j + 1) =
          Real.rpow (1 - t) (v - 1) *
            (Real.rpow t (x - 1) * |Real.log t| ^ i *
              |Real.log (1 - t)| ^ (j + 1)) := by ring
      _ ≤ Real.rpow (1 - t) (y / 2 - 1) *
            (Real.rpow t (x - 1) * |Real.log t| ^ i *
              |Real.log (1 - t)| ^ (j + 1)) :=
        mul_le_mul_of_nonneg_right hrpow hQ
      _ = Real.rpow t (x - 1) *
            Real.rpow (1 - t) (y / 2 - 1) *
              |Real.log t| ^ i *
                |Real.log (1 - t)| ^ (j + 1) := by ring
  have hdiff :
      ∀ᵐ t ∂μ, ∀ v ∈ s, HasDerivAt (F · t) (F' v t) v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    intro v hv
    have hd₀ := ((hasDerivAt_id v).sub_const 1).const_rpow
      (sub_pos.mpr ht.2)
    have hd₁ := hd₀.const_mul (Real.rpow t (x - 1))
    have hd₂ := hd₁.mul_const (Real.log t ^ i)
    have hd := hd₂.mul_const (Real.log (1 - t) ^ j)
    have hfun :
        (fun w => F w t) =
          (fun w =>
            Real.rpow t (x - 1) *
              Real.rpow (1 - t) (w - 1) *
                Real.log t ^ i * Real.log (1 - t) ^ j) := by
      funext w
      rfl
    change HasDerivAt (fun w => F w t) (F' v t) v
    rw [hfun]
    apply hd.congr_deriv
    dsimp [F', momentIntegrand]
    rw [pow_succ]
    ring
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) (μ := μ)
      hs hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [momentIntegral, F, F', μ] using hmain.2

private theorem iteratedDeriv_momentIntegral_fst
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (k i j : ℕ) :
    iteratedDeriv k (fun u => momentIntegral i j u y) x =
      momentIntegral (i + k) j x y := by
  induction k generalizing x with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv k (fun u => momentIntegral i j u y) =ᶠ[𝓝 x]
            (fun u => momentIntegral (i + k) j u y) := by
        filter_upwards [Ioi_mem_nhds hx] with u hu
        exact ih hu
      calc
        deriv (iteratedDeriv k (fun u => momentIntegral i j u y)) x =
            deriv (fun u => momentIntegral (i + k) j u y) x :=
          heq.deriv_eq
        _ = momentIntegral ((i + k) + 1) j x y :=
          (hasDerivAt_momentIntegral_fst hx hy (i + k) j).deriv
        _ = momentIntegral (i + (k + 1)) j x y := by
          congr 1

private theorem iteratedDeriv_momentIntegral_snd
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (k i j : ℕ) :
    iteratedDeriv k (fun v => momentIntegral i j x v) y =
      momentIntegral i (j + k) x y := by
  induction k generalizing y with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv k (fun v => momentIntegral i j x v) =ᶠ[𝓝 y]
            (fun v => momentIntegral i (j + k) x v) := by
        filter_upwards [Ioi_mem_nhds hy] with v hv
        exact ih hv
      calc
        deriv (iteratedDeriv k (fun v => momentIntegral i j x v)) y =
            deriv (fun v => momentIntegral i (j + k) x v) y :=
          heq.deriv_eq
        _ = momentIntegral i ((j + k) + 1) x y :=
          (hasDerivAt_momentIntegral_snd hx hy i (j + k)).deriv
        _ = momentIntegral i (j + (k + 1)) x y := by
          congr 1

private def betaGamma (p : ℝ × ℝ) : ℝ :=
  Real.Gamma p.1 * Real.Gamma p.2 / Real.Gamma (p.1 + p.2)

private theorem momentIntegral_zero_zero_eq_betaGamma
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    momentIntegral 0 0 x y = betaGamma (x, y) := by
  have hcomplex :
      (momentIntegral 0 0 x y : ℂ) =
        Complex.betaIntegral (x : ℂ) (y : ℂ) := by
    rw [Complex.betaIntegral,
      intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [momentIntegral]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htx :
        (t : ℂ) ^ ((x : ℂ) - 1) =
          (Real.rpow t (x - 1) : ℂ) := by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_cpow ht.1.le (x - 1)).symm
    have hty :
        (1 - (t : ℂ)) ^ ((y : ℂ) - 1) =
          (Real.rpow (1 - t) (y - 1) : ℂ) := by
      rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
      rw [show (y : ℂ) - 1 = ((y - 1 : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le) (y - 1)).symm
    rw [htx, hty]
    simp [momentIntegrand]
  have hformula :=
    Complex.betaIntegral_eq_Gamma_mul_div
      (x : ℂ) (y : ℂ) (by simpa using hx) (by simpa using hy)
  rw [hformula] at hcomplex
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hcomplex
  rw [show (x : ℂ) + (y : ℂ) = ((x + y : ℝ) : ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal] at hcomplex
  apply Complex.ofReal_inj.mp
  simpa only [betaGamma, Prod.fst, Prod.snd, Complex.ofReal_mul,
    Complex.ofReal_div] using hcomplex

private theorem contDiffAt_realGamma_of_pos
    {x : ℝ} (hx : 0 < x) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k Real.Gamma x := by
  let H : Set ℂ := {z | 0 < z.re}
  have hHopen : IsOpen H := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma H := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    change 0 < z.re at hz
    simp only [map_neg, Complex.ofReal_natCast, Complex.neg_re,
      Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hc : ContDiffOn ℂ k Complex.Gamma H :=
    hdiff.contDiffOn hHopen
  have hxH : (x : ℂ) ∈ H := by
    change 0 < (x : ℂ).re
    simpa using hx
  have hcat : ContDiffAt ℂ k Complex.Gamma (x : ℂ) :=
    (hc (x : ℂ) hxH).contDiffAt (hHopen.mem_nhds hxH)
  simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using
    hcat.real_of_complex

private theorem contDiffOn_betaGamma (k : WithTop ℕ∞) :
    ContDiffOn ℝ k betaGamma (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  intro p hp
  have hg₁ :
      ContDiffAt ℝ k (fun q : ℝ × ℝ => Real.Gamma q.1) p :=
    (contDiffAt_realGamma_of_pos hp.1 k).comp p contDiffAt_fst
  have hg₂ :
      ContDiffAt ℝ k (fun q : ℝ × ℝ => Real.Gamma q.2) p :=
    (contDiffAt_realGamma_of_pos hp.2 k).comp p contDiffAt_snd
  have hsum :
      ContDiffAt ℝ k (fun q : ℝ × ℝ => q.1 + q.2) p :=
    contDiffAt_fst.add contDiffAt_snd
  have hg₃ :
      ContDiffAt ℝ k
        (fun q : ℝ × ℝ => Real.Gamma (q.1 + q.2)) p :=
    by
      have hcomp := ContDiffAt.comp (𝕜 := ℝ)
        (g := Real.Gamma) (f := fun q : ℝ × ℝ => q.1 + q.2) p
        (contDiffAt_realGamma_of_pos (add_pos hp.1 hp.2) k) hsum
      simpa only [Function.comp_apply] using hcomp
  have hne : Real.Gamma (p.1 + p.2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hp.1 hp.2)).ne'
  exact ((hg₁.mul hg₂).div hg₃ hne).contDiffWithinAt

private theorem betaFn_eq_momentIntegral (x y : ℝ) :
    betaFn x y = momentIntegral 0 0 x y := by
  unfold betaFn momentIntegral betaIntegrand momentIntegrand
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  simp

private theorem betaFn_eq_betaGamma
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    betaFn x y = betaGamma (x, y) := by
  rw [betaFn_eq_momentIntegral]
  exact momentIntegral_zero_zero_eq_betaGamma hx hy

private theorem momentIntegral_continuousOn_Ici
    (i j : ℕ) (x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ContinuousOn
      (fun p : ℝ × ℝ => momentIntegral i j p.1 p.2)
      (Ici x₀ ×ˢ Ici y₀) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : (ℝ × ℝ) → ℝ → ℝ :=
    fun p t => momentIntegrand i j p.1 p.2 t
  let bound : ℝ → ℝ :=
    fun t => ‖momentIntegrand i j x₀ y₀ t‖
  have hboundInt : Integrable bound μ := by
    exact (momentIntegrable hx₀ hy₀ i j).norm
  have hmain :
      ContinuousOn (fun p => ∫ t, F p t ∂μ)
        (Ici x₀ ×ˢ Ici y₀) := by
    apply continuousOn_of_dominated
    · intro p hp
      exact momentAEStronglyMeasurable i j p.1 p.2
    · intro p hp
      rcases hp with ⟨hpx, hpy⟩
      change x₀ ≤ p.1 at hpx
      change y₀ ≤ p.2 at hpy
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have hs0 : 0 < 1 - t := sub_pos.mpr ht.2
      have hs1 : 1 - t ≤ 1 := by linarith
      have hxpow :
          Real.rpow t (p.1 - 1) ≤
            Real.rpow t (x₀ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht1
          (by linarith)
      have hypow :
          Real.rpow (1 - t) (p.2 - 1) ≤
            Real.rpow (1 - t) (y₀ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hs0 hs1
          (by linarith)
      have hbase :
          Real.rpow t (p.1 - 1) *
              Real.rpow (1 - t) (p.2 - 1) ≤
            Real.rpow t (x₀ - 1) *
              Real.rpow (1 - t) (y₀ - 1) := by
        exact mul_le_mul hxpow hypow
          (Real.rpow_nonneg hs0.le _)
          (Real.rpow_nonneg ht0.le _)
      have hweight :
          0 ≤ |Real.log t| ^ i *
            |Real.log (1 - t)| ^ j := by positivity
      dsimp [F, bound, momentIntegrand]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow]
      rw [abs_of_nonneg (Real.rpow_nonneg ht0.le _),
        abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      calc
        Real.rpow t (p.1 - 1) *
              Real.rpow (1 - t) (p.2 - 1) *
                |Real.log t| ^ i * |Real.log (1 - t)| ^ j =
            (Real.rpow t (p.1 - 1) *
              Real.rpow (1 - t) (p.2 - 1)) *
                (|Real.log t| ^ i *
                  |Real.log (1 - t)| ^ j) := by ring
        _ ≤ (Real.rpow t (x₀ - 1) *
              Real.rpow (1 - t) (y₀ - 1)) *
                (|Real.log t| ^ i *
                  |Real.log (1 - t)| ^ j) :=
          mul_le_mul_of_nonneg_right hbase hweight
        _ = ‖momentIntegrand i j x₀ y₀ t‖ := by
          simp only [momentIntegrand, Real.norm_eq_abs,
            abs_mul, abs_pow]
          have habsx :
              |Real.rpow t (x₀ - 1)| =
                Real.rpow t (x₀ - 1) :=
            abs_of_nonneg (Real.rpow_nonneg ht0.le _)
          have habsy :
              |Real.rpow (1 - t) (y₀ - 1)| =
                Real.rpow (1 - t) (y₀ - 1) :=
            abs_of_nonneg (Real.rpow_nonneg hs0.le _)
          rw [habsx, habsy]
          ring
    · exact hboundInt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hxcont :
          Continuous (fun u : ℝ => Real.rpow t (u - 1)) := by
        rw [continuous_iff_continuousAt]
        intro u
        exact
          (((hasDerivAt_id u).sub_const 1).const_rpow ht.1).continuousAt
      have hycont :
          Continuous (fun v : ℝ =>
            Real.rpow (1 - t) (v - 1)) := by
        rw [continuous_iff_continuousAt]
        intro v
        exact
          (((hasDerivAt_id v).sub_const 1).const_rpow
            (sub_pos.mpr ht.2)).continuousAt
      have hc :
          Continuous (fun p : ℝ × ℝ =>
            momentIntegrand i j p.1 p.2 t) := by
        simpa only [momentIntegrand] using
          (((hxcont.comp continuous_fst).mul
            (hycont.comp continuous_snd)).mul_const
              (Real.log t ^ i) |>.mul_const
                (Real.log (1 - t) ^ j))
      exact hc.continuousOn
  simpa only [momentIntegral, F, μ] using hmain

private theorem partialX_eq_momentIntegral
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    partialX betaFn x y = momentIntegral 1 0 x y := by
  unfold partialX
  have hfun :
      (fun u => betaFn u y) =
        (fun u => momentIntegral 0 0 u y) := by
    funext u
    exact betaFn_eq_momentIntegral u y
  rw [hfun]
  exact (hasDerivAt_momentIntegral_fst hx hy 0 0).deriv

private theorem partialY_eq_momentIntegral
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    partialY betaFn x y = momentIntegral 0 1 x y := by
  unfold partialY
  have hfun :
      (fun v => betaFn x v) =
        (fun v => momentIntegral 0 0 x v) := by
    funext v
    exact betaFn_eq_momentIntegral x v
  rw [hfun]
  exact (hasDerivAt_momentIntegral_snd hx hy 0 0).deriv

theorem gap1 (x y t x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < betaIntegrand t x y := by
  unfold betaIntegrand
  exact mul_pos
    (Real.rpow_pos_of_pos ht.1 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _)

theorem gap2 (x y t x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    betaIntegrand t x y ≤ betaIntegrand t x₀ y₀ := by
  unfold betaIntegrand
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le
      (by linarith))
    (Real.rpow_le_rpow_of_exponent_ge
      (sub_pos.mpr ht.2) (by linarith [ht.1])
      (by linarith))
    (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _)
    (Real.rpow_nonneg ht.1.le _)

theorem gap3 (x y t x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < betaIntegrand t x₀ y₀ := by
  exact gap1 x₀ y₀ t x₀ y₀ hx₀ hy₀ le_rfl le_rfl ht

theorem gap4 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    IntervalIntegrable (fun t => betaIntegrand t x₀ y₀)
      volume (0 : ℝ) 1 := by
  apply
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      zero_le_one).2
  simpa only [betaIntegrand] using
    (betaKernel_integrableOn hx₀ hy₀)

theorem gap5 (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ContinuousOn
      (fun p : ℝ × ℝ => betaFn p.1 p.2)
      (Set.Ici x₀ ×ˢ Set.Ici y₀) := by
  exact
    (momentIntegral_continuousOn_Ici 0 0 x₀ y₀ hx₀ hy₀).congr
      (fun p _ => betaFn_eq_momentIntegral p.1 p.2)

theorem gap6 :
    ContinuousOn
      (fun p : ℝ × ℝ => betaFn p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  exact (contDiffOn_betaGamma 0).continuousOn.congr
    (fun p hp => betaFn_eq_betaGamma hp.1 hp.2)

theorem gap7 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t in (0 : ℝ)..1,
        deriv (fun u => betaIntegrand t u y) x) =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y * Real.log t := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  unfold betaIntegrand
  have hd :=
    (((hasDerivAt_id x).sub_const 1).const_rpow ht.1).mul_const
      (Real.rpow (1 - t) (y - 1))
  have hderiv := hd.deriv
  convert hderiv using 1 <;>
    simp only [Real.rpow_eq_pow, id_eq] <;>
    ring

theorem gap8 (x y t x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |betaIntegrand t x y * Real.log t| ≤
      betaIntegrand t x₀ y₀ * |Real.log t| := by
  rw [abs_mul, abs_of_pos
    (gap1 x y t x₀ y₀ hx₀ hy₀ hx hy ht)]
  exact mul_le_mul_of_nonneg_right
    (gap2 x y t x₀ y₀ hx₀ hy₀ hx hy ht)
    (abs_nonneg _)

theorem gap9 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    IntervalIntegrable
      (fun t => betaIntegrand t x₀ y₀ * |Real.log t|)
      volume (0 : ℝ) 1 := by
  apply
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      zero_le_one).2
  have h := (momentIntegrable hx₀ hy₀ 1 0).norm
  refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
  intro t ht
  have htx :
      |Real.rpow t (x₀ - 1)| =
        Real.rpow t (x₀ - 1) :=
    abs_of_pos (Real.rpow_pos_of_pos ht.1 _)
  have hty :
      |Real.rpow (1 - t) (y₀ - 1)| =
        Real.rpow (1 - t) (y₀ - 1) :=
    abs_of_pos
      (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _)
  unfold momentIntegrand betaIntegrand
  simp only [pow_one, pow_zero, mul_one, Real.norm_eq_abs,
    abs_mul, htx, hty]

private theorem neg_rpow_mul_log_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun t : ℝ => -(Real.rpow t a * Real.log t))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero ha
  have hfun :
      (fun t : ℝ => -(Real.rpow t a * Real.log t)) =
        (fun t : ℝ => -(Real.log t * t ^ a)) := by
    funext t
    rw [Real.rpow_eq_pow]
    ring
  rw [hfun]
  simpa using h.neg

private theorem neg_one_sub_rpow_mul_log_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun t : ℝ =>
        -(Real.rpow (1 - t) a * Real.log t))
      (nhdsWithin 1 (Iio 1)) (nhds 0) := by
  have hsub :
      Tendsto (fun t : ℝ => 1 - t)
        (nhdsWithin 1 (Iio 1)) (nhds 0) := by
    have hc :
        ContinuousAt (fun t : ℝ => 1 - t) 1 :=
      continuousAt_const.sub continuousAt_id
    simpa only [sub_self] using
      hc.tendsto.mono_left inf_le_left
  have hpow :
      Tendsto (fun t : ℝ => Real.rpow (1 - t) a)
        (nhdsWithin 1 (Iio 1)) (nhds 0) := by
    simpa only [Function.comp_apply, Real.zero_rpow ha.ne'] using
      (Real.continuousAt_rpow_const 0 a
        (Or.inr ha.le)).tendsto.comp hsub
  have hlog :
      Tendsto (fun t : ℝ => Real.log t)
        (nhdsWithin 1 (Iio 1)) (nhds 0) := by
    simpa using
      (Real.continuousAt_log one_ne_zero).tendsto.mono_left
        inf_le_left
  simpa using (hpow.mul hlog).neg

private theorem left_scaled_tendsto_zero
    {x₀ y₀ : ℝ} (hx₀ : 0 < x₀) :
    Tendsto
      (fun t =>
        Real.rpow t (1 - x₀ / 2) *
          betaIntegrand t x₀ y₀ * |Real.log t|)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hg :
      Tendsto
        (fun t : ℝ =>
          -(Real.rpow t (x₀ / 2) * Real.log t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    neg_rpow_mul_log_tendsto_zero (half_pos hx₀)
  have hfac :
      Tendsto (fun t : ℝ =>
          Real.rpow (1 - t) (y₀ - 1))
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hc :
        ContinuousAt (fun t : ℝ =>
          Real.rpow (1 - t) (y₀ - 1)) 0 :=
      by
        have hout :
            ContinuousAt (fun z : ℝ =>
              Real.rpow z (y₀ - 1)) 1 :=
          Real.continuousAt_rpow_const 1 (y₀ - 1)
            (Or.inl one_ne_zero)
        have hin :
            ContinuousAt (fun t : ℝ => 1 - t) 0 :=
          continuousAt_const.sub continuousAt_id
        simpa only [Function.comp_apply] using
          (ContinuousAt.comp_of_eq hout hin (by norm_num))
    simpa using hc.tendsto.mono_left inf_le_left
  have hprod :
      Tendsto
        (fun t : ℝ =>
          (-(Real.rpow t (x₀ / 2) * Real.log t)) *
            Real.rpow (1 - t) (y₀ - 1))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hg.mul hfac
  refine hprod.congr' ?_
  have hlt :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_mem_nhdsWithin, hlt] with t ht0 ht1
  have hlog : Real.log t ≤ 0 :=
    Real.log_nonpos ht0.le ht1.le
  unfold betaIntegrand
  rw [abs_of_nonpos hlog]
  have hpow :
      Real.rpow t (1 - x₀ / 2) *
          Real.rpow t (x₀ - 1) =
        Real.rpow t (x₀ / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add ht0
      (1 - x₀ / 2) (x₀ - 1)]
    congr 1
    ring
  rw [← hpow]
  ring

private theorem right_scaled_tendsto_zero
    {x₀ y₀ : ℝ} (hy₀ : 0 < y₀) :
    Tendsto
      (fun t =>
        Real.rpow (1 - t) (1 - y₀ / 2) *
          betaIntegrand t x₀ y₀ * |Real.log t|)
      (nhdsWithin 1 (Iio 1)) (nhds 0) := by
  have hg :
      Tendsto
        (fun t : ℝ =>
          -(Real.rpow (1 - t) (y₀ / 2) * Real.log t))
        (nhdsWithin 1 (Iio 1)) (nhds 0) :=
    neg_one_sub_rpow_mul_log_tendsto_zero (half_pos hy₀)
  have hfac :
      Tendsto (fun t : ℝ => Real.rpow t (x₀ - 1))
        (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    have hc :
        ContinuousAt (fun t : ℝ =>
          Real.rpow t (x₀ - 1)) 1 :=
      Real.continuousAt_rpow_const 1 (x₀ - 1)
        (Or.inl one_ne_zero)
    simpa using hc.tendsto.mono_left inf_le_left
  have hprod :
      Tendsto
        (fun t : ℝ =>
          (-(Real.rpow (1 - t) (y₀ / 2) *
            Real.log t)) * Real.rpow t (x₀ - 1))
        (nhdsWithin 1 (Iio 1)) (nhds 0) := by
    simpa using hg.mul hfac
  refine hprod.congr' ?_
  have hgt :
      ∀ᶠ t : ℝ in nhdsWithin 1 (Iio 1), 0 < t :=
    Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_mem_nhdsWithin, hgt] with t ht1 ht0
  have hlog : Real.log t ≤ 0 :=
    Real.log_nonpos ht0.le ht1.le
  have hs0 : 0 < 1 - t := sub_pos.mpr ht1
  unfold betaIntegrand
  rw [abs_of_nonpos hlog]
  have hpow :
      Real.rpow (1 - t) (1 - y₀ / 2) *
          Real.rpow (1 - t) (y₀ - 1) =
        Real.rpow (1 - t) (y₀ / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hs0
      (1 - y₀ / 2) (y₀ - 1)]
    congr 1
    ring
  rw [← hpow]
  ring

private theorem tendsto_iff_of_both_zero
    {α : Type*} {l : Filter α} [l.NeBot]
    {f g : α → ℝ} {L : ℝ}
    (hf : Tendsto f l (nhds 0))
    (hg : Tendsto g l (nhds 0)) :
    Tendsto f l (nhds L) ↔ Tendsto g l (nhds L) := by
  constructor
  · intro hfL
    have hL : L = 0 := tendsto_nhds_unique hfL hf
    subst L
    exact hg
  · intro hgL
    have hL : L = 0 := tendsto_nhds_unique hgL hg
    subst L
    exact hf

theorem gap10 (x y x₀ y₀ L : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
        (fun t =>
          Real.rpow t (1 - x₀ / 2) *
            betaIntegrand t x₀ y₀ * |Real.log t|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun t => -(Real.rpow t (x₀ / 2) * Real.log t))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  exact tendsto_iff_of_both_zero
    (left_scaled_tendsto_zero hx₀)
    (neg_rpow_mul_log_tendsto_zero (half_pos hx₀))

theorem gap11 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
      (fun t => -(Real.rpow t (x₀ / 2) * Real.log t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact neg_rpow_mul_log_tendsto_zero (half_pos hx₀)

theorem gap12 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
      (fun t =>
        Real.rpow t (1 - x₀ / 2) *
          betaIntegrand t x₀ y₀ * |Real.log t|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact left_scaled_tendsto_zero hx₀

theorem gap13 (x y x₀ y₀ L : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
        (fun t =>
          Real.rpow (1 - t) (1 - y₀ / 2) *
            betaIntegrand t x₀ y₀ * |Real.log t|)
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) ↔
      Tendsto
        (fun t =>
          -(Real.rpow (1 - t) (y₀ / 2) * Real.log t))
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) := by
  exact tendsto_iff_of_both_zero
    (right_scaled_tendsto_zero hy₀)
    (neg_one_sub_rpow_mul_log_tendsto_zero (half_pos hy₀))

theorem gap14 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
      (fun t =>
        -(Real.rpow (1 - t) (y₀ / 2) * Real.log t))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  exact neg_one_sub_rpow_mul_log_tendsto_zero (half_pos hy₀)

theorem gap15 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    Tendsto
      (fun t =>
        Real.rpow (1 - t) (1 - y₀ / 2) *
          betaIntegrand t x₀ y₀ * |Real.log t|)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  exact right_scaled_tendsto_zero hy₀

private theorem momentIntegral_eq_interval
    (i j : ℕ) (x y : ℝ) :
    momentIntegral i j x y =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y *
          Real.log t ^ i * Real.log (1 - t) ^ j := by
  unfold momentIntegral momentIntegrand betaIntegrand
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

private theorem iterPartialX_eq_iteratedDeriv
    (n : ℕ) (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    iterPartialX n f x y =
      iteratedDeriv n (fun u => f u y) x := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      rw [iterPartialX, partialX, iteratedDeriv_succ]
      congr 1
      funext u
      exact ih u y

private theorem iterPartialY_eq_iteratedDeriv
    (n : ℕ) (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    iterPartialY n f x y =
      iteratedDeriv n (fun v => f x v) y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      rw [iterPartialY, partialY, iteratedDeriv_succ]
      congr 1
      funext v
      exact ih x v

private theorem partialX_continuousOn_Ici
    (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ContinuousOn
      (fun p : ℝ × ℝ => partialX betaFn p.1 p.2)
      (Ici x₀ ×ˢ Ici y₀) := by
  exact
    (momentIntegral_continuousOn_Ici 1 0 x₀ y₀ hx₀ hy₀).congr
      (fun p hp => by
        rcases hp with ⟨hpx, hpy⟩
        exact partialX_eq_momentIntegral
          (lt_of_lt_of_le hx₀ hpx)
          (lt_of_lt_of_le hy₀ hpy))

private theorem partialY_continuousOn_Ici
    (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ContinuousOn
      (fun p : ℝ × ℝ => partialY betaFn p.1 p.2)
      (Ici x₀ ×ˢ Ici y₀) := by
  exact
    (momentIntegral_continuousOn_Ici 0 1 x₀ y₀ hx₀ hy₀).congr
      (fun p hp => by
        rcases hp with ⟨hpx, hpy⟩
        exact partialY_eq_momentIntegral
          (lt_of_lt_of_le hx₀ hpx)
          (lt_of_lt_of_le hy₀ hpy))

private theorem continuousOn_positive_of_continuousOn_Ici
    (f : ℝ × ℝ → ℝ)
    (h : ∀ x₀ y₀ : ℝ, 0 < x₀ → 0 < y₀ →
      ContinuousOn f (Ici x₀ ×ˢ Ici y₀)) :
    ContinuousOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  intro p hp
  rcases hp with ⟨hpxpos, hpypos⟩
  change 0 < p.1 at hpxpos
  change 0 < p.2 at hpypos
  let x₀ : ℝ := p.1 / 2
  let y₀ : ℝ := p.2 / 2
  have hx₀ : 0 < x₀ := by
    dsimp [x₀]
    exact half_pos hpxpos
  have hy₀ : 0 < y₀ := by
    dsimp [y₀]
    exact half_pos hpypos
  have hpx : x₀ < p.1 := by
    dsimp [x₀]
    linarith
  have hpy : y₀ < p.2 := by
    dsimp [y₀]
    linarith
  have hpclosed : p ∈ Ici x₀ ×ˢ Ici y₀ :=
    ⟨hpx.le, hpy.le⟩
  have hopen :
      IsOpen (Ioi x₀ ×ˢ Ioi y₀) :=
    isOpen_Ioi.prod isOpen_Ioi
  have hopenMem :
      Ioi x₀ ×ˢ Ioi y₀ ∈ nhds p :=
    hopen.mem_nhds ⟨hpx, hpy⟩
  have hclosedMem :
      Ici x₀ ×ˢ Ici y₀ ∈ nhds p :=
    Filter.mem_of_superset hopenMem
      (by
        rintro q ⟨hqx, hqy⟩
        change x₀ < q.1 at hqx
        change y₀ < q.2 at hqy
        exact ⟨hqx.le, hqy.le⟩)
  exact ((h x₀ y₀ hx₀ hy₀) p hpclosed).continuousAt
    hclosedMem |>.continuousWithinAt

theorem gap16 (x y x₀ y₀ : ℝ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    partialX betaFn x y =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y * Real.log t := by
  rw [partialX_eq_momentIntegral
    (lt_of_lt_of_le hx₀ hx) (lt_of_lt_of_le hy₀ hy),
    momentIntegral_eq_interval]
  simp

theorem gap17 (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ContinuousOn
      (fun p : ℝ × ℝ => partialX betaFn p.1 p.2)
      (Set.Ici x₀ ×ˢ Set.Ici y₀) := by
  exact partialX_continuousOn_Ici x₀ y₀ hx₀ hy₀

theorem gap18 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    partialX betaFn x y =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y * Real.log t := by
  exact gap16 x y x y hx hy le_rfl le_rfl

theorem gap19 :
    ContinuousOn
      (fun p : ℝ × ℝ => partialX betaFn p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  apply continuousOn_positive_of_continuousOn_Ici
  exact fun x₀ y₀ hx₀ hy₀ =>
    partialX_continuousOn_Ici x₀ y₀ hx₀ hy₀

theorem gap20 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    partialY betaFn x y =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y * Real.log (1 - t) := by
  rw [partialY_eq_momentIntegral hx hy,
    momentIntegral_eq_interval]
  simp

theorem gap21 :
    ContinuousOn
      (fun p : ℝ × ℝ => partialY betaFn p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  apply continuousOn_positive_of_continuousOn_Ici
  exact fun x₀ y₀ hx₀ hy₀ =>
    partialY_continuousOn_Ici x₀ y₀ hx₀ hy₀

theorem gap22 (x y : ℝ) (n i : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hn : 0 < n) (hi : i ≤ n) :
    iterPartialY (n - i) (iterPartialX i betaFn) x y =
      ∫ t in (0 : ℝ)..1,
        betaIntegrand t x y *
          Real.log t ^ i * Real.log (1 - t) ^ (n - i) := by
  rw [iterPartialY_eq_iteratedDeriv]
  have hinner :
      (fun v => iterPartialX i betaFn x v) =ᶠ[nhds y]
        (fun v => momentIntegral i 0 x v) := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    rw [iterPartialX_eq_iteratedDeriv]
    have hfun :
        (fun u => betaFn u v) =
          (fun u => momentIntegral 0 0 u v) := by
      funext u
      exact betaFn_eq_momentIntegral u v
    rw [hfun]
    simpa only [Nat.zero_add] using
      (iteratedDeriv_momentIntegral_fst hx hv i 0 0)
  calc
    iteratedDeriv (n - i)
        (fun v => iterPartialX i betaFn x v) y =
      iteratedDeriv (n - i)
        (fun v => momentIntegral i 0 x v) y :=
      hinner.iteratedDeriv_eq (n - i)
    _ = momentIntegral i (n - i) x y := by
      simpa only [Nat.zero_add] using
        (iteratedDeriv_momentIntegral_snd
          hx hy (n - i) i 0)
    _ = _ := momentIntegral_eq_interval i (n - i) x y

theorem gap23 :
    ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => betaFn p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  exact (contDiffOn_betaGamma (⊤ : WithTop ℕ∞)).congr
    (fun p hp => betaFn_eq_betaGamma hp.1 hp.2)

theorem gap24 :
    ContinuousOn
        (fun p : ℝ × ℝ => betaFn p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
      ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => betaFn p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  exact ⟨gap6, gap23⟩

end

end ProofGap.Exercise3842
