import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital

namespace ProofGap.Exercise1373

noncomputable section

open Filter

def puncturedZero : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f

def symmetricNumerator (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + h) + f (x - h) - 2 * f x

def symmetricQuotient (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  symmetricNumerator f x h / h ^ 2

def derivativeQuotient (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (deriv f (x + h) - deriv f (x - h)) / (2 * h)

def averagedDerivativeQuotient (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((deriv f (x + h) - deriv f x) / h +
      (deriv f (x - h) - deriv f x) / (-h))

def SameLimitAtZero (u v : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, Tendsto u puncturedZero (nhds L) ↔
    Tendsto v puncturedZero (nhds L)

private theorem continuous_symmetricNumerator (f : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x) :
    Tendsto (symmetricNumerator f x) (nhds 0) (nhds 0) := by
  have hpa : Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x)).add tendsto_id using 1 <;> ring
  have hma : Tendsto (fun h : ℝ => x - h) (nhds 0) (nhds x) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x)).sub tendsto_id using 1 <;> ring
  have hp : Tendsto (fun h : ℝ => f (x + h)) (nhds 0) (nhds (f x)) :=
    Tendsto.comp hf hpa
  have hm : Tendsto (fun h : ℝ => f (x - h)) (nhds 0) (nhds (f x)) :=
    Tendsto.comp hf hma
  convert
    (hp.add hm).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => 2 * f x) (nhds 0) (nhds (2 * f x))) using 1 <;>
    simp <;> ring

private theorem square_tendsto_zero :
    Tendsto (fun h : ℝ => h ^ 2) (nhds 0) (nhds 0) := by
  simpa using ((tendsto_id :
    Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)).pow 2)

private theorem neg_tendsto_punctured :
    Tendsto (fun h : ℝ => -h) puncturedZero puncturedZero := by
  rw [puncturedZero, tendsto_nhdsWithin_iff]
  constructor
  · simpa using ((continuousAt_id.neg :
      ContinuousAt (fun h : ℝ => -h) 0).mono_left inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh

private theorem quotient_eventually_eq (f : ℝ → ℝ) (x : ℝ) :
    derivativeQuotient f x =ᶠ[puncturedZero]
      averagedDerivativeQuotient f x := by
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  simp only [derivativeQuotient, averagedDerivativeQuotient]
  field_simp
  ring

private theorem second_deriv_slope (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (fun h : ℝ => (deriv f (x + h) - deriv f x) / h)
      puncturedZero (nhds (iterDeriv 2 f x)) := by
  have hcd : ContDiffAt ℝ 1 (deriv f) x :=
    hf.derivWithin (m := 1) (by norm_num)
  have hd : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    hcd.differentiableAt_one.hasDerivAt
  simpa [puncturedZero, div_eq_inv_mul, iterDeriv] using
    hd.tendsto_slope_zero

private theorem second_deriv_slope_neg (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (fun h : ℝ => (deriv f (x - h) - deriv f x) / (-h))
      puncturedZero (nhds (iterDeriv 2 f x)) := by
  have h := (second_deriv_slope f x hf).comp neg_tendsto_punctured
  simpa [sub_eq_add_neg] using h

private theorem average_limit (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (averagedDerivativeQuotient f x) puncturedZero
      (nhds ((1 / 2 : ℝ) * (iterDeriv 2 f x + iterDeriv 2 f x))) := by
  change Tendsto
    (fun h : ℝ => (1 / 2 : ℝ) *
      ((deriv f (x + h) - deriv f x) / h +
        (deriv f (x - h) - deriv f x) / (-h)))
    puncturedZero
    (nhds ((1 / 2 : ℝ) * (iterDeriv 2 f x + iterDeriv 2 f x)))
  exact
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) puncturedZero
        (nhds (1 / 2 : ℝ))).mul
      ((second_deriv_slope f x hf).add (second_deriv_slope_neg f x hf))

private theorem derivative_limit (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (derivativeQuotient f x) puncturedZero
      (nhds (iterDeriv 2 f x)) := by
  have hav := average_limit f x hf
  have hav' : Tendsto (averagedDerivativeQuotient f x) puncturedZero
      (nhds (iterDeriv 2 f x)) := by
    convert hav using 1 <;> ring
  exact hav'.congr' (quotient_eventually_eq f x).symm

private theorem numerator_hasDerivAt (f : ℝ → ℝ) (x h : ℝ)
    (hp : DifferentiableAt ℝ f (x + h))
    (hm : DifferentiableAt ℝ f (x - h)) :
    HasDerivAt (symmetricNumerator f x)
      (deriv f (x + h) - deriv f (x - h)) h := by
  have hap : HasDerivAt (fun t : ℝ => f (x + t))
      (deriv f (x + h)) h := by
    convert hp.hasDerivAt.comp h
      ((hasDerivAt_const h x).add (hasDerivAt_id h)) using 1 <;> ring
  have ham : HasDerivAt (fun t : ℝ => f (x - t))
      (-deriv f (x - h)) h := by
    convert hm.hasDerivAt.comp h
      ((hasDerivAt_const h x).sub (hasDerivAt_id h)) using 1 <;> ring
  convert (hap.add ham).sub (hasDerivAt_const h (2 * f x)) using 1 <;>
    simp <;> ring

private theorem denominator_hasDerivAt (h : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * h) h := by
  simpa using (hasDerivAt_pow 2 h)

private theorem symmetric_limit (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (symmetricQuotient f x) puncturedZero
      (nhds (iterDeriv 2 f x)) := by
  have hpz : puncturedZero ≤ nhds 0 := nhdsWithin_le_nhds
  have hpa : Tendsto (fun h : ℝ => x + h) puncturedZero (nhds x) := by
    have hbase : Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x)).add tendsto_id using 1 <;> ring
    exact hbase.mono_left hpz
  have hma : Tendsto (fun h : ℝ => x - h) puncturedZero (nhds x) := by
    have hbase : Tendsto (fun h : ℝ => x - h) (nhds 0) (nhds x) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => x) (nhds 0) (nhds x)).sub tendsto_id using 1 <;> ring
    exact hbase.mono_left hpz
  have hlocal : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y :=
    hf.eventually (by norm_num)
  have hdiff : ∀ᶠ h in puncturedZero,
      HasDerivAt (symmetricNumerator f x)
        (deriv f (x + h) - deriv f (x - h)) h := by
    filter_upwards [hpa.eventually hlocal, hma.eventually hlocal] with h hp hm
    exact numerator_hasDerivAt f x h
      (hp.differentiableAt (by decide)) (hm.differentiableAt (by decide))
  have hdenom : ∀ᶠ h in puncturedZero,
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * h) h :=
    Eventually.of_forall denominator_hasDerivAt
  have hdenom_ne : ∀ᶠ h in puncturedZero, 2 * h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero (by norm_num) (by simpa using hh)
  have hnum0 : Tendsto (symmetricNumerator f x) puncturedZero (nhds 0) :=
    (continuous_symmetricNumerator f x hf.continuousAt).mono_left hpz
  have hdenom0 : Tendsto (fun h : ℝ => h ^ 2) puncturedZero (nhds 0) :=
    square_tendsto_zero.mono_left hpz
  have hdiv : Tendsto
      (fun h : ℝ => (deriv f (x + h) - deriv f (x - h)) / (2 * h))
      puncturedZero (nhds (iterDeriv 2 f x)) :=
    derivative_limit f x hf
  change Tendsto
    (fun h : ℝ => symmetricNumerator f x h / h ^ 2)
    puncturedZero (nhds (iterDeriv 2 f x))
  exact HasDerivAt.lhopital_zero_nhdsNE
    hdiff hdenom hdenom_ne hnum0 hdenom0 hdiv

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hf : ContinuousAt f x) :
    Tendsto (symmetricNumerator f x) (nhds 0) (nhds 0) := by
  exact continuous_symmetricNumerator f x hf

theorem gap2 :
    Tendsto (fun h : ℝ => h ^ 2) (nhds 0) (nhds 0) := by
  exact square_tendsto_zero

theorem gap3 (h : ℝ) (hh : h ≠ 0) :
    2 * h ≠ 0 := by
  exact mul_ne_zero (by norm_num) hh

theorem gap4 (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    SameLimitAtZero (symmetricQuotient f x) (derivativeQuotient f x) := by
  haveI : NeBot puncturedZero := by
    unfold puncturedZero
    exact NormedField.nhdsNE_neBot 0
  intro L
  constructor
  · intro hs
    have hL : L = iterDeriv 2 f x :=
      tendsto_nhds_unique hs (symmetric_limit f x hf)
    rw [hL]
    exact derivative_limit f x hf
  · intro hd
    have hL : L = iterDeriv 2 f x :=
      tendsto_nhds_unique hd (derivative_limit f x hf)
    rw [hL]
    exact symmetric_limit f x hf

theorem gap5 (f : ℝ → ℝ) (x : ℝ) :
    SameLimitAtZero (derivativeQuotient f x)
      (averagedDerivativeQuotient f x) := by
  intro L
  exact tendsto_congr' (quotient_eventually_eq f x)

theorem gap6 (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (averagedDerivativeQuotient f x) puncturedZero
      (nhds ((1 / 2 : ℝ) * (iterDeriv 2 f x + iterDeriv 2 f x))) := by
  exact average_limit f x hf

theorem gap7 (f : ℝ → ℝ) (x : ℝ) :
    (1 / 2 : ℝ) * (iterDeriv 2 f x + iterDeriv 2 f x) =
      iterDeriv 2 f x := by
  ring

theorem gap8 (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (derivativeQuotient f x) puncturedZero
      (nhds (iterDeriv 2 f x)) := by
  exact derivative_limit f x hf

theorem gap9 (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (symmetricQuotient f x) puncturedZero
      (nhds (iterDeriv 2 f x)) := by
  exact symmetric_limit f x hf

end

end ProofGap.Exercise1373
