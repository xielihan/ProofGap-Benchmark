import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2847

noncomputable section

def powerSelf (x : ℝ) : ℝ :=
  Real.rpow x x

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def taylorAtOneTerm (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  iterDeriv n f 1 / (Nat.factorial n : ℝ) * (x - 1) ^ n

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) :
    f 1 = 1 := by
  rw [hf]
  simp [powerSelf]

theorem gap2
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1) :
    ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x) := by
  intro x hx
  have heq : f = powerSelf := funext hf
  rw [heq]
  have hd := (hasDerivAt_id x).rpow (hasDerivAt_id x) hx
  have hpow : x * Real.rpow x (x - 1) = Real.rpow x x := by
    calc
      x * Real.rpow x (x - 1) = Real.rpow x (x - 1) * x := by ring
      _ = Real.rpow x (x - 1) * Real.rpow x 1 := by simp
      _ = Real.rpow x ((x - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = Real.rpow x x := by ring_nf
  have hder :
      deriv (fun y : ℝ => Real.rpow y y) x =
        1 * x * Real.rpow x (x - 1) +
          1 * Real.rpow x x * Real.log x := by
    simpa only [id_eq] using hd.deriv
  change deriv (fun y : ℝ => Real.rpow y y) x = _
  rw [hder, powerSelf]
  simp only [one_mul]
  rw [hpow]
  ring

theorem gap3
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x)) :
    deriv f 1 = 1 := by
  rw [hderiv 1 one_pos]
  simp [powerSelf]

theorem gap4
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1) :
    ∀ x, 0 < x →
      iterDeriv 2 f x =
        powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1) := by
  intro x hx
  have hevent : ∀ᶠ y : ℝ in nhds x, 0 < y := isOpen_Ioi.mem_nhds hx
  have heq :
      (fun y => deriv f y) =ᶠ[nhds x]
        (fun y => powerSelf y * (1 + Real.log y)) := by
    filter_upwards [hevent] with y hy
    exact hderiv y hy
  have hpow : x * Real.rpow x (x - 1) = Real.rpow x x := by
    calc
      x * Real.rpow x (x - 1) = Real.rpow x (x - 1) * x := by ring
      _ = Real.rpow x (x - 1) * Real.rpow x 1 := by simp
      _ = Real.rpow x ((x - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = Real.rpow x x := by ring_nf
  have hp : HasDerivAt powerSelf (powerSelf x * (1 + Real.log x)) x := by
    have hd := (hasDerivAt_id x).rpow (hasDerivAt_id x) hx
    have hcoef :
        1 * x * Real.rpow x (x - 1) +
            1 * Real.rpow x x * Real.log x =
          powerSelf x * (1 + Real.log x) := by
      simp only [one_mul]
      rw [hpow]
      unfold powerSelf
      ring
    change HasDerivAt (fun y : ℝ => Real.rpow y y)
      (powerSelf x * (1 + Real.log x)) x
    convert hd using 1
    simpa only [id_eq] using hcoef.symm
  have hlog : HasDerivAt (fun y : ℝ => 1 + Real.log y) (1 / x) x := by
    convert (hasDerivAt_const x 1).add (Real.hasDerivAt_log hx.ne') using 1 <;> ring
  have hprod := hp.mul hlog
  have hdiv : powerSelf x / x = Real.rpow x (x - 1) := by
    unfold powerSelf
    apply (div_eq_iff hx.ne').2
    calc
      Real.rpow x x = x * Real.rpow x (x - 1) := hpow.symm
      _ = Real.rpow x (x - 1) * x := by ring
  change deriv (fun y => deriv f y) x = _
  calc
    deriv (fun y => deriv f y) x =
        deriv (fun y => powerSelf y * (1 + Real.log y)) x := heq.deriv_eq
    _ = powerSelf x * (1 + Real.log x) * (1 + Real.log x) +
        powerSelf x * (1 / x) := hprod.deriv
    _ = powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1) := by
      rw [show powerSelf x * (1 / x) = powerSelf x / x by ring, hdiv]
      ring

theorem gap5
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1)
    (hsecond :
      ∀ x, 0 < x →
        iterDeriv 2 f x =
          powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1)) :
    iterDeriv 2 f 1 = 2 := by
  rw [hsecond 1 one_pos]
  norm_num [powerSelf]

theorem gap6
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1)
    (hsecond :
      ∀ x, 0 < x →
        iterDeriv 2 f x =
          powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1))
    (hsecond1 : iterDeriv 2 f 1 = 2) :
    ∀ x, 0 < x →
      iterDeriv 3 f x =
        powerSelf x * (1 + Real.log x) ^ 3 +
          2 * Real.rpow x (x - 1) * (1 + Real.log x) +
          Real.rpow x (x - 1) * (Real.log x + (x - 1) / x) := by
  intro x hx
  have hevent : ∀ᶠ y : ℝ in nhds x, 0 < y := isOpen_Ioi.mem_nhds hx
  have heq :
      (fun y => iterDeriv 2 f y) =ᶠ[nhds x]
        (fun y =>
          powerSelf y * (1 + Real.log y) ^ 2 + Real.rpow y (y - 1)) := by
    filter_upwards [hevent] with y hy
    exact hsecond y hy
  have hpow : x * Real.rpow x (x - 1) = Real.rpow x x := by
    calc
      x * Real.rpow x (x - 1) = Real.rpow x (x - 1) * x := by ring
      _ = Real.rpow x (x - 1) * Real.rpow x 1 := by simp
      _ = Real.rpow x ((x - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = Real.rpow x x := by ring_nf
  have hp : HasDerivAt powerSelf (powerSelf x * (1 + Real.log x)) x := by
    have hd := (hasDerivAt_id x).rpow (hasDerivAt_id x) hx
    have hcoef :
        1 * x * Real.rpow x (x - 1) +
            1 * Real.rpow x x * Real.log x =
          powerSelf x * (1 + Real.log x) := by
      simp only [one_mul]
      rw [hpow]
      unfold powerSelf
      ring
    change HasDerivAt (fun y : ℝ => Real.rpow y y)
      (powerSelf x * (1 + Real.log x)) x
    convert hd using 1
    simpa only [id_eq] using hcoef.symm
  have hlog : HasDerivAt (fun y : ℝ => 1 + Real.log y) (1 / x) x := by
    convert (hasDerivAt_const x 1).add (Real.hasDerivAt_log hx.ne') using 1 <;> ring
  have hfirst := hp.mul (hlog.pow 2)
  have hpow2 : x * Real.rpow x (x - 2) = Real.rpow x (x - 1) := by
    calc
      x * Real.rpow x (x - 2) = Real.rpow x (x - 2) * x := by ring
      _ = Real.rpow x (x - 2) * Real.rpow x 1 := by simp
      _ = Real.rpow x ((x - 2) + 1) := (Real.rpow_add hx _ _).symm
      _ = Real.rpow x (x - 1) := by ring_nf
  have htailcoef :
      1 * (x - 1) * Real.rpow x ((x - 1) - 1) +
          1 * Real.rpow x (x - 1) * Real.log x =
        Real.rpow x (x - 1) * (Real.log x + (x - 1) / x) := by
    have hdiv2 : Real.rpow x (x - 2) = Real.rpow x (x - 1) / x := by
      apply (eq_div_iff hx.ne').2
      simpa [mul_comm] using hpow2
    rw [show (x - 1) - 1 = x - 2 by ring, hdiv2]
    ring
  have htail : HasDerivAt (fun y : ℝ => Real.rpow y (y - 1))
      (Real.rpow x (x - 1) * (Real.log x + (x - 1) / x)) x := by
    have hd := (hasDerivAt_id x).rpow ((hasDerivAt_id x).sub_const 1) hx
    convert hd using 1
    simpa only [id_eq, one_mul] using htailcoef.symm
  have hsum := hfirst.add htail
  have hdiv : powerSelf x / x = Real.rpow x (x - 1) := by
    unfold powerSelf
    apply (div_eq_iff hx.ne').2
    calc
      Real.rpow x x = x * Real.rpow x (x - 1) := hpow.symm
      _ = Real.rpow x (x - 1) * x := by ring
  change deriv (fun y => iterDeriv 2 f y) x = _
  calc
    deriv (fun y => iterDeriv 2 f y) x =
        deriv (fun y =>
          powerSelf y * (1 + Real.log y) ^ 2 +
            Real.rpow y (y - 1)) x := heq.deriv_eq
    _ = (powerSelf x * (1 + Real.log x) * (1 + Real.log x) ^ 2 +
          powerSelf x * (2 * (1 + Real.log x) ^ (2 - 1) * (1 / x))) +
        Real.rpow x (x - 1) * (Real.log x + (x - 1) / x) := hsum.deriv
    _ = powerSelf x * (1 + Real.log x) ^ 3 +
          2 * Real.rpow x (x - 1) * (1 + Real.log x) +
          Real.rpow x (x - 1) * (Real.log x + (x - 1) / x) := by
      norm_num
      have hinv : powerSelf x * x⁻¹ = Real.rpow x (x - 1) := by
        simpa [div_eq_mul_inv] using hdiv
      rw [show
        powerSelf x * (2 * (1 + Real.log x) * x⁻¹) =
          2 * (powerSelf x * x⁻¹) * (1 + Real.log x) by ring, hinv]
      rw [← Real.rpow_eq_pow x (x - 1)]
      ring

theorem gap7
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1)
    (hsecond :
      ∀ x, 0 < x →
        iterDeriv 2 f x =
          powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1))
    (hsecond1 : iterDeriv 2 f 1 = 2)
    (hthird :
      ∀ x, 0 < x →
        iterDeriv 3 f x =
          powerSelf x * (1 + Real.log x) ^ 3 +
            2 * Real.rpow x (x - 1) * (1 + Real.log x) +
            Real.rpow x (x - 1) * (Real.log x + (x - 1) / x)) :
    iterDeriv 3 f 1 = 3 := by
  rw [hthird 1 one_pos]
  norm_num [powerSelf]

set_option backward.isDefEq.respectTransparency false in
private theorem powerSelf_hasSum_taylor (x : ℝ) (hx : |x - 1| < 1) :
    HasSum (taylorAtOneTerm powerSelf x) (powerSelf x) := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hxr
  let R : NNReal := ⟨r, hr0.le⟩
  let G : ℂ → ℂ := fun z => z ^ z
  have hsubset : Metric.closedBall (1 : ℂ) R ⊆ Complex.slitPlane := by
    exact (Metric.closedBall_subset_ball (by simpa [R] using hr1)).trans
      Complex.ball_one_subset_slitPlane
  have hGdiff : DifferentiableOn ℂ G (Metric.closedBall (1 : ℂ) R) := by
    intro z hz
    have hzslit := hsubset hz
    exact ((analyticAt_id.cpow analyticAt_id hzslit).differentiableAt).differentiableWithinAt
  have hR0 : (0 : NNReal) < R := by
    exact hr0
  have hG := hGdiff.hasFPowerSeriesOnBall hR0
  have hGreal := hG.restrictScalars (𝕜 := ℝ)
  have hpre := hGreal.compContinuousLinearMap (u := Complex.ofRealCLM) (x := (1 : ℝ))
  have hraw := Complex.reCLM.comp_hasFPowerSeriesOnBall hpre
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    Complex.reCLM.compFormalMultilinearSeries
      ((FormalMultilinearSeries.restrictScalars ℝ
        (cauchyPowerSeries G 1 R)).compContinuousLinearMap Complex.ofRealCLM)
  have hex : ∃ q : FormalMultilinearSeries ℝ ℝ ℝ,
      HasFPowerSeriesOnBall powerSelf q 1 R := by
    refine ⟨q, ?_⟩
    have hc := hraw.congr (g := powerSelf) ?_
    · simpa [q, Complex.ofRealCLM_enorm] using hc
    · intro y hy
      simp only [Function.comp_apply]
      rfl
  rcases hex with ⟨q, hq⟩
  have hy : x - 1 ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.eball_coe]
    simpa [R, Real.norm_eq_abs] using hxr
  have hs := hq.hasSum hy
  have hterm : ∀ n : ℕ,
      (q n) (fun _ => x - 1) = taylorAtOneTerm powerSelf x n := by
    intro n
    have hfact := hq.factorial_smul (1 : ℝ) n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at hfact
    have hcoeff :
        q.coeff n = iteratedDeriv n powerSelf 1 / (Nat.factorial n : ℝ) := by
      apply (eq_div_iff (by positivity : (Nat.factorial n : ℝ) ≠ 0)).2
      rw [mul_comm]
      simpa [← iteratedDeriv_eq_iteratedFDeriv] using hfact
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hcoeff, taylorAtOneTerm, iterDeriv]
    rw [← iteratedDeriv_eq_iterate]
    ring
  have hs' : HasSum (taylorAtOneTerm powerSelf x)
      (powerSelf (1 + (x - 1))) :=
    hs.congr_fun (fun n => (hterm n).symm)
  simpa using hs'

theorem gap8
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1)
    (hsecond :
      ∀ x, 0 < x →
        iterDeriv 2 f x =
          powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1))
    (hsecond1 : iterDeriv 2 f 1 = 2)
    (hthird :
      ∀ x, 0 < x →
        iterDeriv 3 f x =
          powerSelf x * (1 + Real.log x) ^ 3 +
            2 * Real.rpow x (x - 1) * (1 + Real.log x) +
            Real.rpow x (x - 1) * (Real.log x + (x - 1) / x))
    (hthird1 : iterDeriv 3 f 1 = 3) :
    ∀ x, |x - 1| < 1 → f x = ∑' n, taylorAtOneTerm f x n := by
  intro x hx
  have heq : f = powerSelf := funext hf
  subst f
  exact (powerSelf_hasSum_taylor x hx).tsum_eq.symm

theorem gap9
    (f : ℝ → ℝ) (hf : ∀ x, f x = powerSelf x) (hf1 : f 1 = 1)
    (hderiv : ∀ x, 0 < x → deriv f x = powerSelf x * (1 + Real.log x))
    (hderiv1 : deriv f 1 = 1)
    (hsecond :
      ∀ x, 0 < x →
        iterDeriv 2 f x =
          powerSelf x * (1 + Real.log x) ^ 2 + Real.rpow x (x - 1))
    (hsecond1 : iterDeriv 2 f 1 = 2)
    (hthird :
      ∀ x, 0 < x →
        iterDeriv 3 f x =
          powerSelf x * (1 + Real.log x) ^ 3 +
            2 * Real.rpow x (x - 1) * (1 + Real.log x) +
            Real.rpow x (x - 1) * (Real.log x + (x - 1) / x))
    (hthird1 : iterDeriv 3 f 1 = 3)
    (htaylor : ∀ x, |x - 1| < 1 → f x = ∑' n, taylorAtOneTerm f x n) :
    ∀ x, |x - 1| < 1 → Summable (taylorAtOneTerm f x) := by
  intro x hx
  have heq : f = powerSelf := funext hf
  subst f
  exact (powerSelf_hasSum_taylor x hx).summable

end

end ProofGap.Exercise2847
