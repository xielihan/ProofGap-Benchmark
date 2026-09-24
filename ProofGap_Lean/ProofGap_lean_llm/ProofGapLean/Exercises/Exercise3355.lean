import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3355

noncomputable section

open scoped Interval

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z s y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX z x s) y

def IsC2 (z : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (Function.uncurry z)

def primitive (φ₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, φ₁ t

private lemma differentiable_section_x (z : ℝ → ℝ → ℝ) (hz : IsC2 z) (y : ℝ) :
    Differentiable ℝ (fun x => z x y) := by
  have hz' : ContDiff ℝ 2 (Function.uncurry z) := hz
  have hp : ContDiff ℝ 2 (fun x : ℝ => ((x, y) : ℝ × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have hs : ContDiff ℝ 2 (fun x : ℝ => z x y) := by
    simpa [Function.uncurry] using hz'.comp hp
  exact hs.differentiable (by decide)

private lemma partialX_eq_directional (z : ℝ → ℝ → ℝ) (hz : IsC2 z)
    (x y : ℝ) :
    partialX z x y =
      fderiv ℝ (Function.uncurry z) (x, y) ((1, 0) : ℝ × ℝ) := by
  have hz' : ContDiff ℝ 2 (Function.uncurry z) := hz
  have houter :
      HasFDerivAt (Function.uncurry z)
        (fderiv ℝ (Function.uncurry z) (x, y)) (x, y) :=
    (hz'.differentiable (by decide)).differentiableAt.hasFDerivAt
  have hpath : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × ℝ)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hcomp := houter.comp_hasDerivAt x hpath
  simpa [partialX, Function.comp_def, Function.uncurry] using hcomp.deriv

private lemma contDiff_partialX_pair (z : ℝ → ℝ → ℝ) (hz : IsC2 z) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => partialX z p.1 p.2) := by
  have hz' : ContDiff ℝ 2 (Function.uncurry z) := hz
  have hd :
      ContDiff ℝ 1 (fun p => fderiv ℝ (Function.uncurry z) p) :=
    hz'.fderiv_right (by norm_num)
  have he :
      ContDiff ℝ 1
        (fun p => fderiv ℝ (Function.uncurry z) p ((1, 0) : ℝ × ℝ)) :=
    hd.clm_apply contDiff_const
  have heq :
      (fun p : ℝ × ℝ => partialX z p.1 p.2) =
        fun p => fderiv ℝ (Function.uncurry z) p ((1, 0) : ℝ × ℝ) := by
    funext p
    simpa using partialX_eq_directional z hz p.1 p.2
  rw [heq]
  exact he

private theorem mixed_eq_zero_of_add (z : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ)
    (hrep : ∀ x y, z x y = φ x + ψ y) :
    ∀ x y, partialXY z x y = 0 := by
  intro x y
  have hinner :
      (fun t => partialX z x t) = fun _ : ℝ => deriv φ x := by
    funext t
    unfold partialX
    have hsection : (fun s => z s t) = fun s => φ s + ψ t := by
      funext s
      exact hrep s t
    rw [hsection]
    simp
  unfold partialXY
  rw [hinner]
  simp

private lemma additive_representation_of_partialX (z : ℝ → ℝ → ℝ)
    (hz : IsC2 z)
    (hpartial : ∀ x y, partialX z x y = partialX z x 0) :
    ∀ x y, z x y = (z x 0 - z 0 0) + z 0 y := by
  intro x y
  have hdiff : Differentiable ℝ (fun t => z t y - z t 0) :=
    (differentiable_section_x z hz y).sub
      (differentiable_section_x z hz 0)
  have hderiv : ∀ t, deriv (fun s => z s y - z s 0) t = 0 := by
    intro t
    have hy : HasDerivAt (fun s => z s y) (partialX z t y) t := by
      simpa [partialX] using
        (differentiable_section_x z hz y).differentiableAt.hasDerivAt
    have h0 : HasDerivAt (fun s => z s 0) (partialX z t 0) t := by
      simpa [partialX] using
        (differentiable_section_x z hz 0).differentiableAt.hasDerivAt
    calc
      deriv (fun s => z s y - z s 0) t =
          partialX z t y - partialX z t 0 := (hy.sub h0).deriv
      _ = 0 := by rw [hpartial t y, sub_self]
  have hc : z x y - z x 0 = z 0 y - z 0 0 :=
    is_const_of_deriv_eq_zero hdiff hderiv x 0
  calc
    z x y = (z x y - z x 0) + z x 0 := by ring
    _ = (z 0 y - z 0 0) + z x 0 := by rw [hc]
    _ = (z x 0 - z 0 0) + z 0 y := by ring

theorem gap1 (z : ℝ → ℝ → ℝ) (hz : IsC2 z) :
    (∀ x y, partialXY z x y = 0) ↔
      ∃ φ₁ : ℝ → ℝ, ∀ x y, partialX z x y = φ₁ x := by
  constructor
  · intro hzero
    refine ⟨fun x => partialX z x 0, ?_⟩
    intro x y
    have hp : ContDiff ℝ 1 (fun t : ℝ => ((x, t) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    have hdiff : Differentiable ℝ (fun t => partialX z x t) :=
      ((contDiff_partialX_pair z hz).comp hp).differentiable (by norm_num)
    apply is_const_of_deriv_eq_zero hdiff
      (fun t => by simpa [partialXY] using hzero x t) y 0
  · rintro ⟨φ₁, hφ₁⟩ x y
    have heq : (fun t => partialX z x t) = fun _ : ℝ => φ₁ x := by
      funext t
      exact hφ₁ x t
    simp [partialXY, heq]

theorem gap2 (z : ℝ → ℝ → ℝ) (hz : IsC2 z) :
    (∀ x y, partialXY z x y = 0) ↔
      ∃ φ₁ ψ : ℝ → ℝ, Continuous φ₁ ∧
        ∀ x y, z x y = primitive φ₁ x + ψ y := by
  constructor
  · intro hzero
    obtain ⟨f, hf⟩ := (gap1 z hz).mp hzero
    have hconst : ∀ x y, partialX z x y = partialX z x 0 := by
      intro x y
      exact (hf x y).trans (hf x 0).symm
    have hp : ContDiff ℝ 1 (fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    have hcont : Continuous (fun x => partialX z x 0) :=
      ((contDiff_partialX_pair z hz).comp hp).continuous
    have hderiv : ∀ t, HasDerivAt (fun s : ℝ => z s 0) (partialX z t 0) t := by
      intro t
      simpa [partialX] using
        (differentiable_section_x z hz 0).differentiableAt.hasDerivAt
    have hprim : ∀ x, primitive (fun t => partialX z t 0) x = z x 0 - z 0 0 := by
      intro x
      simpa [primitive] using
        (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun t : ℝ => z t 0)
          (f' := fun t => partialX z t 0)
          (a := 0) (b := x)
          (fun t _ => hderiv t)
          (hcont.intervalIntegrable 0 x))
    refine ⟨fun x => partialX z x 0, fun y => z 0 y, hcont, ?_⟩
    intro x y
    rw [hprim x]
    exact additive_representation_of_partialX z hz hconst x y
  · rintro ⟨φ₁, ψ, _, hrep⟩
    exact mixed_eq_zero_of_add z (primitive φ₁) ψ hrep

theorem gap3 (z : ℝ → ℝ → ℝ) (hz : IsC2 z) :
    (∀ x y, partialXY z x y = 0) ↔
      ∃ φ₁ ψ φ : ℝ → ℝ, Continuous φ₁ ∧
        (∀ x, primitive φ₁ x = φ x) ∧
        ∀ x y, z x y = φ x + ψ y := by
  constructor
  · intro hzero
    obtain ⟨φ₁, ψ, hcont, hrep⟩ := (gap2 z hz).mp hzero
    exact ⟨φ₁, ψ, primitive φ₁, hcont, fun _ => rfl, hrep⟩
  · rintro ⟨φ₁, ψ, φ, hcont, hprim, hrep⟩
    apply (gap2 z hz).mpr
    refine ⟨φ₁, ψ, hcont, ?_⟩
    intro x y
    simpa [hprim x] using hrep x y

theorem gap4 (z : ℝ → ℝ → ℝ) (hz : IsC2 z) :
    (∀ x y, partialXY z x y = 0) ↔
      ∃ φ ψ : ℝ → ℝ, ∀ x y, z x y = φ x + ψ y := by
  constructor
  · intro hzero
    obtain ⟨φ₁, ψ, φ, _, _, hrep⟩ := (gap3 z hz).mp hzero
    exact ⟨φ, ψ, hrep⟩
  · rintro ⟨φ, ψ, hrep⟩
    exact mixed_eq_zero_of_add z φ ψ hrep

theorem gap5 (z : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ)
    (hz : ∀ x y, z x y = φ x + ψ y) :
    ∀ x y, partialXY z x y = 0 := by
  exact mixed_eq_zero_of_add z φ ψ hz

end

end ProofGap.Exercise3355
