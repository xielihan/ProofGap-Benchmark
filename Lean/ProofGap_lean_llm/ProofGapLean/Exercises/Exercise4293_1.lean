import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4293_1

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def force (m g : ℝ) : Point3 :=
  (0, 0, -m * g)

def verticalUnit : Point3 :=
  (0, 0, 1)

def potential (m g : ℝ) (p : Point3) : ℝ :=
  -m * g * p.2.2

def coordinateDifferential (V v : Point3) : ℝ :=
  V.1 * v.1 + V.2.1 * v.2.1 + V.2.2 * v.2.2

def differential (A : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv (fun x => A (x, p.2.1, p.2.2)) p.1 * v.1 +
    deriv (fun y => A (p.1, y, p.2.2)) p.2.1 * v.2.1 +
      deriv (fun z => A (p.1, p.2.1, z)) p.2.2 * v.2.2

def lineIntegral (m g : ℝ) (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    coordinateDifferential (force m g)
      (deriv (fun s => (γ s).1) t,
        deriv (fun s => (γ s).2.1) t,
        deriv (fun s => (γ s).2.2) t)

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

def work (m g : ℝ) (start finish : Point3) : ℝ :=
  potential m g finish - potential m g start

private theorem differential_potential_eq (m g : ℝ) (p v : Point3) :
    differential (potential m g) p v = (-m * g) * v.2.2 := by
  have hz :
      deriv (fun z : ℝ => potential m g (p.1, p.2.1, z)) p.2.2 = -m * g := by
    simpa [potential] using
      ((hasDerivAt_id p.2.2).const_mul (-m * g)).deriv
  unfold differential
  rw [hz]
  simp [potential]

private theorem integral_deriv_eq_sub_of_contDiff
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    (∫ x in a..b, deriv f x) = f b - f a := by
  have hsplit :
      Differentiable ℝ f ∧ ContDiff ℝ 0 (fderiv ℝ f) := by
    simpa using (contDiff_succ_iff_fderiv (n := 0)).mp hf
  have hcontFDeriv : Continuous (fderiv ℝ f) :=
    hsplit.2.continuous
  have hcontDeriv : Continuous (deriv f) := by
    simpa only [deriv] using
      hcontFDeriv.clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hsplit.1 x)
    (hcontDeriv.intervalIntegrable a b)

theorem gap1 (m g : ℝ) :
    force m g = (-m * g) • verticalUnit := by
  simp [force, verticalUnit]

theorem gap2 (m g : ℝ) :
    ∃ A : Point3 → ℝ, ∀ p v,
      differential A p v = coordinateDifferential (force m g) v := by
  refine ⟨potential m g, ?_⟩
  intro p v
  rw [differential_potential_eq]
  simp [coordinateDifferential, force]

theorem gap3 (m g : ℝ) (v : Point3) :
    coordinateDifferential (force m g) v = (-m * g) * v.2.2 := by
  simp [coordinateDifferential, force]

theorem gap4 (m g : ℝ) (p v : Point3) :
    (-m * g) * v.2.2 = differential (potential m g) p v := by
  exact (differential_potential_eq m g p v).symm

theorem gap5 (m g : ℝ) :
    ∃ A : Point3 → ℝ, ∀ p v,
      differential A p v = differential (potential m g) p v := by
  exact ⟨potential m g, fun p v => rfl⟩

theorem gap6 (m g : ℝ) (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    work m g start finish = lineIntegral m g γ := by
  rcases hγ with ⟨hγdiff, hγ0, hγ1⟩
  let z : ℝ → ℝ := fun t => (γ t).2.2
  let F : ℝ → ℝ := fun t => (-m * g) * z t
  have hz : ContDiff ℝ 1 z := by
    dsimp [z]
    exact hγdiff.snd.snd
  have hzDiff : Differentiable ℝ z := hz.differentiable (by simp)
  have hF : ContDiff ℝ 1 F := by
    dsimp [F]
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (-m * g))).mul hz
  have hFderiv (t : ℝ) : deriv F t = (-m * g) * deriv z t := by
    dsimp [F]
    exact ((hzDiff t).hasDerivAt.const_mul (-m * g)).deriv
  have hline : lineIntegral m g γ = ∫ t in (0 : ℝ)..1, deriv F t := by
    unfold lineIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [hFderiv t]
    simp [coordinateDifferential, force, z]
  have hFTC : (∫ t in (0 : ℝ)..1, deriv F t) = F 1 - F 0 :=
    integral_deriv_eq_sub_of_contDiff F hF 0 1
  calc
    work m g start finish = F 1 - F 0 := by
      simp [work, potential, F, z, hγ0, hγ1]
    _ = ∫ t in (0 : ℝ)..1, deriv F t := hFTC.symm
    _ = lineIntegral m g γ := hline.symm

theorem gap7 (m g : ℝ) (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral m g γ =
      potential m g finish - potential m g start := by
  calc
    lineIntegral m g γ = work m g start finish :=
      (gap6 m g start finish γ hγ).symm
    _ = potential m g finish - potential m g start := rfl

theorem gap8 (m g : ℝ) (start finish : Point3) :
    potential m g finish - potential m g start =
      -m * g * (finish.2.2 - start.2.2) := by
  unfold potential
  ring

theorem gap9 (m g : ℝ) (start finish : Point3) :
    work m g start finish = -m * g * (finish.2.2 - start.2.2) := by
  simpa [work] using gap8 m g start finish

end

end ProofGap.Exercise4293_1
