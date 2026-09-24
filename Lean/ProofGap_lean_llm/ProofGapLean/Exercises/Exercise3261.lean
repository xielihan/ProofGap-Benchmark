import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3261

noncomputable section

def r (x y ξ η : ℝ) : ℝ :=
  Real.sqrt ((x - ξ) ^ 2 + (y - η) ^ 2)

def u (x y ξ η : ℝ) : ℝ :=
  Real.log (1 / r x y ξ η)

def partialX (g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y ξ η : ℝ) : ℝ :=
  deriv (fun t => g t y ξ η) x

def partialXY (g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y ξ η : ℝ) : ℝ :=
  deriv (fun t => partialX g x t ξ η) y

def partialXYXi (g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y ξ η : ℝ) : ℝ :=
  deriv (fun t => partialXY g x y t η) ξ

def partialXYXiEta (g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y ξ η : ℝ) : ℝ :=
  deriv (fun t => partialXYXi g x y ξ t) η

def fourthExpanded (x y ξ η : ℝ) : ℝ :=
  2 / r x y ξ η ^ 4 -
    8 * (y - η) ^ 2 / r x y ξ η ^ 6 -
    8 * (x - ξ) ^ 2 / r x y ξ η ^ 6 +
    48 * (x - ξ) ^ 2 * (y - η) ^ 2 / r x y ξ η ^ 8

def fourthSimplified (x y ξ η : ℝ) : ℝ :=
  -(6 / r x y ξ η ^ 4) +
    48 * (x - ξ) ^ 2 * (y - η) ^ 2 / r x y ξ η ^ 8

private theorem continuous_r_y (x ξ η : ℝ) :
    Continuous (fun t : ℝ => r x t ξ η) := by
  unfold r
  exact Real.continuous_sqrt.comp
    ((continuous_const.pow 2).add
      ((continuous_id.sub continuous_const).pow 2))

private theorem continuous_r_xi (x y η : ℝ) :
    Continuous (fun t : ℝ => r x y t η) := by
  unfold r
  exact Real.continuous_sqrt.comp
    (((continuous_const.sub continuous_id).pow 2).add
      (continuous_const.pow 2))

private theorem continuous_r_eta (x y ξ : ℝ) :
    Continuous (fun t : ℝ => r x y ξ t) := by
  unfold r
  exact Real.continuous_sqrt.comp
    ((continuous_const.pow 2).add
      ((continuous_const.sub continuous_id).pow 2))

private theorem eventually_r_pos_y (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    ∀ᶠ t in nhds y, 0 < r x t ξ η := by
  have hopen : IsOpen {t : ℝ | 0 < r x t ξ η} :=
    isOpen_Ioi.preimage (continuous_r_y x ξ η)
  exact hopen.mem_nhds hr

private theorem eventually_r_pos_xi (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    ∀ᶠ t in nhds ξ, 0 < r x y t η := by
  have hopen : IsOpen {t : ℝ | 0 < r x y t η} :=
    isOpen_Ioi.preimage (continuous_r_xi x y η)
  exact hopen.mem_nhds hr

private theorem eventually_r_pos_eta (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    ∀ᶠ t in nhds η, 0 < r x y ξ t := by
  have hopen : IsOpen {t : ℝ | 0 < r x y ξ t} :=
    isOpen_Ioi.preimage (continuous_r_eta x y ξ)
  exact hopen.mem_nhds hr

private theorem hasDerivAt_r_x (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    HasDerivAt (fun t : ℝ => r t y ξ η)
      ((x - ξ) / r x y ξ η) x := by
  have hq :
      HasDerivAt
        (fun t : ℝ => (t - ξ) ^ 2 + (y - η) ^ 2)
        (2 * (x - ξ)) x := by
    convert ((((hasDerivAt_id x).sub_const ξ).pow 2).add_const
      ((y - η) ^ 2)) using 1 <;> simp [id] <;> ring
  have hqne : (x - ξ) ^ 2 + (y - η) ^ 2 ≠ 0 := by
    intro h
    have hz : r x y ξ η = 0 := by simp [r, h]
    linarith
  have hs := (Real.hasDerivAt_sqrt hqne).comp x hq
  have hcoef :
      1 / (2 * Real.sqrt ((x - ξ) ^ 2 + (y - η) ^ 2)) *
          (2 * (x - ξ)) =
        (x - ξ) / r x y ξ η := by
    change 1 / (2 * r x y ξ η) * (2 * (x - ξ)) =
      (x - ξ) / r x y ξ η
    field_simp [hr.ne']
  rw [hcoef] at hs
  simpa [r, Function.comp_def] using hs

private theorem hasDerivAt_r_y (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    HasDerivAt (fun t : ℝ => r x t ξ η)
      ((y - η) / r x y ξ η) y := by
  have hq :
      HasDerivAt
        (fun t : ℝ => (x - ξ) ^ 2 + (t - η) ^ 2)
        (2 * (y - η)) y := by
    convert ((((hasDerivAt_id y).sub_const η).pow 2).const_add
      ((x - ξ) ^ 2)) using 1 <;> simp [id] <;> ring
  have hqne : (x - ξ) ^ 2 + (y - η) ^ 2 ≠ 0 := by
    intro h
    have hz : r x y ξ η = 0 := by simp [r, h]
    linarith
  have hs := (Real.hasDerivAt_sqrt hqne).comp y hq
  have hcoef :
      1 / (2 * Real.sqrt ((x - ξ) ^ 2 + (y - η) ^ 2)) *
          (2 * (y - η)) =
        (y - η) / r x y ξ η := by
    change 1 / (2 * r x y ξ η) * (2 * (y - η)) =
      (y - η) / r x y ξ η
    field_simp [hr.ne']
  rw [hcoef] at hs
  simpa [r, Function.comp_def] using hs

private theorem hasDerivAt_r_xi (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    HasDerivAt (fun t : ℝ => r x y t η)
      (-((x - ξ) / r x y ξ η)) ξ := by
  have hq :
      HasDerivAt
        (fun t : ℝ => (x - t) ^ 2 + (y - η) ^ 2)
        (-2 * (x - ξ)) ξ := by
    convert (((((hasDerivAt_const (x := ξ) x).sub
      (hasDerivAt_id ξ)).pow 2).add_const ((y - η) ^ 2))) using 1 <;>
      simp [id] <;> ring
  have hqne : (x - ξ) ^ 2 + (y - η) ^ 2 ≠ 0 := by
    intro h
    have hz : r x y ξ η = 0 := by simp [r, h]
    linarith
  have hs := (Real.hasDerivAt_sqrt hqne).comp ξ hq
  have hcoef :
      1 / (2 * Real.sqrt ((x - ξ) ^ 2 + (y - η) ^ 2)) *
          (-2 * (x - ξ)) =
        -((x - ξ) / r x y ξ η) := by
    change 1 / (2 * r x y ξ η) * (-2 * (x - ξ)) =
      -((x - ξ) / r x y ξ η)
    field_simp [hr.ne']
  rw [hcoef] at hs
  simpa [r, Function.comp_def] using hs

private theorem hasDerivAt_r_eta (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    HasDerivAt (fun t : ℝ => r x y ξ t)
      (-((y - η) / r x y ξ η)) η := by
  have hq :
      HasDerivAt
        (fun t : ℝ => (x - ξ) ^ 2 + (y - t) ^ 2)
        (-2 * (y - η)) η := by
    convert (((((hasDerivAt_const (x := η) y).sub
      (hasDerivAt_id η)).pow 2).const_add ((x - ξ) ^ 2))) using 1 <;>
      simp [id] <;> ring
  have hqne : (x - ξ) ^ 2 + (y - η) ^ 2 ≠ 0 := by
    intro h
    have hz : r x y ξ η = 0 := by simp [r, h]
    linarith
  have hs := (Real.hasDerivAt_sqrt hqne).comp η hq
  have hcoef :
      1 / (2 * Real.sqrt ((x - ξ) ^ 2 + (y - η) ^ 2)) *
          (-2 * (y - η)) =
        -((y - η) / r x y ξ η) := by
    change 1 / (2 * r x y ξ η) * (-2 * (y - η)) =
      -((y - η) / r x y ξ η)
    field_simp [hr.ne']
  rw [hcoef] at hs
  simpa [r, Function.comp_def] using hs

private theorem hasDerivAt_u_x (x y ξ η : ℝ)
    (hr : 0 < r x y ξ η) :
    HasDerivAt (fun t : ℝ => u t y ξ η)
      (-((x - ξ) / r x y ξ η ^ 2)) x := by
  have hR := hasDerivAt_r_x x y ξ η hr
  have hlog := (Real.hasDerivAt_log hr.ne').comp x hR
  have hneg := hlog.neg
  convert hneg using 1
  · funext t
    simpa [u, one_div] using (Real.log_inv (r t y ξ η))
  · field_simp [hr.ne']

theorem gap1 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    u x y ξ η = -Real.log (r x y ξ η) := by
  simpa [u, one_div] using (Real.log_inv (r x y ξ η))

theorem gap2 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialX u x y ξ η =
      -(1 / r x y ξ η) * partialX r x y ξ η := by
  unfold partialX
  rw [(hasDerivAt_u_x x y ξ η hr).deriv,
    (hasDerivAt_r_x x y ξ η hr).deriv]
  field_simp [hr.ne']

theorem gap3 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    -(1 / r x y ξ η) * partialX r x y ξ η =
      -((x - ξ) / r x y ξ η ^ 2) := by
  unfold partialX
  rw [(hasDerivAt_r_x x y ξ η hr).deriv]
  field_simp [hr.ne']

theorem gap4 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialX u x y ξ η =
      -((x - ξ) / r x y ξ η ^ 2) := by
  unfold partialX
  exact (hasDerivAt_u_x x y ξ η hr).deriv

theorem gap5 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialXY u x y ξ η =
      2 * (x - ξ) * (y - η) / r x y ξ η ^ 4 := by
  have hinv := ((hasDerivAt_r_y x y ξ η hr).pow 2).inv
    (pow_ne_zero 2 hr.ne')
  have hraw := hinv.const_mul (-(x - ξ))
  have heq :
      (fun t : ℝ => -(x - ξ) * ((fun s : ℝ => r x s ξ η) ^ 2)⁻¹ t) =ᶠ[nhds y]
        (fun t : ℝ => partialX u x t ξ η) :=
    (eventually_r_pos_y x y ξ η hr).mono (fun t ht => by
      change -(x - ξ) * (r x t ξ η ^ 2)⁻¹ = partialX u x t ξ η
      calc
        -(x - ξ) * (r x t ξ η ^ 2)⁻¹ =
            -((x - ξ) / r x t ξ η ^ 2) := by
              rw [div_eq_mul_inv]
              ring
        _ = partialX u x t ξ η := (gap4 x t ξ η ht).symm)
  unfold partialXY
  rw [(hraw.congr_of_eventuallyEq heq.symm).deriv]
  simp only [Pi.inv_apply, Pi.pow_apply]
  field_simp [hr.ne'] <;> ring

theorem gap6 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialXYXi u x y ξ η =
      -(2 * (y - η) / r x y ξ η ^ 4) +
        8 * (x - ξ) ^ 2 * (y - η) / r x y ξ η ^ 6 := by
  have hA :
      HasDerivAt (fun t : ℝ => 2 * (x - t) * (y - η))
        (-2 * (y - η)) ξ := by
    convert (((((hasDerivAt_const (x := ξ) x).sub
      (hasDerivAt_id ξ)).const_mul 2).mul_const (y - η))) using 1 <;>
      simp <;> ring
  have hinv := ((hasDerivAt_r_xi x y ξ η hr).pow 4).inv
    (pow_ne_zero 4 hr.ne')
  have hraw := hA.mul hinv
  have heq :
      (fun t : ℝ =>
        (2 * (x - t) * (y - η)) *
          ((fun s : ℝ => r x y s η) ^ 4)⁻¹ t) =ᶠ[nhds ξ]
        (fun t : ℝ => partialXY u x y t η) :=
    (eventually_r_pos_xi x y ξ η hr).mono (fun t ht => by
      change
        (2 * (x - t) * (y - η)) * (r x y t η ^ 4)⁻¹ =
          partialXY u x y t η
      calc
        (2 * (x - t) * (y - η)) * (r x y t η ^ 4)⁻¹ =
            2 * (x - t) * (y - η) / r x y t η ^ 4 := by
              rw [div_eq_mul_inv]
        _ = partialXY u x y t η := (gap5 x y t η ht).symm)
  unfold partialXYXi
  rw [(hraw.congr_of_eventuallyEq heq.symm).deriv]
  simp only [Pi.inv_apply, Pi.pow_apply]
  field_simp [hr.ne'] <;> ring

theorem gap7 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialXYXiEta u x y ξ η = fourthExpanded x y ξ η := by
  have hdy : HasDerivAt (fun t : ℝ => y - t) (-1) η := by
    convert ((hasDerivAt_const (x := η) y).sub (hasDerivAt_id η)) using 1 <;>
      simp <;> ring
  have hN1 : HasDerivAt (fun t : ℝ => -(2 * (y - t))) 2 η := by
    convert (hdy.const_mul 2).neg using 1 <;> ring
  have hN2 :
      HasDerivAt (fun t : ℝ => 8 * (x - ξ) ^ 2 * (y - t))
        (-(8 * (x - ξ) ^ 2)) η := by
    convert hdy.const_mul (8 * (x - ξ) ^ 2) using 1 <;> ring
  have hR := hasDerivAt_r_eta x y ξ η hr
  have hinv4 := (hR.pow 4).inv (pow_ne_zero 4 hr.ne')
  have hinv6 := (hR.pow 6).inv (pow_ne_zero 6 hr.ne')
  have hraw := (hN1.mul hinv4).add (hN2.mul hinv6)
  have heq :
      (fun t : ℝ =>
        (-(2 * (y - t))) * ((fun s : ℝ => r x y ξ s) ^ 4)⁻¹ t +
          (8 * (x - ξ) ^ 2 * (y - t)) *
            ((fun s : ℝ => r x y ξ s) ^ 6)⁻¹ t) =ᶠ[nhds η]
        (fun t : ℝ => partialXYXi u x y ξ t) :=
    (eventually_r_pos_eta x y ξ η hr).mono (fun t ht => by
      change
        (-(2 * (y - t))) * (r x y ξ t ^ 4)⁻¹ +
            (8 * (x - ξ) ^ 2 * (y - t)) * (r x y ξ t ^ 6)⁻¹ =
          partialXYXi u x y ξ t
      calc
        (-(2 * (y - t))) * (r x y ξ t ^ 4)⁻¹ +
              (8 * (x - ξ) ^ 2 * (y - t)) * (r x y ξ t ^ 6)⁻¹ =
            -(2 * (y - t) / r x y ξ t ^ 4) +
              8 * (x - ξ) ^ 2 * (y - t) / r x y ξ t ^ 6 := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
        _ = partialXYXi u x y ξ t := (gap6 x y ξ t ht).symm)
  unfold partialXYXiEta
  rw [(hraw.congr_of_eventuallyEq heq.symm).deriv]
  unfold fourthExpanded
  simp only [Pi.inv_apply, Pi.pow_apply]
  field_simp [hr.ne'] <;> ring

theorem gap8 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    fourthExpanded x y ξ η = fourthSimplified x y ξ η := by
  have hnonneg :
      0 ≤ (x - ξ) ^ 2 + (y - η) ^ 2 :=
    add_nonneg (sq_nonneg (x - ξ)) (sq_nonneg (y - η))
  have hR2 :
      r x y ξ η ^ 2 = (x - ξ) ^ 2 + (y - η) ^ 2 := by
    simpa [r] using (Real.sq_sqrt hnonneg)
  have hR4 :
      r x y ξ η ^ 4 =
        ((x - ξ) ^ 2 + (y - η) ^ 2) * r x y ξ η ^ 2 := by
    calc
      r x y ξ η ^ 4 = r x y ξ η ^ 2 * r x y ξ η ^ 2 := by ring
      _ = ((x - ξ) ^ 2 + (y - η) ^ 2) * r x y ξ η ^ 2 := by rw [hR2]
  unfold fourthExpanded fourthSimplified
  field_simp [hr.ne']
  nlinarith [hR4]

theorem gap9 (x y ξ η : ℝ) (hr : 0 < r x y ξ η) :
    partialXYXiEta u x y ξ η = fourthSimplified x y ξ η := by
  rw [gap7 x y ξ η hr, gap8 x y ξ η hr]

end

end ProofGap.Exercise3261
