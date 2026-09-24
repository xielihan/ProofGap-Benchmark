import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3481

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

theorem gap1 (x : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (r, φ))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      x p.1 p.2 = p.1 * Real.cos p.2) :
    differential x r φ dr dφ =
      Real.cos φ * dr - r * Real.sin φ * dφ := by
  have hmapR :
      Filter.Tendsto (fun t : ℝ => (t, φ)) (nhds r) (nhds (r, φ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmapPhi :
      Filter.Tendsto (fun t : ℝ => (r, t)) (nhds φ) (nhds (r, φ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hXr :
      (fun t : ℝ => x t φ) =ᶠ[nhds r]
        (fun t : ℝ => t * Real.cos φ) := by
    simpa using hmapR.eventually hX
  have hXphi :
      (fun t : ℝ => x r t) =ᶠ[nhds φ]
        (fun t : ℝ => r * Real.cos t) := by
    simpa using hmapPhi.eventually hX
  have hxR : partialX x r φ = Real.cos φ := by
    unfold partialX
    calc
      deriv (fun t : ℝ => x t φ) r =
          deriv (fun t : ℝ => t * Real.cos φ) r := hXr.deriv_eq
      _ = Real.cos φ := by
        simpa using ((hasDerivAt_id r).mul_const (Real.cos φ)).deriv
  have hxPhi : partialY x r φ = -(r * Real.sin φ) := by
    unfold partialY
    calc
      deriv (fun t : ℝ => x r t) φ =
          deriv (fun t : ℝ => r * Real.cos t) φ := hXphi.deriv_eq
      _ = -(r * Real.sin φ) := by
        simpa using ((Real.hasDerivAt_cos φ).const_mul r).deriv
  unfold differential
  rw [hxR, hxPhi]
  ring

theorem gap2 (y : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (r, φ))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      y p.1 p.2 = p.1 * Real.sin p.2) :
    differential y r φ dr dφ =
      Real.sin φ * dr + r * Real.cos φ * dφ := by
  have hmapR :
      Filter.Tendsto (fun t : ℝ => (t, φ)) (nhds r) (nhds (r, φ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmapPhi :
      Filter.Tendsto (fun t : ℝ => (r, t)) (nhds φ) (nhds (r, φ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hYr :
      (fun t : ℝ => y t φ) =ᶠ[nhds r]
        (fun t : ℝ => t * Real.sin φ) := by
    simpa using hmapR.eventually hY
  have hYphi :
      (fun t : ℝ => y r t) =ᶠ[nhds φ]
        (fun t : ℝ => r * Real.sin t) := by
    simpa using hmapPhi.eventually hY
  have hyR : partialX y r φ = Real.sin φ := by
    unfold partialX
    calc
      deriv (fun t : ℝ => y t φ) r =
          deriv (fun t : ℝ => t * Real.sin φ) r := hYr.deriv_eq
      _ = Real.sin φ := by
        simpa using ((hasDerivAt_id r).mul_const (Real.sin φ)).deriv
  have hyPhi : partialY y r φ = r * Real.cos φ := by
    unfold partialY
    calc
      deriv (fun t : ℝ => y r t) φ =
          deriv (fun t : ℝ => r * Real.sin t) φ := hYphi.deriv_eq
      _ = r * Real.cos φ := by
        simpa using ((Real.hasDerivAt_sin φ).const_mul r).deriv
  unfold differential
  rw [hyR, hyPhi]

theorem gap3 (x y : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hr : r ≠ 0)
    (hX : x r φ = r * Real.cos φ)
    (hY : y r φ = r * Real.sin φ)
    (hDx : differential x r φ dr dφ =
      Real.cos φ * dr - r * Real.sin φ * dφ)
    (hDy : differential y r φ dr dφ =
      Real.sin φ * dr + r * Real.cos φ * dφ) :
    dr = x r φ / r * differential x r φ dr dφ +
      y r φ / r * differential y r φ dr dφ := by
  rw [hX, hY, hDx, hDy]
  calc
    dr = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * dr := by
      rw [Real.sin_sq_add_cos_sq, one_mul]
    _ = r * Real.cos φ / r *
          (Real.cos φ * dr - r * Real.sin φ * dφ) +
        r * Real.sin φ / r *
          (Real.sin φ * dr + r * Real.cos φ * dφ) := by
      field_simp [hr] <;> ring

theorem gap4 (x y : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hr : r ≠ 0)
    (hX : x r φ = r * Real.cos φ)
    (hY : y r φ = r * Real.sin φ)
    (hDx : differential x r φ dr dφ =
      Real.cos φ * dr - r * Real.sin φ * dφ)
    (hDy : differential y r φ dr dφ =
      Real.sin φ * dr + r * Real.cos φ * dφ) :
    dφ = x r φ / r ^ 2 * differential y r φ dr dφ -
      y r φ / r ^ 2 * differential x r φ dr dφ := by
  rw [hX, hY, hDx, hDy]
  calc
    dφ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * dφ := by
      rw [Real.sin_sq_add_cos_sq, one_mul]
    _ = r * Real.cos φ / r ^ 2 *
          (Real.sin φ * dr + r * Real.cos φ * dφ) -
        r * Real.sin φ / r ^ 2 *
          (Real.cos φ * dr - r * Real.sin φ * dφ) := by
      field_simp [hr] <;> ring

theorem gap5 (u : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ) :
    differential u r φ dr dφ =
      partialX u r φ * dr + partialY u r φ * dφ := by
  rfl

theorem gap6 (x y u : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hr : r ≠ 0)
    (hDr : dr = x r φ / r * differential x r φ dr dφ +
      y r φ / r * differential y r φ dr dφ)
    (hDφ : dφ = x r φ / r ^ 2 * differential y r φ dr dφ -
      y r φ / r ^ 2 * differential x r φ dr dφ) :
    partialX u r φ * dr + partialY u r φ * dφ =
      (x r φ / r * partialX u r φ -
          y r φ / r ^ 2 * partialY u r φ) *
            differential x r φ dr dφ +
        (y r φ / r * partialX u r φ +
          x r φ / r ^ 2 * partialY u r φ) *
            differential y r φ dr dφ := by
  calc
    partialX u r φ * dr + partialY u r φ * dφ =
        partialX u r φ *
            (x r φ / r * differential x r φ dr dφ +
              y r φ / r * differential y r φ dr dφ) +
          partialY u r φ *
            (x r φ / r ^ 2 * differential y r φ dr dφ -
              y r φ / r ^ 2 * differential x r φ dr dφ) := by
      exact congrArg₂
        (fun a b : ℝ => partialX u r φ * a + partialY u r φ * b)
        hDr hDφ
    _ = (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) *
              differential x r φ dr dφ +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) *
              differential y r φ dr dφ := by
      ring

theorem gap7 (x y u : ℝ → ℝ → ℝ) (r φ dr dφ : ℝ)
    (hDu : differential u r φ dr dφ =
      partialX u r φ * dr + partialY u r φ * dφ)
    (hSubstitution :
      partialX u r φ * dr + partialY u r φ * dφ =
        (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) *
              differential x r φ dr dφ +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) *
              differential y r φ dr dφ) :
    differential u r φ dr dφ =
      (x r φ / r * partialX u r φ -
          y r φ / r ^ 2 * partialY u r φ) *
            differential x r φ dr dφ +
        (y r φ / r * partialX u r φ +
          x r φ / r ^ 2 * partialY u r φ) *
            differential y r φ dr dφ := by
  exact hDu.trans hSubstitution

theorem gap8 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hForm : ∀ dx dy,
      differential U (x r φ) (y r φ) dx dy =
        (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) * dx +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) * dy) :
    partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ -
        y r φ / r ^ 2 * partialY u r φ := by
  simpa [differential] using hForm 1 0

theorem gap9 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hForm : ∀ dx dy,
      differential U (x r φ) (y r φ) dx dy =
        (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) * dx +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) * dy) :
    partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ +
        x r φ / r ^ 2 * partialY u r φ := by
  simpa [differential] using hForm 0 1

theorem gap10 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hUx : partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ -
        y r φ / r ^ 2 * partialY u r φ)
    (hUy : partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ +
        x r φ / r ^ 2 * partialY u r φ) :
    x r φ * partialY U (x r φ) (y r φ) -
        y r φ * partialX U (x r φ) (y r φ) =
      x r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) -
        y r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) := by
  rw [hUx, hUy]

theorem gap11 (x y u : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hRadius : x r φ ^ 2 + y r φ ^ 2 = r ^ 2) :
    x r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) -
        y r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) =
      partialY u r φ := by
  calc
    x r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) -
        y r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) =
        (x r φ ^ 2 + y r φ ^ 2) / r ^ 2 *
          partialY u r φ := by ring
    _ = partialY u r φ := by
      rw [hRadius]
      simp [hr]

theorem gap12 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hSubstitution :
      x r φ * partialY U (x r φ) (y r φ) -
          y r φ * partialX U (x r φ) (y r φ) =
        x r φ *
            (y r φ / r * partialX u r φ +
              x r φ / r ^ 2 * partialY u r φ) -
          y r φ *
            (x r φ / r * partialX u r φ -
              y r φ / r ^ 2 * partialY u r φ))
    (hSimplify :
      x r φ *
            (y r φ / r * partialX u r φ +
              x r φ / r ^ 2 * partialY u r φ) -
          y r φ *
            (x r φ / r * partialX u r φ -
              y r φ / r ^ 2 * partialY u r φ) =
        partialY u r φ) :
    x r φ * partialY U (x r φ) (y r φ) -
      y r φ * partialX U (x r φ) (y r φ) = partialY u r φ := by
  exact hSubstitution.trans hSimplify

end

end ProofGap.Exercise3481
