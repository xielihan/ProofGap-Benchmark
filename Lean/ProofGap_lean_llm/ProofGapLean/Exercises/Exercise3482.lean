import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3482

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

private theorem polar_partial_transform
    (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hUDiff : DifferentiableAt ℝ (Function.uncurry U) (x r φ, y r φ))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      x p.1 p.2 = p.1 * Real.cos p.2)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      y p.1 p.2 = p.1 * Real.sin p.2)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      u p.1 p.2 = U (x p.1 p.2) (y p.1 p.2)) :
    partialX U (x r φ) (y r φ) =
        x r φ / r * partialX u r φ -
          y r φ / r ^ 2 * partialY u r φ ∧
      partialY U (x r φ) (y r φ) =
        y r φ / r * partialX u r φ +
          x r φ / r ^ 2 * partialY u r φ := by
  have chain_rule :
      ∀ (p q : ℝ → ℝ) (t dp dq : ℝ),
        DifferentiableAt ℝ (Function.uncurry U) (p t, q t) →
        HasDerivAt p dp t →
        HasDerivAt q dq t →
        HasDerivAt (fun s => U (p s) (q s))
          (dp * partialX U (p t) (q t) +
            dq * partialY U (p t) (q t)) t := by
    intro p q t dp dq hDiff hp hq
    have pair_deriv :
        ∀ (a b : ℝ → ℝ) (s da db : ℝ),
          HasDerivAt a da s →
          HasDerivAt b db s →
          HasDerivAt (fun z => (a z, b z)) (da, db) s := by
      intro a b s da db ha hb
      have hsum :
          HasDerivAt
            (fun z =>
              a z • ((1, 0) : ℝ × ℝ) +
                b z • ((0, 1) : ℝ × ℝ))
            (da • ((1, 0) : ℝ × ℝ) +
              db • ((0, 1) : ℝ × ℝ)) s :=
        (ha.smul_const ((1, 0) : ℝ × ℝ)).add
          (hb.smul_const ((0, 1) : ℝ × ℝ))
      have hfun :
          (fun z =>
            a z • ((1, 0) : ℝ × ℝ) +
              b z • ((0, 1) : ℝ × ℝ)) =
            (fun z => (a z, b z)) := by
        funext z
        ext <;> simp
      have hder :
          da • ((1, 0) : ℝ × ℝ) +
              db • ((0, 1) : ℝ × ℝ) =
            (da, db) := by
        ext <;> simp
      simpa only [hfun, hder] using hsum
    let L : (ℝ × ℝ) →L[ℝ] ℝ :=
      fderiv ℝ (Function.uncurry U) (p t, q t)
    have hUL : HasFDerivAt (Function.uncurry U) L (p t, q t) := by
      simpa [L] using hDiff.hasFDerivAt
    have hsx :
        HasDerivAt (fun z : ℝ => U z (q t)) (L (1, 0)) (p t) := by
      have hinner :
          HasDerivAt (fun z : ℝ => (z, q t)) (1, 0) (p t) :=
        pair_deriv
          (fun z : ℝ => z) (fun _ : ℝ => q t)
          (p t) 1 0
          (hasDerivAt_id (p t))
          (hasDerivAt_const (x := p t) (c := q t))
      have hcomp := hUL.comp (p t) hinner.hasFDerivAt
      simpa [Function.comp_def, Function.uncurry] using hcomp.hasDerivAt
    have hsy :
        HasDerivAt (fun z : ℝ => U (p t) z) (L (0, 1)) (q t) := by
      have hinner :
          HasDerivAt (fun z : ℝ => (p t, z)) (0, 1) (q t) :=
        pair_deriv
          (fun _ : ℝ => p t) (fun z : ℝ => z)
          (q t) 0 1
          (hasDerivAt_const (x := q t) (c := p t))
          (hasDerivAt_id (q t))
      have hcomp := hUL.comp (q t) hinner.hasFDerivAt
      simpa [Function.comp_def, Function.uncurry] using hcomp.hasDerivAt
    have hLx : L (1, 0) = partialX U (p t) (q t) := by
      simpa [partialX] using hsx.deriv.symm
    have hLy : L (0, 1) = partialY U (p t) (q t) := by
      simpa [partialY] using hsy.deriv.symm
    have hpath :
        HasDerivAt (fun z : ℝ => (p z, q z)) (dp, dq) t :=
      pair_deriv p q t dp dq hp hq
    have hcomp :
        HasDerivAt (fun z => U (p z) (q z)) (L (dp, dq)) t := by
      have hc := hUL.comp t hpath.hasFDerivAt
      simpa [Function.comp_def, Function.uncurry] using hc.hasDerivAt
    have hlin :
        L (dp, dq) =
          dp * partialX U (p t) (q t) +
            dq * partialY U (p t) (q t) := by
      have hdecomp :
          (dp, dq) =
            dp • ((1, 0) : ℝ × ℝ) +
              dq • ((0, 1) : ℝ × ℝ) := by
        ext <;> simp
      calc
        L (dp, dq) =
            L (dp • ((1, 0) : ℝ × ℝ) +
              dq • ((0, 1) : ℝ × ℝ)) :=
          congrArg (fun v : ℝ × ℝ => L v) hdecomp
        _ = L (dp • ((1, 0) : ℝ × ℝ)) +
              L (dq • ((0, 1) : ℝ × ℝ)) := by
          exact L.map_add _ _
        _ = dp • L ((1, 0) : ℝ × ℝ) +
              dq • L ((0, 1) : ℝ × ℝ) := by
          simp only [map_smul]
        _ = dp * partialX U (p t) (q t) +
              dq * partialY U (p t) (q t) := by
          simp [hLx, hLy]
    rw [hlin] at hcomp
    exact hcomp
  have hx0 : x r φ = r * Real.cos φ := by
    simpa using hX.self_of_nhds
  have hy0 : y r φ = r * Real.sin φ := by
    simpa using hY.self_of_nhds
  have hUDiff0 :
      DifferentiableAt ℝ (Function.uncurry U)
        (r * Real.cos φ, r * Real.sin φ) := by
    simpa [hx0, hy0] using hUDiff
  have hpathR : ContinuousAt (fun t : ℝ => (t, φ)) r := by
    simpa only [id_eq] using
      ((continuousAt_id : ContinuousAt (fun t : ℝ => t) r).prodMk
        (continuousAt_const : ContinuousAt (fun _ : ℝ => φ) r))
  have hpathPhi : ContinuousAt (fun t : ℝ => (r, t)) φ := by
    simpa only [id_eq] using
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => r) φ).prodMk
        (continuousAt_id : ContinuousAt (fun t : ℝ => t) φ))
  have hComposeR :
      (fun t : ℝ => u t φ) =ᶠ[nhds r]
        (fun t => U (x t φ) (y t φ)) := by
    simpa [Function.comp_def] using (hpathR hCompose)
  have hXR :
      (fun t : ℝ => x t φ) =ᶠ[nhds r]
        (fun t => t * Real.cos φ) := by
    simpa [Function.comp_def] using (hpathR hX)
  have hYR :
      (fun t : ℝ => y t φ) =ᶠ[nhds r]
        (fun t => t * Real.sin φ) := by
    simpa [Function.comp_def] using (hpathR hY)
  have huR :
      (fun t : ℝ => u t φ) =ᶠ[nhds r]
        (fun t => U (t * Real.cos φ) (t * Real.sin φ)) := by
    filter_upwards [hComposeR, hXR, hYR] with t hC hxt hyt
    simpa [hxt, hyt] using hC
  have hComposePhi :
      (fun t : ℝ => u r t) =ᶠ[nhds φ]
        (fun t => U (x r t) (y r t)) := by
    simpa [Function.comp_def] using (hpathPhi hCompose)
  have hXPhi :
      (fun t : ℝ => x r t) =ᶠ[nhds φ]
        (fun t => r * Real.cos t) := by
    simpa [Function.comp_def] using (hpathPhi hX)
  have hYPhi :
      (fun t : ℝ => y r t) =ᶠ[nhds φ]
        (fun t => r * Real.sin t) := by
    simpa [Function.comp_def] using (hpathPhi hY)
  have huPhi :
      (fun t : ℝ => u r t) =ᶠ[nhds φ]
        (fun t => U (r * Real.cos t) (r * Real.sin t)) := by
    filter_upwards [hComposePhi, hXPhi, hYPhi] with t hC hxt hyt
    simpa [hxt, hyt] using hC
  have hpR :
      HasDerivAt (fun t : ℝ => t * Real.cos φ) (Real.cos φ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.cos φ)
  have hqR :
      HasDerivAt (fun t : ℝ => t * Real.sin φ) (Real.sin φ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.sin φ)
  have hpPhi :
      HasDerivAt (fun t : ℝ => r * Real.cos t)
        (r * (-Real.sin φ)) φ := by
    simpa using (Real.hasDerivAt_cos φ).const_mul r
  have hqPhi :
      HasDerivAt (fun t : ℝ => r * Real.sin t)
        (r * Real.cos φ) φ := by
    simpa using (Real.hasDerivAt_sin φ).const_mul r
  have hPolarR :
      HasDerivAt
        (fun t : ℝ => U (t * Real.cos φ) (t * Real.sin φ))
        (Real.cos φ *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          Real.sin φ *
            partialY U (r * Real.cos φ) (r * Real.sin φ)) r := by
    exact chain_rule
      (fun t : ℝ => t * Real.cos φ)
      (fun t : ℝ => t * Real.sin φ)
      r (Real.cos φ) (Real.sin φ) hUDiff0 hpR hqR
  have hPolarPhi :
      HasDerivAt
        (fun t : ℝ => U (r * Real.cos t) (r * Real.sin t))
        ((r * (-Real.sin φ)) *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          (r * Real.cos φ) *
            partialY U (r * Real.cos φ) (r * Real.sin φ)) φ := by
    exact chain_rule
      (fun t : ℝ => r * Real.cos t)
      (fun t : ℝ => r * Real.sin t)
      φ (r * (-Real.sin φ)) (r * Real.cos φ)
      hUDiff0 hpPhi hqPhi
  have huDerivR :
      HasDerivAt (fun t : ℝ => u t φ)
        (Real.cos φ *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          Real.sin φ *
            partialY U (r * Real.cos φ) (r * Real.sin φ)) r :=
    hPolarR.congr_of_eventuallyEq huR
  have huDerivPhi :
      HasDerivAt (fun t : ℝ => u r t)
        ((r * (-Real.sin φ)) *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          (r * Real.cos φ) *
            partialY U (r * Real.cos φ) (r * Real.sin φ)) φ :=
    hPolarPhi.congr_of_eventuallyEq huPhi
  have hRderiv :
      partialX u r φ =
        Real.cos φ *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          Real.sin φ *
            partialY U (r * Real.cos φ) (r * Real.sin φ) := by
    simpa [partialX] using huDerivR.deriv
  have hPhiDeriv :
      partialY u r φ =
        (r * (-Real.sin φ)) *
            partialX U (r * Real.cos φ) (r * Real.sin φ) +
          (r * Real.cos φ) *
            partialY U (r * Real.cos φ) (r * Real.sin φ) := by
    simpa [partialY] using huDerivPhi.deriv
  have htrig : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
    simpa only [add_comm] using Real.sin_sq_add_cos_sq φ
  constructor
  · rw [hx0, hy0, hRderiv, hPhiDeriv]
    calc
      partialX U (r * Real.cos φ) (r * Real.sin φ) =
          (Real.cos φ ^ 2 + Real.sin φ ^ 2) *
            partialX U (r * Real.cos φ) (r * Real.sin φ) := by
              simp [htrig]
      _ = _ := by
        field_simp [hr] <;> ring
  · rw [hx0, hy0, hRderiv, hPhiDeriv]
    calc
      partialY U (r * Real.cos φ) (r * Real.sin φ) =
          (Real.cos φ ^ 2 + Real.sin φ ^ 2) *
            partialY U (r * Real.cos φ) (r * Real.sin φ) := by
              simp [htrig]
      _ = _ := by
        field_simp [hr] <;> ring

theorem gap1 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (r, φ))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (r, φ))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (r, φ))
    (hUDiff : DifferentiableAt ℝ (Function.uncurry U) (x r φ, y r φ))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      x p.1 p.2 = p.1 * Real.cos p.2)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      y p.1 p.2 = p.1 * Real.sin p.2)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      u p.1 p.2 = U (x p.1 p.2) (y p.1 p.2)) :
    partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ -
        y r φ / r ^ 2 * partialY u r φ := by
  exact
    (polar_partial_transform x y u U r φ hr hUDiff hX hY hCompose).1

theorem gap2 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (r, φ))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (r, φ))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (r, φ))
    (hUDiff : DifferentiableAt ℝ (Function.uncurry U) (x r φ, y r φ))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      x p.1 p.2 = p.1 * Real.cos p.2)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      y p.1 p.2 = p.1 * Real.sin p.2)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (r, φ),
      u p.1 p.2 = U (x p.1 p.2) (y p.1 p.2)) :
    partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ +
        x r φ / r ^ 2 * partialY u r φ := by
  exact
    (polar_partial_transform x y u U r φ hr hUDiff hX hY hCompose).2

theorem gap3 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hUx : partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ -
        y r φ / r ^ 2 * partialY u r φ)
    (hUy : partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ +
        x r φ / r ^ 2 * partialY u r φ) :
    x r φ * partialX U (x r φ) (y r φ) +
        y r φ * partialY U (x r φ) (y r φ) =
      x r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) +
        y r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) := by
  rw [hUx, hUy]

theorem gap4 (x y u : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hRadius : x r φ ^ 2 + y r φ ^ 2 = r ^ 2) :
    x r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) +
        y r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) =
      r * partialX u r φ := by
  calc
    x r φ *
          (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) +
        y r φ *
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) =
        (x r φ ^ 2 + y r φ ^ 2) / r * partialX u r φ := by
          field_simp [hr] <;> ring
    _ = r * partialX u r φ := by
      rw [hRadius]
      field_simp [hr] <;> ring

theorem gap5 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hSubstitution :
      x r φ * partialX U (x r φ) (y r φ) +
          y r φ * partialY U (x r φ) (y r φ) =
        x r φ *
            (x r φ / r * partialX u r φ -
              y r φ / r ^ 2 * partialY u r φ) +
          y r φ *
            (y r φ / r * partialX u r φ +
              x r φ / r ^ 2 * partialY u r φ))
    (hSimplify :
      x r φ *
            (x r φ / r * partialX u r φ -
              y r φ / r ^ 2 * partialY u r φ) +
          y r φ *
            (y r φ / r * partialX u r φ +
              x r φ / r ^ 2 * partialY u r φ) =
        r * partialX u r φ) :
    x r φ * partialX U (x r φ) (y r φ) +
      y r φ * partialY U (x r φ) (y r φ) = r * partialX u r φ := by
  exact hSubstitution.trans hSimplify

end

end ProofGap.Exercise3482
