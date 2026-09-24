import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3491

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX (partialX f) x y

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialX f) x y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialY f) x y

private theorem tendsto_real_id {x : ℝ} :
    Filter.Tendsto (fun t : ℝ => t) (nhds x) (nhds x) := by
  intro s hs
  exact hs

theorem gap1 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = Real.log p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = Real.log p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialX Z x y = 1 / x * partialX z (u x y) (v x y) := by
  have hu : u x y = Real.log x := hU.self_of_nhds
  have hv : v x y = Real.log y := hV.self_of_nhds
  have hpath :
      Filter.Tendsto (fun t : ℝ => (t, y)) (nhds x) (nhds (x, y)) := by
    rw [nhds_prod_eq]
    exact
      (tendsto_real_id (x := x) :
        Filter.Tendsto (fun t : ℝ => t) (nhds x) (nhds x)).prodMk
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => y) (nhds x) (nhds y))
  have heq :
      (fun t : ℝ => Z t y) =ᶠ[nhds x]
        (fun t : ℝ => z (Real.log t) (Real.log y)) := by
    exact
      ((hpath.eventually hCompose).and
        ((hpath.eventually hU).and (hpath.eventually hV))).mono (by
          intro t ht
          rcases ht with ⟨hcomp, hut, hvt⟩
          simp only [Prod.fst, Prod.snd] at hcomp hut hvt ⊢
          calc
            Z t y = z (u t y) (v t y) := hcomp
            _ = z (Real.log t) (Real.log y) := by rw [hut, hvt])
  rw [hu, hv] at hDiffz ⊢
  have hcurve :
      DifferentiableAt ℝ (fun t : ℝ => (t, Real.log y)) (Real.log x) := by
    exact
      (((hasDerivAt_id (Real.log x)).hasFDerivAt.prodMk
        (hasDerivAt_const (x := Real.log x) (Real.log y)).hasFDerivAt).differentiableAt)
  have hz :
      DifferentiableAt ℝ (fun t : ℝ => z t (Real.log y)) (Real.log x) := by
    simpa [Function.comp_def] using
      (hDiffz.comp (Real.log x) hcurve)
  have hderiv :
      HasDerivAt (fun t : ℝ => z (Real.log t) (Real.log y))
        (partialX z (Real.log x) (Real.log y) * (1 / x)) x := by
    simpa [partialX, one_div] using
      hz.hasDerivAt.comp x (Real.hasDerivAt_log hx.ne')
  change deriv (fun t : ℝ => Z t y) x = _
  rw [heq.deriv_eq]
  simpa [mul_comm] using hderiv.deriv

theorem gap2 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = Real.log p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = Real.log p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialY Z x y = 1 / y * partialY z (u x y) (v x y) := by
  have hu : u x y = Real.log x := hU.self_of_nhds
  have hv : v x y = Real.log y := hV.self_of_nhds
  have hpath :
      Filter.Tendsto (fun t : ℝ => (x, t)) (nhds y) (nhds (x, y)) := by
    rw [nhds_prod_eq]
    exact
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => x) (nhds y) (nhds x)).prodMk
        (tendsto_real_id (x := y) :
          Filter.Tendsto (fun t : ℝ => t) (nhds y) (nhds y))
  have heq :
      (fun t : ℝ => Z x t) =ᶠ[nhds y]
        (fun t : ℝ => z (Real.log x) (Real.log t)) := by
    exact
      ((hpath.eventually hCompose).and
        ((hpath.eventually hU).and (hpath.eventually hV))).mono (by
          intro t ht
          rcases ht with ⟨hcomp, hut, hvt⟩
          simp only [Prod.fst, Prod.snd] at hcomp hut hvt ⊢
          calc
            Z x t = z (u x t) (v x t) := hcomp
            _ = z (Real.log x) (Real.log t) := by rw [hut, hvt])
  rw [hu, hv] at hDiffz ⊢
  have hcurve :
      DifferentiableAt ℝ (fun t : ℝ => (Real.log x, t)) (Real.log y) := by
    exact
      (((hasDerivAt_const (x := Real.log y) (Real.log x)).hasFDerivAt.prodMk
        (hasDerivAt_id (Real.log y)).hasFDerivAt).differentiableAt)
  have hz :
      DifferentiableAt ℝ (fun t : ℝ => z (Real.log x) t) (Real.log y) := by
    simpa [Function.comp_def] using
      (hDiffz.comp (Real.log y) hcurve)
  have hderiv :
      HasDerivAt (fun t : ℝ => z (Real.log x) (Real.log t))
        (partialY z (Real.log x) (Real.log y) * (1 / y)) y := by
    simpa [partialY, one_div] using
      hz.hasDerivAt.comp y (Real.hasDerivAt_log hy.ne')
  change deriv (fun t : ℝ => Z x t) y = _
  rw [heq.deriv_eq]
  simpa [mul_comm] using hderiv.deriv

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        1 / p.1 * partialX z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = Real.log p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = Real.log p.2)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y)) :
    partialXY Z x y =
      1 / (x * y) * partialXY z (u x y) (v x y) := by
  have hu : u x y = Real.log x := hU.self_of_nhds
  have hv : v x y = Real.log y := hV.self_of_nhds
  have hpath :
      Filter.Tendsto (fun t : ℝ => (x, t)) (nhds y) (nhds (x, y)) := by
    rw [nhds_prod_eq]
    exact
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => x) (nhds y) (nhds x)).prodMk
        (tendsto_real_id (x := y) :
          Filter.Tendsto (fun t : ℝ => t) (nhds y) (nhds y))
  have heq :
      (fun t : ℝ => partialX Z x t) =ᶠ[nhds y]
        (fun t : ℝ => 1 / x * partialX z (Real.log x) (Real.log t)) := by
    exact
      ((hpath.eventually hZx).and
        ((hpath.eventually hU).and (hpath.eventually hV))).mono (by
          intro t ht
          rcases ht with ⟨hzx, hut, hvt⟩
          simp only [Prod.fst, Prod.snd] at hzx hut hvt ⊢
          calc
            partialX Z x t = 1 / x * partialX z (u x t) (v x t) := hzx
            _ = 1 / x * partialX z (Real.log x) (Real.log t) := by
              rw [hut, hvt])
  rw [hu, hv] at hDiffZu ⊢
  have hcurve :
      DifferentiableAt ℝ (fun t : ℝ => (Real.log x, t)) (Real.log y) := by
    exact
      (((hasDerivAt_const (x := Real.log y) (Real.log x)).hasFDerivAt.prodMk
        (hasDerivAt_id (Real.log y)).hasFDerivAt).differentiableAt)
  have hz :
      DifferentiableAt ℝ
        (fun t : ℝ => partialX z (Real.log x) t) (Real.log y) := by
    simpa [Function.comp_def] using
      (hDiffZu.comp (Real.log y) hcurve)
  have hinner :
      HasDerivAt
        (fun t : ℝ => partialX z (Real.log x) (Real.log t))
        (partialXY z (Real.log x) (Real.log y) * (1 / y)) y := by
    simpa [partialXY, partialY, one_div] using
      hz.hasDerivAt.comp y (Real.hasDerivAt_log hy)
  have hprod :
      HasDerivAt
        (fun t : ℝ => 1 / x * partialX z (Real.log x) (Real.log t))
        ((1 / x) *
          (partialXY z (Real.log x) (Real.log y) * (1 / y))) y := by
    simpa using (hasDerivAt_const (x := y) (1 / x)).mul hinner
  change deriv (fun t : ℝ => partialX Z x t) y = _
  rw [heq.deriv_eq, hprod.deriv]
  field_simp [hx, hy]

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        1 / p.1 * partialX z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = Real.log p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = Real.log p.2)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y)) :
    partialXX Z x y =
      -(1 / x ^ 2) * partialX z (u x y) (v x y) +
        1 / x ^ 2 * partialXX z (u x y) (v x y) := by
  have hu : u x y = Real.log x := hU.self_of_nhds
  have hv : v x y = Real.log y := hV.self_of_nhds
  have hpath :
      Filter.Tendsto (fun t : ℝ => (t, y)) (nhds x) (nhds (x, y)) := by
    rw [nhds_prod_eq]
    exact
      (tendsto_real_id (x := x) :
        Filter.Tendsto (fun t : ℝ => t) (nhds x) (nhds x)).prodMk
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => y) (nhds x) (nhds y))
  have heq :
      (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
        (fun t : ℝ => t⁻¹ * partialX z (Real.log t) (Real.log y)) := by
    exact
      ((hpath.eventually hZx).and
        ((hpath.eventually hU).and (hpath.eventually hV))).mono (by
          intro t ht
          rcases ht with ⟨hzx, hut, hvt⟩
          simp only [Prod.fst, Prod.snd] at hzx hut hvt ⊢
          calc
            partialX Z t y = 1 / t * partialX z (u t y) (v t y) := hzx
            _ = t⁻¹ * partialX z (Real.log t) (Real.log y) := by
              rw [hut, hvt]
              simp [one_div])
  rw [hu, hv] at hDiffZu ⊢
  have hcurve :
      DifferentiableAt ℝ (fun t : ℝ => (t, Real.log y)) (Real.log x) := by
    exact
      (((hasDerivAt_id (Real.log x)).hasFDerivAt.prodMk
        (hasDerivAt_const (x := Real.log x) (Real.log y)).hasFDerivAt).differentiableAt)
  have hz :
      DifferentiableAt ℝ
        (fun t : ℝ => partialX z t (Real.log y)) (Real.log x) := by
    simpa [Function.comp_def] using
      (hDiffZu.comp (Real.log x) hcurve)
  have hinner :
      HasDerivAt
        (fun t : ℝ => partialX z (Real.log t) (Real.log y))
        (partialXX z (Real.log x) (Real.log y) * (1 / x)) x := by
    simpa [partialXX, partialX, one_div] using
      hz.hasDerivAt.comp x (Real.hasDerivAt_log hx)
  have hd := (((hasDerivAt_id x).inv hx).mul hinner).deriv
  change
    deriv
        (fun t : ℝ => t⁻¹ * partialX z (Real.log t) (Real.log y)) x = _ at hd
  simp only [Pi.inv_apply, id_eq] at hd
  change deriv (fun t : ℝ => partialX Z t y) x = _
  rw [heq.deriv_eq, hd]
  field_simp [hx] <;> ring

theorem gap5 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : y ≠ 0)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        1 / p.2 * partialY z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = Real.log p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = Real.log p.2)
    (hDiffZv :
      DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y)) :
    partialYY Z x y =
      -(1 / y ^ 2) * partialY z (u x y) (v x y) +
        1 / y ^ 2 * partialYY z (u x y) (v x y) := by
  have hu : u x y = Real.log x := hU.self_of_nhds
  have hv : v x y = Real.log y := hV.self_of_nhds
  have hpath :
      Filter.Tendsto (fun t : ℝ => (x, t)) (nhds y) (nhds (x, y)) := by
    rw [nhds_prod_eq]
    exact
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => x) (nhds y) (nhds x)).prodMk
        (tendsto_real_id (x := y) :
          Filter.Tendsto (fun t : ℝ => t) (nhds y) (nhds y))
  have heq :
      (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
        (fun t : ℝ => t⁻¹ * partialY z (Real.log x) (Real.log t)) := by
    exact
      ((hpath.eventually hZy).and
        ((hpath.eventually hU).and (hpath.eventually hV))).mono (by
          intro t ht
          rcases ht with ⟨hzy, hut, hvt⟩
          simp only [Prod.fst, Prod.snd] at hzy hut hvt ⊢
          calc
            partialY Z x t = 1 / t * partialY z (u x t) (v x t) := hzy
            _ = t⁻¹ * partialY z (Real.log x) (Real.log t) := by
              rw [hut, hvt]
              simp [one_div])
  rw [hu, hv] at hDiffZv ⊢
  have hcurve :
      DifferentiableAt ℝ (fun t : ℝ => (Real.log x, t)) (Real.log y) := by
    exact
      (((hasDerivAt_const (x := Real.log y) (Real.log x)).hasFDerivAt.prodMk
        (hasDerivAt_id (Real.log y)).hasFDerivAt).differentiableAt)
  have hz :
      DifferentiableAt ℝ
        (fun t : ℝ => partialY z (Real.log x) t) (Real.log y) := by
    simpa [Function.comp_def] using
      (hDiffZv.comp (Real.log y) hcurve)
  have hinner :
      HasDerivAt
        (fun t : ℝ => partialY z (Real.log x) (Real.log t))
        (partialYY z (Real.log x) (Real.log y) * (1 / y)) y := by
    simpa [partialYY, partialY, one_div] using
      hz.hasDerivAt.comp y (Real.hasDerivAt_log hy)
  have hd := (((hasDerivAt_id y).inv hy).mul hinner).deriv
  change
    deriv
        (fun t : ℝ => t⁻¹ * partialY z (Real.log x) (Real.log t)) y = _ at hd
  simp only [Pi.inv_apply, id_eq] at hd
  change deriv (fun t : ℝ => partialY Z x t) y = _
  rw [heq.deriv_eq, hd]
  field_simp [hy] <;> ring

theorem gap6 (a b c : ℝ) (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hPDE :
      a * x ^ 2 * partialXX Z x y +
          2 * b * x * y * partialXY Z x y +
          c * y ^ 2 * partialYY Z x y = 0)
    (hZxx :
      partialXX Z x y =
        -(1 / x ^ 2) * partialX z (u x y) (v x y) +
          1 / x ^ 2 * partialXX z (u x y) (v x y))
    (hZxy :
      partialXY Z x y =
        1 / (x * y) * partialXY z (u x y) (v x y))
    (hZyy :
      partialYY Z x y =
        -(1 / y ^ 2) * partialY z (u x y) (v x y) +
          1 / y ^ 2 * partialYY z (u x y) (v x y)) :
    a * (partialXX z (u x y) (v x y) - partialX z (u x y) (v x y)) +
        2 * b * partialXY z (u x y) (v x y) +
        c * (partialYY z (u x y) (v x y) - partialY z (u x y) (v x y)) = 0 := by
  calc
    a * (partialXX z (u x y) (v x y) -
          partialX z (u x y) (v x y)) +
        2 * b * partialXY z (u x y) (v x y) +
        c * (partialYY z (u x y) (v x y) -
          partialY z (u x y) (v x y)) =
      a * x ^ 2 * partialXX Z x y +
          2 * b * x * y * partialXY Z x y +
          c * y ^ 2 * partialYY Z x y := by
            rw [hZxx, hZxy, hZyy]
            field_simp [hx, hy]
            ring
    _ = 0 := hPDE

end

end ProofGap.Exercise3491
