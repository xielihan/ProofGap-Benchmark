import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ProofGap.Exercise3508

noncomputable section

open Filter

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f t y z) x

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f x t z) y

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x t z) y

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x y t) z

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial3 f x y t) z

def partial31 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial3 f t y z) x

def forwardX (ξ η ζ : ℝ) : ℝ := η * ζ

def forwardY (ξ η ζ : ℝ) : ℝ := ξ * ζ

def forwardZ (ξ η ζ : ℝ) : ℝ := ξ * η

def C2 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial1 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial2 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial3 f p.1 p.2.1 p.2.2)

def IsLocalInverse
    (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : Prop :=
  ξ ≠ 0 ∧ η ≠ 0 ∧ ζ ≠ 0 ∧
    DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => xi p.1 p.2.1 p.2.2)
      (forwardX ξ η ζ, (forwardY ξ η ζ, forwardZ ξ η ζ)) ∧
    DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => eta p.1 p.2.1 p.2.2)
      (forwardX ξ η ζ, (forwardY ξ η ζ, forwardZ ξ η ζ)) ∧
    DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => zeta p.1 p.2.1 p.2.2)
      (forwardX ξ η ζ, (forwardY ξ η ζ, forwardZ ξ η ζ)) ∧
    -- Statement correction: use one genuine product neighborhood.
    (∀ᶠ p : ℝ × (ℝ × ℝ) in nhds (ξ, (η, ζ)),
      xi (forwardX p.1 p.2.1 p.2.2)
          (forwardY p.1 p.2.1 p.2.2) (forwardZ p.1 p.2.1 p.2.2) = p.1 ∧
      eta (forwardX p.1 p.2.1 p.2.2)
          (forwardY p.1 p.2.1 p.2.2) (forwardZ p.1 p.2.1 p.2.2) = p.2.1 ∧
      zeta (forwardX p.1 p.2.1 p.2.2)
          (forwardY p.1 p.2.1 p.2.2) (forwardZ p.1 p.2.1 p.2.2) = p.2.2)

def IsLocalPullback
    (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : Prop :=
  -- Statement correction: use one genuine product neighborhood.
  (∀ᶠ p : ℝ × (ℝ × ℝ) in
      nhds (forwardX ξ η ζ, (forwardY ξ η ζ, forwardZ ξ η ζ)),
    f p.1 p.2.1 p.2.2 =
      F (xi p.1 p.2.1 p.2.2) (eta p.1 p.2.1 p.2.2)
        (zeta p.1 p.2.1 p.2.2)) ∧ C2 F

def mixedXYFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  -1 / (4 * η * ζ ^ 2) * partial1 F ξ η ζ -
    ξ / (4 * η * ζ ^ 2) * partial11 F ξ η ζ -
    1 / (4 * ξ * ζ ^ 2) * partial2 F ξ η ζ -
    η / (4 * ξ * ζ ^ 2) * partial22 F ξ η ζ +
    1 / (4 * ξ * η * ζ) * partial3 F ξ η ζ +
    1 / (4 * ξ * η) * partial33 F ξ η ζ +
    1 / (2 * ζ ^ 2) * partial12 F ξ η ζ

def mixedYZFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  1 / (4 * ξ * η * ζ) * partial1 F ξ η ζ +
    1 / (4 * η * ζ) * partial11 F ξ η ζ -
    1 / (4 * ξ ^ 2 * ζ) * partial2 F ξ η ζ -
    η / (4 * ξ ^ 2 * ζ) * partial22 F ξ η ζ -
    1 / (4 * ξ ^ 2 * η) * partial3 F ξ η ζ -
    ζ / (4 * ξ ^ 2 * η) * partial33 F ξ η ζ +
    1 / (2 * ξ ^ 2) * partial23 F ξ η ζ

def mixedZXFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  -1 / (4 * η ^ 2 * ζ) * partial1 F ξ η ζ -
    ξ / (4 * η ^ 2 * ζ) * partial11 F ξ η ζ +
    1 / (4 * ξ * η * ζ) * partial2 F ξ η ζ +
    1 / (4 * ξ * ζ) * partial22 F ξ η ζ -
    1 / (4 * η ^ 2 * ξ) * partial3 F ξ η ζ -
    ζ / (4 * η ^ 2 * ξ) * partial33 F ξ η ζ +
    1 / (2 * η ^ 2) * partial31 F ξ η ζ

def physicalPDE (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * y * partial12 f x y z + y * z * partial23 f x y z +
    x * z * partial31 f x y z

def transformedBalance (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : Prop :=
  ξ * partial1 F ξ η ζ + η * partial2 F ξ η ζ + ζ * partial3 F ξ η ζ +
      ξ ^ 2 * partial11 F ξ η ζ + η ^ 2 * partial22 F ξ η ζ +
      ζ ^ 2 * partial33 F ξ η ζ =
    2 * (ξ * η * partial12 F ξ η ζ + η * ζ * partial23 F ξ η ζ +
      ζ * ξ * partial31 F ξ η ζ)

private abbrev Point3 := ℝ × (ℝ × ℝ)

private def forwardMap (p : Point3) : Point3 :=
  (forwardX p.1 p.2.1 p.2.2,
    (forwardY p.1 p.2.1 p.2.2, forwardZ p.1 p.2.1 p.2.2))

private def inverseMap (xi eta zeta : ℝ → ℝ → ℝ → ℝ)
    (p : Point3) : Point3 :=
  (xi p.1 p.2.1 p.2.2,
    (eta p.1 p.2.1 p.2.2, zeta p.1 p.2.1 p.2.2))

private def forwardJacobianEquiv (ξ η ζ : ℝ)
    (hξ : ξ ≠ 0) (hη : η ≠ 0) (hζ : ζ ≠ 0) :
    Point3 ≃ₗ[ℝ] Point3 where
  toFun d :=
    (ζ * d.2.1 + η * d.2.2,
      (ζ * d.1 + ξ * d.2.2, η * d.1 + ξ * d.2.1))
  invFun d :=
    (-ξ / (2 * η * ζ) * d.1 + 1 / (2 * ζ) * d.2.1 +
        1 / (2 * η) * d.2.2,
      (1 / (2 * ζ) * d.1 - η / (2 * ξ * ζ) * d.2.1 +
          1 / (2 * ξ) * d.2.2,
        1 / (2 * η) * d.1 + 1 / (2 * ξ) * d.2.1 -
          ζ / (2 * ξ * η) * d.2.2))
  map_add' a b := by
    ext <;> simp <;> ring
  map_smul' c a := by
    ext <;> simp <;> ring
  left_inv d := by
    ext <;> dsimp
    all_goals field_simp [hξ, hη, hζ] <;> ring
  right_inv d := by
    ext <;> dsimp
    all_goals field_simp [hξ, hη, hζ] <;> ring

private lemma forwardMap_hasFDerivAt (ξ η ζ : ℝ)
    (hξ : ξ ≠ 0) (hη : η ≠ 0) (hζ : ζ ≠ 0) :
    HasFDerivAt forwardMap
      ((forwardJacobianEquiv ξ η ζ hξ hη hζ).toContinuousLinearEquiv :
        Point3 →L[ℝ] Point3) (ξ, (η, ζ)) := by
  have h1 : HasFDerivAt (fun p : Point3 => p.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (ξ, (η, ζ)) :=
    hasFDerivAt_fst
  have h21 : HasFDerivAt (fun p : Point3 => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (ξ, (η, ζ)) := by
    fun_prop
  have h22 : HasFDerivAt (fun p : Point3 => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (ξ, (η, ζ)) := by
    fun_prop
  have h :=
    (h21.mul h22).prodMk
      ((h1.mul h22).prodMk (h1.mul h21))
  convert h using 1
  ext <;> simp [forwardMap, forwardX, forwardY, forwardZ,
    forwardJacobianEquiv]

private lemma inverseMap_hasFDerivAt
    (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    HasFDerivAt (inverseMap xi eta zeta)
      (((forwardJacobianEquiv ξ η ζ hInv.1 hInv.2.1 hInv.2.2.1).toContinuousLinearEquiv
        ).symm : Point3 →L[ℝ] Point3)
      (forwardMap (ξ, (η, ζ))) := by
  have hforward : ContDiffAt ℝ (2 : WithTop ℕ∞) forwardMap (ξ, (η, ζ)) := by
    unfold forwardMap forwardX forwardY forwardZ
    fun_prop
  have hstrict :=
    hforward.hasStrictFDerivAt'
      (forwardMap_hasFDerivAt ξ η ζ hInv.1 hInv.2.1 hInv.2.2.1)
      (by decide)
  have hinv :
      ∀ᶠ p : Point3 in nhds (ξ, (η, ζ)),
        inverseMap xi eta zeta (forwardMap p) = p := by
    filter_upwards [hInv.2.2.2.2.2.2] with p hp
    apply Prod.ext
    · exact hp.1
    · apply Prod.ext
      · exact hp.2.1
      · exact hp.2.2
  exact (hstrict.to_local_left_inverse hinv).hasFDerivAt

private lemma hasDerivAt_comp_three
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ) {t da db dc : ℝ}
    (hF : DifferentiableAt ℝ
      (fun p : Point3 => F p.1 p.2.1 p.2.2)
      (a t, (b t, c t)))
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => F (a s) (b s) (c s))
      (da * partial1 F (a t) (b t) (c t) +
        db * partial2 F (a t) (b t) (c t) +
        dc * partial3 F (a t) (b t) (c t)) t := by
  let G := fun p : Point3 => F p.1 p.2.1 p.2.2
  let L := fderiv ℝ G (a t, (b t, c t))
  let e1 : Point3 := (1, (0, 0))
  let e2 : Point3 := (0, (1, 0))
  let e3 : Point3 := (0, (0, 1))
  have hG : HasFDerivAt G L (a t, (b t, c t)) := hF.hasFDerivAt
  have hcomp := hG.comp t
    (ha.hasFDerivAt.prodMk (hb.hasFDerivAt.prodMk hc.hasFDerivAt))
  have h1 : partial1 F (a t) (b t) (c t) = L e1 := by
    have hs := hG.comp (a t)
      ((hasDerivAt_id (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_const (a t) (b t)).hasFDerivAt.prodMk
          (hasDerivAt_const (a t) (c t)).hasFDerivAt))
    unfold partial1
    simpa [G, L, e1, Function.comp_def] using hs.hasDerivAt.deriv
  have h2 : partial2 F (a t) (b t) (c t) = L e2 := by
    have hs := hG.comp (b t)
      ((hasDerivAt_const (b t) (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_id (b t)).hasFDerivAt.prodMk
          (hasDerivAt_const (b t) (c t)).hasFDerivAt))
    unfold partial2
    simpa [G, L, e2, Function.comp_def] using hs.hasDerivAt.deriv
  have h3 : partial3 F (a t) (b t) (c t) = L e3 := by
    have hs := hG.comp (c t)
      ((hasDerivAt_const (c t) (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_const (c t) (b t)).hasFDerivAt.prodMk
          (hasDerivAt_id (c t)).hasFDerivAt))
    unfold partial3
    simpa [G, L, e3, Function.comp_def] using hs.hasDerivAt.deriv
  have hv : (da, (db, dc)) = da • e1 + db • e2 + dc • e3 := by
    ext <;> simp [e1, e2, e3]
  have hlin : L (da, (db, dc)) =
      da * partial1 F (a t) (b t) (c t) +
        db * partial2 F (a t) (b t) (c t) +
        dc * partial3 F (a t) (b t) (c t) := by
    rw [hv, map_add, map_add, map_smul, map_smul, map_smul,
      ← h1, ← h2, ← h3]
    simp
  have hd : HasDerivAt (fun s => F (a s) (b s) (c s))
      (L (da, (db, dc))) t := by
    simpa [G, Function.comp_def] using hcomp.hasDerivAt
  rwa [hlin] at hd

private def pullXFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  -ξ / (2 * η * ζ) * partial1 F ξ η ζ +
    1 / (2 * ζ) * partial2 F ξ η ζ +
    1 / (2 * η) * partial3 F ξ η ζ

private def pullYFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  1 / (2 * ζ) * partial1 F ξ η ζ -
    η / (2 * ξ * ζ) * partial2 F ξ η ζ +
    1 / (2 * ξ) * partial3 F ξ η ζ

private def pullZFormula (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : ℝ :=
  1 / (2 * η) * partial1 F ξ η ζ +
    1 / (2 * ξ) * partial2 F ξ η ζ -
    ζ / (2 * ξ * η) * partial3 F ξ η ζ

private def gradientMap (F : ℝ → ℝ → ℝ → ℝ) (p : Point3) :
    Point3 →L[ℝ] ℝ :=
  partial1 F p.1 p.2.1 p.2.2 •
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
    partial2 F p.1 p.2.1 p.2.2 •
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
    partial3 F p.1 p.2.1 p.2.2 •
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

private lemma hasFDerivAt_gradientMap
    (F : ℝ → ℝ → ℝ → ℝ) (p : Point3)
    (hF : DifferentiableAt ℝ
      (fun q : Point3 => F q.1 q.2.1 q.2.2) p) :
    HasFDerivAt (fun q : Point3 => F q.1 q.2.1 q.2.2)
      (gradientMap F p) p := by
  let G := fun q : Point3 => F q.1 q.2.1 q.2.2
  let L := fderiv ℝ G p
  let e1 : Point3 := (1, (0, 0))
  let e2 : Point3 := (0, (1, 0))
  let e3 : Point3 := (0, (0, 1))
  have hG : HasFDerivAt G L p := hF.hasFDerivAt
  have h1 : partial1 F p.1 p.2.1 p.2.2 = L e1 := by
    have hs := hG.comp p.1
      ((hasDerivAt_id p.1).hasFDerivAt.prodMk
        ((hasDerivAt_const p.1 p.2.1).hasFDerivAt.prodMk
          (hasDerivAt_const p.1 p.2.2).hasFDerivAt))
    unfold partial1
    simpa [G, L, e1, Function.comp_def] using hs.hasDerivAt.deriv
  have h2 : partial2 F p.1 p.2.1 p.2.2 = L e2 := by
    have hs := hG.comp p.2.1
      ((hasDerivAt_const p.2.1 p.1).hasFDerivAt.prodMk
        ((hasDerivAt_id p.2.1).hasFDerivAt.prodMk
          (hasDerivAt_const p.2.1 p.2.2).hasFDerivAt))
    unfold partial2
    simpa [G, L, e2, Function.comp_def] using hs.hasDerivAt.deriv
  have h3 : partial3 F p.1 p.2.1 p.2.2 = L e3 := by
    have hs := hG.comp p.2.2
      ((hasDerivAt_const p.2.2 p.1).hasFDerivAt.prodMk
        ((hasDerivAt_const p.2.2 p.2.1).hasFDerivAt.prodMk
          (hasDerivAt_id p.2.2).hasFDerivAt))
    unfold partial3
    simpa [G, L, e3, Function.comp_def] using hs.hasDerivAt.deriv
  convert hG using 1
  apply ContinuousLinearMap.ext
  intro d
  have hd : d = d.1 • e1 + d.2.1 • e2 + d.2.2 • e3 := by
    ext <;> simp [e1, e2, e3]
  rw [hd, map_add, map_add, map_smul, map_smul, map_smul]
  simp [gradientMap, e1, e2, e3, h1, h2, h3]
  rw [hd, map_add, map_add, map_smul, map_smul, map_smul]
  simp [e1, e2, e3]

private lemma mixed_partials_of_C2
    (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) (hF : C2 F) :
    partial1 (partial2 F) ξ η ζ = partial12 F ξ η ζ ∧
      partial3 (partial1 F) ξ η ζ = partial31 F ξ η ζ ∧
      partial2 (partial3 F) ξ η ζ = partial23 F ξ η ζ := by
  let G := fun p : Point3 => F p.1 p.2.1 p.2.2
  let u : Point3 := (ξ, (η, ζ))
  have hgrad : Differentiable ℝ (gradientMap F) := by
    unfold gradientMap
    exact
      ((hF.2.1.smul_const
          (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).add
        (hF.2.2.1.smul_const
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).add
      (hF.2.2.2.smul_const
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
  let D := fderiv ℝ (gradientMap F) u
  have hD : HasFDerivAt (gradientMap F) D u :=
    hgrad.differentiableAt.hasFDerivAt
  have hfirst :
      ∀ᶠ p : Point3 in nhds u, HasFDerivAt G (gradientMap F p) p :=
    Eventually.of_forall fun p =>
      hasFDerivAt_gradientMap F p hF.1.differentiableAt
  have hsymm (v w : Point3) : D v w = D w v :=
    second_derivative_symmetric_of_eventually hfirst hD v w
  let e1 : Point3 := (1, (0, 0))
  let e2 : Point3 := (0, (1, 0))
  let e3 : Point3 := (0, (0, 1))
  have evalAlong
      (e : Point3) (path : ℝ → Point3) (t : ℝ) (v : Point3)
      (hpath : HasDerivAt path v t) (hpt : path t = u) :
      HasDerivAt
        (fun s : ℝ => gradientMap F (path s) e)
        (D v e) t := by
    have hD' : HasFDerivAt (gradientMap F) D (path t) := by
      simpa only [hpt] using hD
    have hc := hD'.comp t hpath.hasFDerivAt
    have heval :
        HasFDerivAt (fun L : Point3 →L[ℝ] ℝ => L e)
          (ContinuousLinearMap.apply ℝ ℝ e) (gradientMap F u) :=
      (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt
    have heval' :
        HasFDerivAt (fun L : Point3 →L[ℝ] ℝ => L e)
          (ContinuousLinearMap.apply ℝ ℝ e) (gradientMap F (path t)) := by
      simpa only [hpt] using heval
    simpa [Function.comp_def] using (heval'.comp t hc).hasDerivAt
  have hxPath : HasDerivAt
      (fun t : ℝ => ((t, (η, ζ)) : Point3)) e1 ξ :=
    (hasDerivAt_id ξ).prodMk
      ((hasDerivAt_const ξ η).prodMk (hasDerivAt_const ξ ζ))
  have hyPath : HasDerivAt
      (fun t : ℝ => ((ξ, (t, ζ)) : Point3)) e2 η :=
    (hasDerivAt_const η ξ).prodMk
      ((hasDerivAt_id η).prodMk (hasDerivAt_const η ζ))
  have hzPath : HasDerivAt
      (fun t : ℝ => ((ξ, (η, t)) : Point3)) e3 ζ :=
    (hasDerivAt_const ζ ξ).prodMk
      ((hasDerivAt_const ζ η).prodMk (hasDerivAt_id ζ))
  have h12a := evalAlong e2 _ ξ e1 hxPath rfl
  have h12b := evalAlong e1 _ η e2 hyPath rfl
  have h13a := evalAlong e1 _ ζ e3 hzPath rfl
  have h13b := evalAlong e3 _ ξ e1 hxPath rfl
  have h23a := evalAlong e3 _ η e2 hyPath rfl
  have h23b := evalAlong e2 _ ζ e3 hzPath rfl
  have h12a' : partial1 (partial2 F) ξ η ζ = D e1 e2 := by
    unfold partial1
    simpa [gradientMap, e2] using h12a.deriv
  have h12b' : partial12 F ξ η ζ = D e2 e1 := by
    unfold partial12
    simpa [gradientMap, e1] using h12b.deriv
  have h13a' : partial3 (partial1 F) ξ η ζ = D e3 e1 := by
    unfold partial3
    simpa [gradientMap, e1] using h13a.deriv
  have h13b' : partial31 F ξ η ζ = D e1 e3 := by
    unfold partial31
    simpa [gradientMap, e3] using h13b.deriv
  have h23a' : partial2 (partial3 F) ξ η ζ = D e2 e3 := by
    unfold partial2
    simpa [gradientMap, e3] using h23a.deriv
  have h23b' : partial23 F ξ η ζ = D e3 e2 := by
    unfold partial23
    simpa [gradientMap, e2] using h23b.deriv
  constructor
  · rw [h12a', h12b', hsymm e1 e2]
  constructor
  · rw [h13a', h13b', hsymm e3 e1]
  · rw [h23a', h23b', hsymm e2 e3]

private lemma first_partials_of_local_pullback
    (f F : ℝ → ℝ → ℝ → ℝ) (g : Point3 → Point3)
    (q u : Point3) (hξ : u.1 ≠ 0) (hη : u.2.1 ≠ 0)
    (hζ : u.2.2 ≠ 0) (hgu : g q = u)
    (hF : DifferentiableAt ℝ
      (fun p : Point3 => F p.1 p.2.1 p.2.2) u)
    (hg : HasFDerivAt g
      (((forwardJacobianEquiv u.1 u.2.1 u.2.2 hξ hη hζ).toContinuousLinearEquiv
        ).symm : Point3 →L[ℝ] Point3) q)
    (heq :
      (fun p : Point3 => f p.1 p.2.1 p.2.2) =ᶠ[nhds q]
        (fun p => F (g p).1 (g p).2.1 (g p).2.2)) :
    partial1 f q.1 q.2.1 q.2.2 =
        pullXFormula F u.1 u.2.1 u.2.2 ∧
      partial2 f q.1 q.2.1 q.2.2 =
        pullYFormula F u.1 u.2.1 u.2.2 ∧
      partial3 f q.1 q.2.1 q.2.2 =
        pullZFormula F u.1 u.2.1 u.2.2 := by
  rcases q with ⟨qx, qy, qz⟩
  have hxPath : HasDerivAt
      (fun t : ℝ => ((t, (qy, qz)) : Point3))
      ((1, (0, 0)) : Point3) qx :=
    (hasDerivAt_id qx).prodMk
      ((hasDerivAt_const qx qy).prodMk
        (hasDerivAt_const qx qz))
  have hyPath : HasDerivAt
      (fun t : ℝ => ((qx, (t, qz)) : Point3))
      ((0, (1, 0)) : Point3) qy :=
    (hasDerivAt_const qy qx).prodMk
      ((hasDerivAt_id qy).prodMk
        (hasDerivAt_const qy qz))
  have hzPath : HasDerivAt
      (fun t : ℝ => ((qx, (qy, t)) : Point3))
      ((0, (0, 1)) : Point3) qz :=
    (hasDerivAt_const qz qx).prodMk
      ((hasDerivAt_const qz qy).prodMk
        (hasDerivAt_id qz))
  have proveForPath
      (path : ℝ → Point3) (t : ℝ) (v : Point3)
      (hpath : HasDerivAt path v t) (hpt : path t = (qx, (qy, qz))) :
      HasDerivAt (fun s => (g (path s)).1)
          ((((forwardJacobianEquiv u.1 u.2.1 u.2.2 hξ hη hζ).toContinuousLinearEquiv
            ).symm : Point3 →L[ℝ] Point3) v).1 t ∧
        HasDerivAt (fun s => (g (path s)).2.1)
          ((((forwardJacobianEquiv u.1 u.2.1 u.2.2 hξ hη hζ).toContinuousLinearEquiv
            ).symm : Point3 →L[ℝ] Point3) v).2.1 t ∧
        HasDerivAt (fun s => (g (path s)).2.2)
          ((((forwardJacobianEquiv u.1 u.2.1 u.2.2 hξ hη hζ).toContinuousLinearEquiv
            ).symm : Point3 →L[ℝ] Point3) v).2.2 t := by
    have hg' : HasFDerivAt g
        (((forwardJacobianEquiv u.1 u.2.1 u.2.2 hξ hη hζ).toContinuousLinearEquiv
          ).symm : Point3 →L[ℝ] Point3) (path t) := by
      simpa only [hpt] using hg
    have hc := hg'.comp t hpath.hasFDerivAt
    constructor
    · simpa [Function.comp_def] using
        (hasFDerivAt_fst.comp t hc).hasDerivAt
    constructor
    · have hs := hasFDerivAt_snd.comp t hc
      simpa [Function.comp_def] using
        (hasFDerivAt_fst.comp t hs).hasDerivAt
    · have hs := hasFDerivAt_snd.comp t hc
      simpa [Function.comp_def] using
        (hasFDerivAt_snd.comp t hs).hasDerivAt
  have hdx := proveForPath _ _ _ hxPath rfl
  have hdy := proveForPath _ _ _ hyPath rfl
  have hdz := proveForPath _ _ _ hzPath rfl
  have hFx : DifferentiableAt ℝ
      (fun p : Point3 => F p.1 p.2.1 p.2.2)
      (g (qx, (qy, qz))) := by simpa [hgu] using hF
  constructor
  · have hchain := hasDerivAt_comp_three F
      (fun t => (g (t, (qy, qz))).1)
      (fun t => (g (t, (qy, qz))).2.1)
      (fun t => (g (t, (qy, qz))).2.2)
      hFx hdx.1 hdx.2.1 hdx.2.2
    have hline :
        (fun t => f t qy qz) =ᶠ[nhds qx]
          (fun t => F (g (t, (qy, qz))).1
            (g (t, (qy, qz))).2.1
            (g (t, (qy, qz))).2.2) :=
      hxPath.continuousAt.eventually heq
    unfold partial1 pullXFormula
    rw [hline.deriv_eq, hchain.deriv]
    simp only
    rw [hgu]
    simp [forwardJacobianEquiv]
  constructor
  · have hchain := hasDerivAt_comp_three F
      (fun t => (g (qx, (t, qz))).1)
      (fun t => (g (qx, (t, qz))).2.1)
      (fun t => (g (qx, (t, qz))).2.2)
      hFx hdy.1 hdy.2.1 hdy.2.2
    have hline :
        (fun t => f qx t qz) =ᶠ[nhds qy]
          (fun t => F (g (qx, (t, qz))).1
            (g (qx, (t, qz))).2.1
            (g (qx, (t, qz))).2.2) :=
      hyPath.continuousAt.eventually heq
    unfold partial2 pullYFormula
    rw [hline.deriv_eq, hchain.deriv]
    simp only
    rw [hgu]
    simp [forwardJacobianEquiv]
    ring
  · have hchain := hasDerivAt_comp_three F
      (fun t => (g (qx, (qy, t))).1)
      (fun t => (g (qx, (qy, t))).2.1)
      (fun t => (g (qx, (qy, t))).2.2)
      hFx hdz.1 hdz.2.1 hdz.2.2
    have hline :
        (fun t => f qx qy t) =ᶠ[nhds qz]
          (fun t => F (g (qx, (qy, t))).1
            (g (qx, (qy, t))).2.1
            (g (qx, (qy, t))).2.2) :=
      hzPath.continuousAt.eventually heq
    unfold partial3 pullZFormula
    rw [hline.deriv_eq, hchain.deriv]
    simp only
    rw [hgu]
    simp [forwardJacobianEquiv]
    ring

private lemma inverseMap_local_data
    (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    ContDiffAt ℝ (2 : WithTop ℕ∞) (inverseMap xi eta zeta)
        (forwardMap (ξ, (η, ζ))) ∧
      (∀ᶠ q : Point3 in nhds (forwardMap (ξ, (η, ζ))),
        forwardMap (inverseMap xi eta zeta q) = q) := by
  have hforward : ContDiffAt ℝ (2 : WithTop ℕ∞)
      forwardMap (ξ, (η, ζ)) := by
    unfold forwardMap forwardX forwardY forwardZ
    fun_prop
  have hderiv :=
    forwardMap_hasFDerivAt ξ η ζ hInv.1 hInv.2.1 hInv.2.2.1
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by decide
  let localInv : Point3 → Point3 := hforward.localInverse hderiv hn
  have hlocal :
      ContDiffAt ℝ (2 : WithTop ℕ∞) localInv
        (forwardMap (ξ, (η, ζ))) := by
    dsimp [localInv]
    exact hforward.to_localInverse hderiv hn
  have hstrict := hforward.hasStrictFDerivAt' hderiv hn
  have hinv :
      ∀ᶠ p : Point3 in nhds (ξ, (η, ζ)),
        inverseMap xi eta zeta (forwardMap p) = p := by
    filter_upwards [hInv.2.2.2.2.2.2] with p hp
    apply Prod.ext
    · exact hp.1
    · apply Prod.ext
      · exact hp.2.1
      · exact hp.2.2
  have heq :
      inverseMap xi eta zeta =ᶠ[nhds (forwardMap (ξ, (η, ζ)))]
        localInv := by
    simpa [localInv, ContDiffAt.localInverse] using
      hstrict.localInverse_unique hinv
  constructor
  · exact hlocal.congr_of_eventuallyEq heq
  · filter_upwards [heq, hstrict.eventually_right_inverse] with q hq hr
    rw [hq]
    exact hr

private lemma eventually_first_partials
    (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ)
    (hPullback : IsLocalPullback f F xi eta zeta ξ η ζ) :
    ∀ᶠ q : Point3 in nhds (forwardMap (ξ, (η, ζ))),
      partial1 f q.1 q.2.1 q.2.2 =
          pullXFormula F (inverseMap xi eta zeta q).1
            (inverseMap xi eta zeta q).2.1
            (inverseMap xi eta zeta q).2.2 ∧
        partial2 f q.1 q.2.1 q.2.2 =
          pullYFormula F (inverseMap xi eta zeta q).1
            (inverseMap xi eta zeta q).2.1
            (inverseMap xi eta zeta q).2.2 ∧
        partial3 f q.1 q.2.1 q.2.2 =
          pullZFormula F (inverseMap xi eta zeta q).1
            (inverseMap xi eta zeta q).2.1
            (inverseMap xi eta zeta q).2.2 := by
  let q₀ := forwardMap (ξ, (η, ζ))
  let g := inverseMap xi eta zeta
  have hdata := inverseMap_local_data xi eta zeta ξ η ζ hInv
  have hsmooth :
      ∀ᶠ q : Point3 in nhds q₀,
        ContDiffAt ℝ (2 : WithTop ℕ∞) g q := by
    simpa [q₀, g] using hdata.1.eventually (by decide)
  have hright :
      ∀ᶠ q : Point3 in nhds q₀,
        ∀ᶠ r : Point3 in nhds q, forwardMap (g r) = r := by
    simpa [q₀, g] using eventually_eventually_nhds.2 hdata.2
  have hpull :
      ∀ᶠ q : Point3 in nhds q₀,
        (fun p : Point3 => f p.1 p.2.1 p.2.2) =ᶠ[nhds q]
          (fun p => F (g p).1 (g p).2.1 (g p).2.2) := by
    simpa [q₀, g] using eventually_eventually_nhds.2 hPullback.1
  have hinv0 := hInv.2.2.2.2.2.2.self_of_nhds
  have hbase : g q₀ = (ξ, (η, ζ)) := by
    apply Prod.ext
    · exact hinv0.1
    · apply Prod.ext
      · exact hinv0.2.1
      · exact hinv0.2.2
  have hcont : ContinuousAt g q₀ := by
    simpa [q₀, g] using hdata.1.continuousAt
  have hξ_ne : ∀ᶠ q : Point3 in nhds q₀, (g q).1 ≠ 0 := by
    have ht : Tendsto (fun q => (g q).1) (nhds q₀) (nhds ξ) := by
      simpa only [ContinuousAt, hbase] using hcont.fst
    exact ht.eventually (eventually_ne_nhds hInv.1)
  have hη_ne : ∀ᶠ q : Point3 in nhds q₀, (g q).2.1 ≠ 0 := by
    have ht : Tendsto (fun q => (g q).2.1) (nhds q₀) (nhds η) := by
      simpa only [ContinuousAt, hbase] using hcont.snd.fst
    exact ht.eventually (eventually_ne_nhds hInv.2.1)
  have hζ_ne : ∀ᶠ q : Point3 in nhds q₀, (g q).2.2 ≠ 0 := by
    have ht : Tendsto (fun q => (g q).2.2) (nhds q₀) (nhds ζ) := by
      simpa only [ContinuousAt, hbase] using hcont.snd.snd
    exact ht.eventually (eventually_ne_nhds hInv.2.2.1)
  filter_upwards [hsmooth, hright, hpull, hξ_ne, hη_ne, hζ_ne]
    with q hqSmooth hqRight hqPull hqξ hqη hqζ
  let u := g q
  have hforward :=
    forwardMap_hasFDerivAt u.1 u.2.1 u.2.2 hqξ hqη hqζ
  have hgDeriv :
      HasFDerivAt g
        (((forwardJacobianEquiv u.1 u.2.1 u.2.2 hqξ hqη hqζ).toContinuousLinearEquiv
          ).symm : Point3 →L[ℝ] Point3) q :=
    hforward.of_local_left_inverse hqSmooth.continuousAt hqRight
  exact first_partials_of_local_pullback f F g q u hqξ hqη hqζ rfl
    hPullback.2.1.differentiableAt hgDeriv hqPull

private lemma hasDerivAt_partial1_along
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ) (t da db dc : ℝ)
    (hF : C2 F) (ha : HasDerivAt a da t)
    (hb : HasDerivAt b db t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => partial1 F (a s) (b s) (c s))
      (da * partial11 F (a t) (b t) (c t) +
        db * partial12 F (a t) (b t) (c t) +
        dc * partial31 F (a t) (b t) (c t)) t := by
  have h := hasDerivAt_comp_three (partial1 F) a b c
    hF.2.1.differentiableAt ha hb hc
  have hm := (mixed_partials_of_C2 F (a t) (b t) (c t) hF).2.1
  convert h using 1
  change
    da * partial1 (partial1 F) (a t) (b t) (c t) +
          db * partial2 (partial1 F) (a t) (b t) (c t) +
          dc * partial31 F (a t) (b t) (c t) =
      da * partial1 (partial1 F) (a t) (b t) (c t) +
          db * partial2 (partial1 F) (a t) (b t) (c t) +
          dc * partial3 (partial1 F) (a t) (b t) (c t)
  rw [hm]

private lemma hasDerivAt_partial2_along
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ) (t da db dc : ℝ)
    (hF : C2 F) (ha : HasDerivAt a da t)
    (hb : HasDerivAt b db t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => partial2 F (a s) (b s) (c s))
      (da * partial12 F (a t) (b t) (c t) +
        db * partial22 F (a t) (b t) (c t) +
        dc * partial23 F (a t) (b t) (c t)) t := by
  have h := hasDerivAt_comp_three (partial2 F) a b c
    hF.2.2.1.differentiableAt ha hb hc
  have hm := (mixed_partials_of_C2 F (a t) (b t) (c t) hF).1
  convert h using 1
  change
    da * partial12 F (a t) (b t) (c t) +
          db * partial2 (partial2 F) (a t) (b t) (c t) +
          dc * partial3 (partial2 F) (a t) (b t) (c t) =
      da * partial1 (partial2 F) (a t) (b t) (c t) +
          db * partial2 (partial2 F) (a t) (b t) (c t) +
          dc * partial3 (partial2 F) (a t) (b t) (c t)
  rw [hm]

private lemma hasDerivAt_partial3_along
    (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ) (t da db dc : ℝ)
    (hF : C2 F) (ha : HasDerivAt a da t)
    (hb : HasDerivAt b db t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => partial3 F (a s) (b s) (c s))
      (da * partial31 F (a t) (b t) (c t) +
        db * partial23 F (a t) (b t) (c t) +
        dc * partial33 F (a t) (b t) (c t)) t := by
  have h := hasDerivAt_comp_three (partial3 F) a b c
    hF.2.2.2.differentiableAt ha hb hc
  have hm := (mixed_partials_of_C2 F (a t) (b t) (c t) hF).2.2
  convert h using 1
  change
    da * partial1 (partial3 F) (a t) (b t) (c t) +
          db * partial23 F (a t) (b t) (c t) +
          dc * partial3 (partial3 F) (a t) (b t) (c t) =
      da * partial1 (partial3 F) (a t) (b t) (c t) +
          db * partial2 (partial3 F) (a t) (b t) (c t) +
          dc * partial3 (partial3 F) (a t) (b t) (c t)
  rw [hm]

theorem gap1 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial1 xi (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      -ξ / (2 * η * ζ) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      ((1, (0, 0)) : Point3) x₀ :=
    (hasDerivAt_id x₀).prodMk
      ((hasDerivAt_const x₀ y₀).prodMk (hasDerivAt_const x₀ z₀))
  have hc := H.comp x₀ hp.hasFDerivAt
  have hout :=
    (hasFDerivAt_fst.comp x₀ hc).hasDerivAt
  unfold partial1
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]

theorem gap2 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial1 eta (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      1 / (2 * ζ) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      ((1, (0, 0)) : Point3) x₀ :=
    (hasDerivAt_id x₀).prodMk
      ((hasDerivAt_const x₀ y₀).prodMk (hasDerivAt_const x₀ z₀))
  have hc := H.comp x₀ hp.hasFDerivAt
  have hsnd := hasFDerivAt_snd.comp x₀ hc
  have hout := (hasFDerivAt_fst.comp x₀ hsnd).hasDerivAt
  unfold partial1
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]

theorem gap3 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial1 zeta (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      1 / (2 * η) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      ((1, (0, 0)) : Point3) x₀ :=
    (hasDerivAt_id x₀).prodMk
      ((hasDerivAt_const x₀ y₀).prodMk (hasDerivAt_const x₀ z₀))
  have hc := H.comp x₀ hp.hasFDerivAt
  have hsnd := hasFDerivAt_snd.comp x₀ hc
  have hout := (hasFDerivAt_snd.comp x₀ hsnd).hasDerivAt
  unfold partial1
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]

theorem gap4 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial2 xi (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      1 / (2 * ζ) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((x₀, (t, z₀)) : Point3))
      ((0, (1, 0)) : Point3) y₀ :=
    (hasDerivAt_const y₀ x₀).prodMk
      ((hasDerivAt_id y₀).prodMk (hasDerivAt_const y₀ z₀))
  have hc := H.comp y₀ hp.hasFDerivAt
  have hout := (hasFDerivAt_fst.comp y₀ hc).hasDerivAt
  unfold partial2
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]

theorem gap5 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial2 eta (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      -η / (2 * ξ * ζ) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((x₀, (t, z₀)) : Point3))
      ((0, (1, 0)) : Point3) y₀ :=
    (hasDerivAt_const y₀ x₀).prodMk
      ((hasDerivAt_id y₀).prodMk (hasDerivAt_const y₀ z₀))
  have hc := H.comp y₀ hp.hasFDerivAt
  have hsnd := hasFDerivAt_snd.comp y₀ hc
  have hout := (hasFDerivAt_fst.comp y₀ hsnd).hasDerivAt
  unfold partial2
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]
  ring

theorem gap6 (xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ) :
    partial2 zeta (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      1 / (2 * ξ) := by
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((x₀, (t, z₀)) : Point3))
      ((0, (1, 0)) : Point3) y₀ :=
    (hasDerivAt_const y₀ x₀).prodMk
      ((hasDerivAt_id y₀).prodMk (hasDerivAt_const y₀ z₀))
  have hc := H.comp y₀ hp.hasFDerivAt
  have hsnd := hasFDerivAt_snd.comp y₀ hc
  have hout := (hasFDerivAt_snd.comp y₀ hsnd).hasDerivAt
  unfold partial2
  convert hout.deriv using 1
  simp [x₀, y₀, z₀, inverseMap, forwardMap, forwardJacobianEquiv]

theorem gap7 (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ)
    (hPullback : IsLocalPullback f F xi eta zeta ξ η ζ) :
    partial1 f (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      -ξ / (2 * η * ζ) * partial1 F ξ η ζ +
        1 / (2 * ζ) * partial2 F ξ η ζ +
        1 / (2 * η) * partial3 F ξ η ζ := by
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  have hp : HasDerivAt (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      ((1, (0, 0)) : Point3) x₀ :=
    (hasDerivAt_id x₀).prodMk
      ((hasDerivAt_const x₀ y₀).prodMk (hasDerivAt_const x₀ z₀))
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  have hc := H.comp x₀ hp.hasFDerivAt
  have hxi :=
    (hasFDerivAt_fst.comp x₀ hc).hasDerivAt
  have hsnd := hasFDerivAt_snd.comp x₀ hc
  have heta :=
    (hasFDerivAt_fst.comp x₀ hsnd).hasDerivAt
  have hzeta :=
    (hasFDerivAt_snd.comp x₀ hsnd).hasDerivAt
  have hxi' : HasDerivAt (fun t => xi t y₀ z₀)
      (-ξ / (2 * η * ζ)) x₀ := by
    convert hxi using 1
    simp [inverseMap, forwardMap, forwardJacobianEquiv]
  have heta' : HasDerivAt (fun t => eta t y₀ z₀)
      (1 / (2 * ζ)) x₀ := by
    convert heta using 1
    simp [inverseMap, forwardMap, forwardJacobianEquiv]
  have hzeta' : HasDerivAt (fun t => zeta t y₀ z₀)
      (1 / (2 * η)) x₀ := by
    convert hzeta using 1
    simp [inverseMap, forwardMap, forwardJacobianEquiv]
  have hinv0 := hInv.2.2.2.2.2.2.self_of_nhds
  have hchain :=
    hasDerivAt_comp_three F
      (fun t => xi t y₀ z₀) (fun t => eta t y₀ z₀)
      (fun t => zeta t y₀ z₀)
      (hPullback.2.1.differentiableAt) hxi' heta' hzeta'
  have hpath : Tendsto (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      (nhds x₀) (nhds (x₀, (y₀, z₀))) := by
    exact continuousAt_id.prodMk
      (continuousAt_const.prodMk continuousAt_const)
  have heq :
      (fun t : ℝ => f t y₀ z₀) =ᶠ[nhds x₀]
        (fun t => F (xi t y₀ z₀) (eta t y₀ z₀) (zeta t y₀ z₀)) :=
    hpath.eventually hPullback.1
  unfold partial1
  rw [heq.deriv_eq, hchain.deriv]
  simp only [x₀, y₀, z₀] at hinv0 ⊢
  rw [hinv0.1, hinv0.2.1, hinv0.2.2]
  rfl

theorem gap8 (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ)
    (hPullback : IsLocalPullback f F xi eta zeta ξ η ζ) :
    partial12 f (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      mixedXYFormula F ξ η ζ := by
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  let g := inverseMap xi eta zeta
  let a := fun t : ℝ => (g (x₀, (t, z₀))).1
  let b := fun t : ℝ => (g (x₀, (t, z₀))).2.1
  let c := fun t : ℝ => (g (x₀, (t, z₀))).2.2
  have hp : HasDerivAt (fun t : ℝ => ((x₀, (t, z₀)) : Point3))
      ((0, (1, 0)) : Point3) y₀ :=
    (hasDerivAt_const y₀ x₀).prodMk
      ((hasDerivAt_id y₀).prodMk (hasDerivAt_const y₀ z₀))
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  have hcAll := H.comp y₀ hp.hasFDerivAt
  have ha : HasDerivAt a (1 / (2 * ζ)) y₀ := by
    have h := (hasFDerivAt_fst.comp y₀ hcAll).hasDerivAt
    convert h using 1
    simp [a, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hsnd := hasFDerivAt_snd.comp y₀ hcAll
  have hb : HasDerivAt b (-η / (2 * ξ * ζ)) y₀ := by
    have h := (hasFDerivAt_fst.comp y₀ hsnd).hasDerivAt
    convert h using 1
    simp [b, g, inverseMap, forwardMap, forwardJacobianEquiv]
    ring
  have hc : HasDerivAt c (1 / (2 * ξ)) y₀ := by
    have h := (hasFDerivAt_snd.comp y₀ hsnd).hasDerivAt
    convert h using 1
    simp [c, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hinv0 := hInv.2.2.2.2.2.2.self_of_nhds
  have ha0 : a y₀ = ξ := by
    simpa [a, g, x₀, y₀, z₀] using hinv0.1
  have hb0 : b y₀ = η := by
    simpa [b, g, x₀, y₀, z₀] using hinv0.2.1
  have hc0 : c y₀ = ζ := by
    simpa [c, g, x₀, y₀, z₀] using hinv0.2.2
  have hp1 := hasDerivAt_partial1_along F a b c y₀
    (1 / (2 * ζ)) (-η / (2 * ξ * ζ)) (1 / (2 * ξ))
    hPullback.2 ha hb hc
  have hp2 := hasDerivAt_partial2_along F a b c y₀
    (1 / (2 * ζ)) (-η / (2 * ξ * ζ)) (1 / (2 * ξ))
    hPullback.2 ha hb hc
  have hp3 := hasDerivAt_partial3_along F a b c y₀
    (1 / (2 * ζ)) (-η / (2 * ξ * ζ)) (1 / (2 * ξ))
    hPullback.2 ha hb hc
  have htwo : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 y₀ :=
    hasDerivAt_const y₀ 2
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y₀ :=
    hasDerivAt_const y₀ 1
  have hA := ha.neg.div ((htwo.mul hb).mul hc) (by
    simp only [Pi.mul_apply]
    rw [hb0, hc0]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hInv.2.1) hInv.2.2.1)
  have hB := hone.div (htwo.mul hc) (by
    simp only [Pi.mul_apply]
    rw [hc0]
    exact mul_ne_zero (by norm_num) hInv.2.2.1)
  have hC := hone.div (htwo.mul hb) (by
    simp only [Pi.mul_apply]
    rw [hb0]
    exact mul_ne_zero (by norm_num) hInv.2.1)
  have htotal := ((hA.mul hp1).add (hB.mul hp2)).add (hC.mul hp3)
  change HasDerivAt
    (fun t => pullXFormula F (a t) (b t) (c t)) _ y₀ at htotal
  have hevent := hp.continuousAt.eventually
    (eventually_first_partials f F xi eta zeta ξ η ζ hInv hPullback)
  have heq :
      (fun t => partial1 f x₀ t z₀) =ᶠ[nhds y₀]
        (fun t => pullXFormula F (a t) (b t) (c t)) := by
    filter_upwards [hevent] with t ht
    exact ht.1
  unfold partial12
  rw [heq.deriv_eq, htotal.deriv]
  simp [ha0, hb0, hc0]
  unfold mixedXYFormula
  field_simp [hInv.1, hInv.2.1, hInv.2.2.1]
  ring

theorem gap9 (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ)
    (hPullback : IsLocalPullback f F xi eta zeta ξ η ζ) :
    partial23 f (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      mixedYZFormula F ξ η ζ := by
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  let g := inverseMap xi eta zeta
  let a := fun t : ℝ => (g (x₀, (y₀, t))).1
  let b := fun t : ℝ => (g (x₀, (y₀, t))).2.1
  let c := fun t : ℝ => (g (x₀, (y₀, t))).2.2
  have hp : HasDerivAt (fun t : ℝ => ((x₀, (y₀, t)) : Point3))
      ((0, (0, 1)) : Point3) z₀ :=
    (hasDerivAt_const z₀ x₀).prodMk
      ((hasDerivAt_const z₀ y₀).prodMk (hasDerivAt_id z₀))
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  have hcAll := H.comp z₀ hp.hasFDerivAt
  have ha : HasDerivAt a (1 / (2 * η)) z₀ := by
    have h := (hasFDerivAt_fst.comp z₀ hcAll).hasDerivAt
    convert h using 1
    simp [a, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hsnd := hasFDerivAt_snd.comp z₀ hcAll
  have hb : HasDerivAt b (1 / (2 * ξ)) z₀ := by
    have h := (hasFDerivAt_fst.comp z₀ hsnd).hasDerivAt
    convert h using 1
    simp [b, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hc : HasDerivAt c (-ζ / (2 * ξ * η)) z₀ := by
    have h := (hasFDerivAt_snd.comp z₀ hsnd).hasDerivAt
    convert h using 1
    simp [c, g, inverseMap, forwardMap, forwardJacobianEquiv]
    ring
  have hinv0 := hInv.2.2.2.2.2.2.self_of_nhds
  have ha0 : a z₀ = ξ := by
    simpa [a, g, x₀, y₀, z₀] using hinv0.1
  have hb0 : b z₀ = η := by
    simpa [b, g, x₀, y₀, z₀] using hinv0.2.1
  have hc0 : c z₀ = ζ := by
    simpa [c, g, x₀, y₀, z₀] using hinv0.2.2
  have hp1 := hasDerivAt_partial1_along F a b c z₀
    (1 / (2 * η)) (1 / (2 * ξ)) (-ζ / (2 * ξ * η))
    hPullback.2 ha hb hc
  have hp2 := hasDerivAt_partial2_along F a b c z₀
    (1 / (2 * η)) (1 / (2 * ξ)) (-ζ / (2 * ξ * η))
    hPullback.2 ha hb hc
  have hp3 := hasDerivAt_partial3_along F a b c z₀
    (1 / (2 * η)) (1 / (2 * ξ)) (-ζ / (2 * ξ * η))
    hPullback.2 ha hb hc
  have htwo : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 z₀ :=
    hasDerivAt_const z₀ 2
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 z₀ :=
    hasDerivAt_const z₀ 1
  have hA := hone.div (htwo.mul hc) (by
    simp only [Pi.mul_apply]
    rw [hc0]
    exact mul_ne_zero (by norm_num) hInv.2.2.1)
  have hB := hb.div ((htwo.mul ha).mul hc) (by
    simp only [Pi.mul_apply]
    rw [ha0, hc0]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hInv.1) hInv.2.2.1)
  have hC := hone.div (htwo.mul ha) (by
    simp only [Pi.mul_apply]
    rw [ha0]
    exact mul_ne_zero (by norm_num) hInv.1)
  have htotal := ((hA.mul hp1).sub (hB.mul hp2)).add (hC.mul hp3)
  change HasDerivAt
    (fun t => pullYFormula F (a t) (b t) (c t)) _ z₀ at htotal
  have hevent := hp.continuousAt.eventually
    (eventually_first_partials f F xi eta zeta ξ η ζ hInv hPullback)
  have heq :
      (fun t => partial2 f x₀ y₀ t) =ᶠ[nhds z₀]
        (fun t => pullYFormula F (a t) (b t) (c t)) := by
    filter_upwards [hevent] with t ht
    exact ht.2.1
  unfold partial23
  rw [heq.deriv_eq, htotal.deriv]
  simp [ha0, hb0, hc0]
  unfold mixedYZFormula
  field_simp [hInv.1, hInv.2.1, hInv.2.2.1]
  ring

theorem gap10 (f F xi eta zeta : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hInv : IsLocalInverse xi eta zeta ξ η ζ)
    (hPullback : IsLocalPullback f F xi eta zeta ξ η ζ) :
    partial31 f (forwardX ξ η ζ) (forwardY ξ η ζ) (forwardZ ξ η ζ) =
      mixedZXFormula F ξ η ζ := by
  let x₀ := forwardX ξ η ζ
  let y₀ := forwardY ξ η ζ
  let z₀ := forwardZ ξ η ζ
  let g := inverseMap xi eta zeta
  let a := fun t : ℝ => (g (t, (y₀, z₀))).1
  let b := fun t : ℝ => (g (t, (y₀, z₀))).2.1
  let c := fun t : ℝ => (g (t, (y₀, z₀))).2.2
  have hp : HasDerivAt (fun t : ℝ => ((t, (y₀, z₀)) : Point3))
      ((1, (0, 0)) : Point3) x₀ :=
    (hasDerivAt_id x₀).prodMk
      ((hasDerivAt_const x₀ y₀).prodMk (hasDerivAt_const x₀ z₀))
  have H := inverseMap_hasFDerivAt xi eta zeta ξ η ζ hInv
  have hcAll := H.comp x₀ hp.hasFDerivAt
  have ha : HasDerivAt a (-ξ / (2 * η * ζ)) x₀ := by
    have h := (hasFDerivAt_fst.comp x₀ hcAll).hasDerivAt
    convert h using 1
    simp [a, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hsnd := hasFDerivAt_snd.comp x₀ hcAll
  have hb : HasDerivAt b (1 / (2 * ζ)) x₀ := by
    have h := (hasFDerivAt_fst.comp x₀ hsnd).hasDerivAt
    convert h using 1
    simp [b, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hc : HasDerivAt c (1 / (2 * η)) x₀ := by
    have h := (hasFDerivAt_snd.comp x₀ hsnd).hasDerivAt
    convert h using 1
    simp [c, g, inverseMap, forwardMap, forwardJacobianEquiv]
  have hinv0 := hInv.2.2.2.2.2.2.self_of_nhds
  have ha0 : a x₀ = ξ := by
    simpa [a, g, x₀, y₀, z₀] using hinv0.1
  have hb0 : b x₀ = η := by
    simpa [b, g, x₀, y₀, z₀] using hinv0.2.1
  have hc0 : c x₀ = ζ := by
    simpa [c, g, x₀, y₀, z₀] using hinv0.2.2
  have hp1 := hasDerivAt_partial1_along F a b c x₀
    (-ξ / (2 * η * ζ)) (1 / (2 * ζ)) (1 / (2 * η))
    hPullback.2 ha hb hc
  have hp2 := hasDerivAt_partial2_along F a b c x₀
    (-ξ / (2 * η * ζ)) (1 / (2 * ζ)) (1 / (2 * η))
    hPullback.2 ha hb hc
  have hp3 := hasDerivAt_partial3_along F a b c x₀
    (-ξ / (2 * η * ζ)) (1 / (2 * ζ)) (1 / (2 * η))
    hPullback.2 ha hb hc
  have htwo : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x₀ :=
    hasDerivAt_const x₀ 2
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x₀ :=
    hasDerivAt_const x₀ 1
  have hA := hone.div (htwo.mul hb) (by
    simp only [Pi.mul_apply]
    rw [hb0]
    exact mul_ne_zero (by norm_num) hInv.2.1)
  have hB := hone.div (htwo.mul ha) (by
    simp only [Pi.mul_apply]
    rw [ha0]
    exact mul_ne_zero (by norm_num) hInv.1)
  have hC := hc.div ((htwo.mul ha).mul hb) (by
    simp only [Pi.mul_apply]
    rw [ha0, hb0]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hInv.1) hInv.2.1)
  have htotal := ((hA.mul hp1).add (hB.mul hp2)).sub (hC.mul hp3)
  change HasDerivAt
    (fun t => pullZFormula F (a t) (b t) (c t)) _ x₀ at htotal
  have hevent := hp.continuousAt.eventually
    (eventually_first_partials f F xi eta zeta ξ η ζ hInv hPullback)
  have heq :
      (fun t => partial3 f t y₀ z₀) =ᶠ[nhds x₀]
        (fun t => pullZFormula F (a t) (b t) (c t)) := by
    filter_upwards [hevent] with t ht
    exact ht.2.2
  unfold partial31
  rw [heq.deriv_eq, htotal.deriv]
  simp [ha0, hb0, hc0]
  unfold mixedZXFormula
  field_simp [hInv.1, hInv.2.1, hInv.2.2.1]
  ring

theorem gap11 (f F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hξ : ξ ≠ 0) (hη : η ≠ 0) (hζ : ζ ≠ 0)
    (hPDE : physicalPDE f (forwardX ξ η ζ) (forwardY ξ η ζ)
      (forwardZ ξ η ζ) = 0)
    (hXY : partial12 f (forwardX ξ η ζ) (forwardY ξ η ζ)
      (forwardZ ξ η ζ) = mixedXYFormula F ξ η ζ)
    (hYZ : partial23 f (forwardX ξ η ζ) (forwardY ξ η ζ)
      (forwardZ ξ η ζ) = mixedYZFormula F ξ η ζ)
    (hZX : partial31 f (forwardX ξ η ζ) (forwardY ξ η ζ)
      (forwardZ ξ η ζ) = mixedZXFormula F ξ η ζ) :
    transformedBalance F ξ η ζ := by
  unfold physicalPDE at hPDE
  rw [hXY, hYZ, hZX] at hPDE
  unfold forwardX forwardY forwardZ mixedXYFormula mixedYZFormula
    mixedZXFormula at hPDE
  unfold transformedBalance
  field_simp [hξ, hη, hζ] at hPDE ⊢
  ring_nf at hPDE ⊢
  linarith

theorem gap12 (F : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hF : C2 F)
    (hBalance : transformedBalance F ξ η ζ) :
    ξ * deriv (fun t => t * partial1 F t η ζ) ξ +
        η * deriv (fun t => t * partial2 F ξ t ζ) η +
        ζ * deriv (fun t => t * partial3 F ξ η t) ζ =
      2 * (ξ * η * partial12 F ξ η ζ + η * ζ * partial23 F ξ η ζ +
        ζ * ξ * partial31 F ξ η ζ) := by
  have hxPath : HasDerivAt
      (fun t : ℝ => ((t, (η, ζ)) : Point3))
      ((1, (0, 0)) : Point3) ξ :=
    (hasDerivAt_id ξ).prodMk
      ((hasDerivAt_const ξ η).prodMk (hasDerivAt_const ξ ζ))
  have hyPath : HasDerivAt
      (fun t : ℝ => ((ξ, (t, ζ)) : Point3))
      ((0, (1, 0)) : Point3) η :=
    (hasDerivAt_const η ξ).prodMk
      ((hasDerivAt_id η).prodMk (hasDerivAt_const η ζ))
  have hzPath : HasDerivAt
      (fun t : ℝ => ((ξ, (η, t)) : Point3))
      ((0, (0, 1)) : Point3) ζ :=
    (hasDerivAt_const ζ ξ).prodMk
      ((hasDerivAt_const ζ η).prodMk (hasDerivAt_id ζ))
  have hd1 : DifferentiableAt ℝ (fun t => partial1 F t η ζ) ξ := by
    simpa [Function.comp_def] using
      hF.2.1.differentiableAt.comp ξ hxPath.differentiableAt
  have hd2 : DifferentiableAt ℝ (fun t => partial2 F ξ t ζ) η := by
    simpa [Function.comp_def] using
      hF.2.2.1.differentiableAt.comp η hyPath.differentiableAt
  have hd3 : DifferentiableAt ℝ (fun t => partial3 F ξ η t) ζ := by
    simpa [Function.comp_def] using
      hF.2.2.2.differentiableAt.comp ζ hzPath.differentiableAt
  have h1 : HasDerivAt (fun t => partial1 F t η ζ)
      (partial11 F ξ η ζ) ξ := by
    unfold partial11
    exact hd1.hasDerivAt
  have h2 : HasDerivAt (fun t => partial2 F ξ t ζ)
      (partial22 F ξ η ζ) η := by
    unfold partial22
    exact hd2.hasDerivAt
  have h3 : HasDerivAt (fun t => partial3 F ξ η t)
      (partial33 F ξ η ζ) ζ := by
    unfold partial33
    exact hd3.hasDerivAt
  have hp1 := (hasDerivAt_id ξ).mul h1
  have hp2 := (hasDerivAt_id η).mul h2
  have hp3 := (hasDerivAt_id ζ).mul h3
  change HasDerivAt (fun t => t * partial1 F t η ζ) _ ξ at hp1
  change HasDerivAt (fun t => t * partial2 F ξ t ζ) _ η at hp2
  change HasDerivAt (fun t => t * partial3 F ξ η t) _ ζ at hp3
  rw [hp1.deriv, hp2.deriv, hp3.deriv]
  simp only [id_eq]
  unfold transformedBalance at hBalance
  ring_nf at hBalance ⊢
  linarith

end

end ProofGap.Exercise3508
