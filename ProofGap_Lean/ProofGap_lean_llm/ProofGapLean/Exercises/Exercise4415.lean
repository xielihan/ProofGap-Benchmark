import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4415

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def segment (B A : Vec3) (t : ℝ) : Vec3 :=
  ((1 - t) * B.1 + t * A.1,
    (1 - t) * B.2.1 + t * A.2.1,
    (1 - t) * B.2.2 + t * A.2.2)

def displacement (B A : Vec3) : Vec3 :=
  (A.1 - B.1, A.2.1 - B.2.1, A.2.2 - B.2.2)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def distance (A B : Vec3) : ℝ :=
  norm3 (displacement B A)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def path (u : Vec3 → ℝ) (B A : Vec3) (t : ℝ) : ℝ :=
  u (segment B A t)

def DifferentiableThroughout (u : Vec3 → ℝ) (Ω : Set Vec3) : Prop :=
  ∀ p ∈ Ω, DifferentiableAt ℝ u p

def GradientBound (u : Vec3 → ℝ) (Ω : Set Vec3) (M : ℝ) : Prop :=
  ∀ p ∈ Ω, norm3 (gradient u p) ≤ M

def IsMLipschitzOn (u : Vec3 → ℝ) (Ω : Set Vec3) (M : ℝ) : Prop :=
  ∀ A ∈ Ω, ∀ B ∈ Ω, |u A - u B| ≤ M * distance A B

private def CurveDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (f' : E) (x : ℝ) : Prop :=
  HasDerivAt f f' x

private theorem prod_curve_hasDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => (f y, g y)) (f', g') x := by
  unfold HasDerivAt at hf hg ⊢
  convert hf.prodMk hg using 1 <;> ext y <;> simp

private theorem CurveDeriv.hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {x : ℝ} (h : CurveDeriv f f' x) :
    HasDerivAt f f' x :=
  h

private theorem CurveDeriv.prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {x : ℝ}
    (hf : CurveDeriv f f' x) (hg : CurveDeriv g g' x) :
    CurveDeriv (fun y => (f y, g y)) (f', g') x :=
  prod_curve_hasDerivAt hf.hasDerivAt hg.hasDerivAt

private theorem CurveDeriv.differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {x : ℝ} (h : CurveDeriv f f' x) :
    DifferentiableAt ℝ f x :=
  h.hasDerivAt.differentiableAt

private theorem affineCoord_hasDerivAt (b a t : ℝ) :
    CurveDeriv (fun s : ℝ => (1 - s) * b + s * a) (a - b) t := by
  unfold CurveDeriv
  convert
    ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const b).add
      ((hasDerivAt_id t).mul_const a)) using 1 <;> ring

private theorem comp_curve_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {c : ℝ → E} {u' : E →L[ℝ] ℝ} {c' : E} {t : ℝ}
    (hu : HasFDerivAt u u' (c t)) (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s => u (c s)) (u' c') t := by
  have hcomp : HasFDerivAt (u ∘ c)
      (u'.comp (ContinuousLinearMap.toSpanSingleton ℝ c')) t :=
    hu.comp t hc.hasFDerivAt
  simpa [Function.comp_def] using hcomp.hasDerivAt

theorem gap1 (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω) :
    segment B A '' Set.Icc (0 : ℝ) 1 ⊆ Ω := by
  rintro _ ⟨t, ht, rfl⟩
  have hm : (1 - t) • B + t • A ∈ Ω :=
    hConvex hB hA (sub_nonneg.mpr ht.2) ht.1 (by ring)
  simpa [segment] using hm

theorem gap2 (u : Vec3 → ℝ) (A B : Vec3) :
    path u B A 0 = u B := by
  simp [path, segment]

theorem gap3 (u : Vec3 → ℝ) (A B : Vec3) :
    path u B A 1 = u A := by
  simp [path, segment]

theorem gap4 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω) :
    DifferentiableOn ℝ (path u B A) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hp : segment B A t ∈ Ω :=
    gap1 Ω A B hConvex hA hB ⟨t, ht, rfl⟩
  have hs : DifferentiableAt ℝ (segment B A) t :=
    ((affineCoord_hasDerivAt B.1 A.1 t).prod
      ((affineCoord_hasDerivAt B.2.1 A.2.1 t).prod
        (affineCoord_hasDerivAt B.2.2 A.2.2 t))).differentiableAt
  have hc : DifferentiableAt ℝ (u ∘ segment B A) t :=
    (hu (segment B A t) hp).comp t hs
  simpa [path, Function.comp_def] using hc.differentiableWithinAt

theorem gap5 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3) (t : ℝ)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (path u B A)
      (dot (gradient u (segment B A t)) (displacement B A)) t := by
  let p : Vec3 := segment B A t
  have hp : p ∈ Ω := by
    apply gap1 Ω A B hConvex hA hB
    exact ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
  have hU : HasFDerivAt u (fderiv ℝ u p) p := (hu p hp).hasFDerivAt
  have hs : HasDerivAt (segment B A) (displacement B A) t := by
    simpa [segment, displacement] using
      ((affineCoord_hasDerivAt B.1 A.1 t).prod
        ((affineCoord_hasDerivAt B.2.1 A.2.1 t).prod
          (affineCoord_hasDerivAt B.2.2 A.2.2 t))).hasDerivAt
  have hUt : HasFDerivAt u (fderiv ℝ u p) (segment B A t) := by
    simpa [p] using hU
  have hpath : HasDerivAt (path u B A)
      (fderiv ℝ u p (displacement B A)) t := by
    simpa [path, Function.comp_def] using comp_curve_hasDerivAt hUt hs
  have hxCurve : HasDerivAt (fun x : ℝ => (x, p.2.1, p.2.2))
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) p.1 := by
    exact prod_curve_hasDerivAt (hasDerivAt_id p.1)
      (prod_curve_hasDerivAt
        (hasDerivAt_const p.1 p.2.1)
        (hasDerivAt_const p.1 p.2.2))
  have hyCurve : HasDerivAt (fun y : ℝ => (p.1, y, p.2.2))
      ((0 : ℝ), (1 : ℝ), (0 : ℝ)) p.2.1 := by
    exact prod_curve_hasDerivAt (hasDerivAt_const p.2.1 p.1)
      (prod_curve_hasDerivAt
        (hasDerivAt_id p.2.1)
        (hasDerivAt_const p.2.1 p.2.2))
  have hzCurve : HasDerivAt (fun z : ℝ => (p.1, p.2.1, z))
      ((0 : ℝ), (0 : ℝ), (1 : ℝ)) p.2.2 := by
    exact prod_curve_hasDerivAt (hasDerivAt_const p.2.2 p.1)
      (prod_curve_hasDerivAt
        (hasDerivAt_const p.2.2 p.2.1)
        (hasDerivAt_id p.2.2))
  have hUx : HasFDerivAt u (fderiv ℝ u p) (p.1, p.2.1, p.2.2) := by
    simpa using hU
  have hxD : HasDerivAt (fun x : ℝ => u (x, p.2.1, p.2.2))
      (fderiv ℝ u p (1, 0, 0)) p.1 := by
    simpa [Function.comp_def] using comp_curve_hasDerivAt hUx hxCurve
  have hyD : HasDerivAt (fun y : ℝ => u (p.1, y, p.2.2))
      (fderiv ℝ u p (0, 1, 0)) p.2.1 := by
    simpa [Function.comp_def] using comp_curve_hasDerivAt hUx hyCurve
  have hzD : HasDerivAt (fun z : ℝ => u (p.1, p.2.1, z))
      (fderiv ℝ u p (0, 0, 1)) p.2.2 := by
    simpa [Function.comp_def] using comp_curve_hasDerivAt hUx hzCurve
  have hx : partialX u p = fderiv ℝ u p (1, 0, 0) := by
    simpa [partialX] using hxD.deriv
  have hy : partialY u p = fderiv ℝ u p (0, 1, 0) := by
    simpa [partialY] using hyD.deriv
  have hz : partialZ u p = fderiv ℝ u p (0, 0, 1) := by
    simpa [partialZ] using hzD.deriv
  have hdecomp : displacement B A =
      (A.1 - B.1) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
        (A.2.1 - B.2.1) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        (A.2.2 - B.2.2) • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [displacement]
  have hfdot : fderiv ℝ u p (displacement B A) =
      dot (gradient u p) (displacement B A) := by
    calc
      fderiv ℝ u p (displacement B A) =
          (A.1 - B.1) * fderiv ℝ u p (1, 0, 0) +
            (A.2.1 - B.2.1) * fderiv ℝ u p (0, 1, 0) +
            (A.2.2 - B.2.2) * fderiv ℝ u p (0, 0, 1) := by
              rw [hdecomp, map_add, map_add, map_smul, map_smul, map_smul]
              rfl
      _ = dot (gradient u p) (displacement B A) := by
            simp [dot, gradient, displacement, hx, hy, hz]
            ring
  rw [hfdot] at hpath
  simpa [p] using hpath

theorem gap6 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      u A - u B = deriv (path u B A) ξ := by
  have hd := gap4 u Ω A B hConvex hA hB hu
  have hdi : DifferentiableOn ℝ (path u B A) (Set.Ioo (0 : ℝ) 1) :=
    hd.mono Set.Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, hder⟩ :=
    exists_deriv_eq_slope (f := path u B A) (a := (0 : ℝ)) (b := 1)
      (by norm_num) hd.continuousOn hdi
  refine ⟨ξ, hξ, ?_⟩
  simpa [path, segment] using hder.symm

theorem gap7 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      u A - u B =
        dot (gradient u (segment B A ξ)) (displacement B A) := by
  obtain ⟨ξ, hξ, heq⟩ := gap6 u Ω A B hConvex hA hB hu
  refine ⟨ξ, hξ, heq.trans ?_⟩
  exact (gap5 u Ω A B ξ hConvex hA hB hu hξ).deriv

theorem gap8 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      |u A - u B| =
        |dot (gradient u (segment B A ξ)) (displacement B A)| := by
  obtain ⟨ξ, hξ, heq⟩ := gap7 u Ω A B hConvex hA hB hu
  exact ⟨ξ, hξ, congrArg abs heq⟩

theorem gap9 (u : Vec3 → ℝ) (Ω : Set Vec3) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      |u A - u B| ≤
        norm3 (gradient u (segment B A ξ)) * distance A B := by
  obtain ⟨ξ, hξ, heq⟩ := gap8 u Ω A B hConvex hA hB hu
  refine ⟨ξ, hξ, ?_⟩
  rw [heq]
  let g : Vec3 := gradient u (segment B A ξ)
  let d : Vec3 := displacement B A
  change |dot g d| ≤ norm3 g * norm3 d
  let s : ℝ := g.1 ^ 2 + g.2.1 ^ 2 + g.2.2 ^ 2
  let q : ℝ := d.1 ^ 2 + d.2.1 ^ 2 + d.2.2 ^ 2
  let w : ℝ := g.1 * d.1 + g.2.1 * d.2.1 + g.2.2 * d.2.2
  change |w| ≤ Real.sqrt s * Real.sqrt q
  have hs : 0 ≤ s := by
    dsimp [s]
    nlinarith [sq_nonneg g.1, sq_nonneg g.2.1, sq_nonneg g.2.2]
  have hq : 0 ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg d.1, sq_nonneg d.2.1, sq_nonneg d.2.2]
  have hcs : w ^ 2 ≤ s * q := by
    dsimp [w, s, q]
    nlinarith
      [sq_nonneg (g.1 * d.2.1 - g.2.1 * d.1),
       sq_nonneg (g.1 * d.2.2 - g.2.2 * d.1),
       sq_nonneg (g.2.1 * d.2.2 - g.2.2 * d.2.1)]
  have hrs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hrq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hrprod : (Real.sqrt s * Real.sqrt q) ^ 2 = s * q := by
    rw [mul_pow, hrs, hrq]
  have habs : |w| ^ 2 = w ^ 2 := sq_abs w
  have hleft : 0 ≤ |w| := abs_nonneg w
  have hright : 0 ≤ Real.sqrt s * Real.sqrt q :=
    mul_nonneg (Real.sqrt_nonneg s) (Real.sqrt_nonneg q)
  nlinarith

theorem gap10 (u : Vec3 → ℝ) (Ω : Set Vec3) (M : ℝ) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω)
    (hBound : GradientBound u Ω M) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      norm3 (gradient u (segment B A ξ)) * distance A B ≤
        M * distance A B := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  have hp : segment B A (1 / 2 : ℝ) ∈ Ω := by
    apply gap1 Ω A B hConvex hA hB
    exact ⟨(1 / 2 : ℝ), by norm_num, rfl⟩
  have hb := hBound (segment B A (1 / 2 : ℝ)) hp
  exact mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)

theorem gap11 (u : Vec3 → ℝ) (Ω : Set Vec3) (M : ℝ) (A B : Vec3)
    (hConvex : Convex ℝ Ω) (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hu : DifferentiableThroughout u Ω)
    (hBound : GradientBound u Ω M) :
    |u A - u B| ≤ M * distance A B := by
  obtain ⟨ξ, hξ, hdot⟩ := gap9 u Ω A B hConvex hA hB hu
  have hp : segment B A ξ ∈ Ω := by
    apply gap1 Ω A B hConvex hA hB
    exact ⟨ξ, ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩, rfl⟩
  calc
    |u A - u B| ≤
        norm3 (gradient u (segment B A ξ)) * distance A B := hdot
    _ ≤ M * distance A B :=
      mul_le_mul_of_nonneg_right (hBound (segment B A ξ) hp)
        (Real.sqrt_nonneg _)

theorem gap12 (u : Vec3 → ℝ) (Ω : Set Vec3) (M : ℝ)
    (hConvex : Convex ℝ Ω)
    (hu : DifferentiableThroughout u Ω)
    (hBound : GradientBound u Ω M) :
    IsMLipschitzOn u Ω M := by
  intro A hA B hB
  exact gap11 u Ω M A B hConvex hA hB hu hBound

end

end ProofGap.Exercise4415
