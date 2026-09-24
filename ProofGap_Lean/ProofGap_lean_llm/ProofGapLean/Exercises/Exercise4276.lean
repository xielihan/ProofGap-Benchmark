import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4276

noncomputable section

open scoped Interval
open Filter

abbrev Point := ℝ × ℝ

def radius (p : Point) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def fundamental (p : Point) : ℝ :=
  Real.log (1 / radius p)

def conjugate (p : Point) : ℝ :=
  Real.arctan (p.1 / p.2)

def partialX (f : Point → ℝ) (p : Point) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

def partialY (f : Point → ℝ) (p : Point) : ℝ :=
  deriv (fun y => f (p.1, y)) p.2

def iterX : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f => f
  | n + 1, f => partialX (iterX n f)

def iterY : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f => f
  | m + 1, f => partialY (iterY m f)

def mixedDerivative (f : Point → ℝ) (n m : ℕ) : Point → ℝ :=
  iterY m (iterX n f)

def derivedField (n m : ℕ) (p : Point) : Point :=
  (mixedDerivative fundamental (n + 2) (m - 1) p,
    -mixedDerivative fundamental (n - 1) (m + 2) p)

def derivedPotential (n m : ℕ) : Point → ℝ :=
  mixedDerivative conjugate n m

def laplacian (p : Point) : ℝ :=
  partialX (partialX fundamental) p + partialY (partialY fundamental) p

def curlDefect (n m : ℕ) (p : Point) : ℝ :=
  partialY (fun q => (derivedField n m q).1) p -
    partialX (fun q => (derivedField n m q).2) p

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (f : Point → ℝ) (p v : Point) : ℝ :=
  partialX f p * v.1 + partialY f p * v.2

def HasCoordinateGradientAt
    (f : Point → ℝ) (V : Point) (p : Point) : Prop :=
  HasDerivAt (fun x => f (x, p.2)) V.1 p.1 ∧
    HasDerivAt (fun y => f (p.1, y)) V.2 p.2

def IsUpperSolution (z : Point → ℝ) (n m : ℕ) : Prop :=
  ∀ p, 0 < p.2 → HasCoordinateGradientAt z (derivedField n m p) p

def IsLowerSolution (z : Point → ℝ) (n m : ℕ) : Prop :=
  ∀ p, p.2 < 0 → HasCoordinateGradientAt z (derivedField n m p) p

def constructedUpper (n m : ℕ) (p : Point) : ℝ :=
  (∫ s in (0 : ℝ)..p.1, (derivedField n m (s, p.2)).1) +
    ∫ t in (1 : ℝ)..p.2, (derivedField n m (0, t)).2

def constructedLower (n m : ℕ) (p : Point) : ℝ :=
  (∫ s in (0 : ℝ)..p.1, (derivedField n m (s, p.2)).1) +
    ∫ t in (-1 : ℝ)..p.2, (derivedField n m (0, t)).2

def splitPotential (n m : ℕ) (C₁ C₂ : ℝ) (p : Point) : ℝ :=
  if 0 < p.2 then derivedPotential n m p + C₁
  else derivedPotential n m p + C₂

private theorem point_sq_pos (p : Point) (hp : p ≠ (0, 0)) :
    0 < p.1 ^ 2 + p.2 ^ 2 := by
  have hnonneg :
      0 ≤ p.1 ^ 2 + p.2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_contra hn
  have hz : p.1 ^ 2 + p.2 ^ 2 = 0 := by linarith
  have hx : p.1 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hy : p.2 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  exact hp (Prod.ext hx hy)

private theorem radius_sq (p : Point)
    (hp : 0 ≤ p.1 ^ 2 + p.2 ^ 2) :
    radius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt hp

private theorem fundamental_hasDerivAt_x
    (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun x => fundamental (x, p.2))
      (-p.1 / radius p ^ 2) p.1 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hinner :
      HasDerivAt
        (fun x : ℝ => x ^ 2 + p.2 ^ 2)
        (2 * p.1) p.1 := by
    convert
      ((hasDerivAt_id p.1).pow 2).add_const
        (p.2 ^ 2) using 1 <;>
      simp [mul_comm]
  have hroot := hinner.sqrt hD0
  have hinv := hroot.inv hr0
  have hlog := hinv.log (inv_ne_zero hr0)
  convert hlog using 1
  · simp [fundamental, radius, one_div]
  · rw [radius_sq p (le_of_lt hD)]
    simp only [Pi.inv_apply]
    field_simp [hD0, hr0]
    · rw [Real.sq_sqrt (le_of_lt hD)]

private theorem fundamental_hasDerivAt_y
    (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun y => fundamental (p.1, y))
      (-p.2 / radius p ^ 2) p.2 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hinner :
      HasDerivAt
        (fun y : ℝ => p.1 ^ 2 + y ^ 2)
        (2 * p.2) p.2 := by
    convert
      (hasDerivAt_const p.2 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2).pow 2) using 1 <;>
      simp [mul_comm]
  have hroot := hinner.sqrt hD0
  have hinv := hroot.inv hr0
  have hlog := hinv.log (inv_ne_zero hr0)
  convert hlog using 1
  · simp [fundamental, radius, one_div]
  · rw [radius_sq p (le_of_lt hD)]
    simp only [Pi.inv_apply]
    field_simp [hD0, hr0]
    · rw [Real.sq_sqrt (le_of_lt hD)]

private theorem partialX_fundamental_eventually
    (p : Point) (hp : p ≠ (0, 0)) :
    (fun x => partialX fundamental (x, p.2)) =ᶠ[nhds p.1]
      (fun x => -x / (x ^ 2 + p.2 ^ 2)) := by
  by_cases hy : p.2 = 0
  · have hx : p.1 ≠ 0 := by
      intro hx
      exact hp (Prod.ext hx hy)
    have hnear : ∀ᶠ x in nhds p.1, x ≠ 0 :=
      continuousAt_id.eventually_ne hx
    filter_upwards [hnear] with x hx
    have hq : (x, p.2) ≠ (0, 0) := by
      intro h
      exact hx (congrArg Prod.fst h)
    unfold partialX
    rw [(fundamental_hasDerivAt_x (x, p.2) hq).deriv]
    have hD :
        0 ≤ x ^ 2 + p.2 ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [radius_sq (x, p.2) hD]
  · filter_upwards [] with x
    have hq : (x, p.2) ≠ (0, 0) := by
      intro h
      exact hy (congrArg Prod.snd h)
    unfold partialX
    rw [(fundamental_hasDerivAt_x (x, p.2) hq).deriv]
    have hD :
        0 ≤ x ^ 2 + p.2 ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [radius_sq (x, p.2) hD]

private theorem partialY_fundamental_eventually
    (p : Point) (hp : p ≠ (0, 0)) :
    (fun y => partialY fundamental (p.1, y)) =ᶠ[nhds p.2]
      (fun y => -y / (p.1 ^ 2 + y ^ 2)) := by
  by_cases hx : p.1 = 0
  · have hy : p.2 ≠ 0 := by
      intro hy
      exact hp (Prod.ext hx hy)
    have hnear : ∀ᶠ y in nhds p.2, y ≠ 0 :=
      continuousAt_id.eventually_ne hy
    filter_upwards [hnear] with y hy
    have hq : (p.1, y) ≠ (0, 0) := by
      intro h
      exact hy (congrArg Prod.snd h)
    unfold partialY
    rw [(fundamental_hasDerivAt_y (p.1, y) hq).deriv]
    have hD :
        0 ≤ p.1 ^ 2 + y ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [radius_sq (p.1, y) hD]
  · filter_upwards [] with y
    have hq : (p.1, y) ≠ (0, 0) := by
      intro h
      exact hx (congrArg Prod.fst h)
    unfold partialY
    rw [(fundamental_hasDerivAt_y (p.1, y) hq).deriv]
    have hD :
        0 ≤ p.1 ^ 2 + y ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [radius_sq (p.1, y) hD]

private theorem fundamental_second_x
    (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun x => partialX fundamental (x, p.2))
      (-(radius p ^ 2 - 2 * p.1 ^ 2) / radius p ^ 4) p.1 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hnum :
      HasDerivAt (fun x : ℝ => -x) (-1) p.1 := by
    simpa using (hasDerivAt_id p.1).neg
  have hden :
      HasDerivAt (fun x : ℝ => x ^ 2 + p.2 ^ 2)
        (2 * p.1) p.1 := by
    convert
      ((hasDerivAt_id p.1).pow 2).add_const
        (p.2 ^ 2) using 1 <;>
      simp [mul_comm]
  have hrat := hnum.div hden hD0
  have htarget :
      HasDerivAt
        (fun x => -x / (x ^ 2 + p.2 ^ 2))
        (-(radius p ^ 2 - 2 * p.1 ^ 2) / radius p ^ 4)
        p.1 := by
    convert hrat using 1
    have hrsq := radius_sq p (le_of_lt hD)
    rw [show radius p ^ 4 = (radius p ^ 2) ^ 2 by ring,
      hrsq]
    field_simp [hD0]
    ring
  exact htarget.congr_of_eventuallyEq
    (partialX_fundamental_eventually p hp)

private theorem fundamental_second_y
    (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun y => partialY fundamental (p.1, y))
      (-(radius p ^ 2 - 2 * p.2 ^ 2) / radius p ^ 4) p.2 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hnum :
      HasDerivAt (fun y : ℝ => -y) (-1) p.2 := by
    simpa using (hasDerivAt_id p.2).neg
  have hden :
      HasDerivAt (fun y : ℝ => p.1 ^ 2 + y ^ 2)
        (2 * p.2) p.2 := by
    convert
      (hasDerivAt_const p.2 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2).pow 2) using 1 <;>
      simp [mul_comm]
  have hrat := hnum.div hden hD0
  have htarget :
      HasDerivAt
        (fun y => -y / (p.1 ^ 2 + y ^ 2))
        (-(radius p ^ 2 - 2 * p.2 ^ 2) / radius p ^ 4)
        p.2 := by
    convert hrat using 1
    have hrsq := radius_sq p (le_of_lt hD)
    rw [show radius p ^ 4 = (radius p ^ 2) ^ 2 by ring,
      hrsq]
    field_simp [hD0]
    ring
  exact htarget.congr_of_eventuallyEq
    (partialY_fundamental_eventually p hp)

private theorem laplacian_zero
    (p : Point) (hp : p ≠ (0, 0)) :
    laplacian p = 0 := by
  unfold laplacian
  have hx :
      partialX (partialX fundamental) p =
        -(radius p ^ 2 - 2 * p.1 ^ 2) /
          radius p ^ 4 :=
    (fundamental_second_x p hp).deriv
  have hy :
      partialY (partialY fundamental) p =
        -(radius p ^ 2 - 2 * p.2 ^ 2) /
          radius p ^ 4 :=
    (fundamental_second_y p hp).deriv
  rw [hx, hy]
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hrsq := radius_sq p (le_of_lt hD)
  field_simp [hr0]
  nlinarith

private theorem partialX_eventually_zero
    {f : Point → ℝ} {p : Point}
    (h : f =ᶠ[nhds p] fun _ => (0 : ℝ)) :
    partialX f =ᶠ[nhds p] fun _ => (0 : ℝ) := by
  rcases mem_nhds_iff.1 h with ⟨s, hs, hopen, hp⟩
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hmap :
      Tendsto (fun x : ℝ => (x, q.2))
        (nhds q.1) (nhds q) := by
    simpa using
      (continuousAt_id.prodMk continuousAt_const).tendsto
  have hslice :
      (fun x => f (x, q.2)) =ᶠ[nhds q.1]
        fun _ => (0 : ℝ) := by
    filter_upwards [hmap (hopen.mem_nhds hq)] with x hx
    exact hs hx
  unfold partialX
  rw [hslice.deriv_eq]
  simp

private theorem partialY_eventually_zero
    {f : Point → ℝ} {p : Point}
    (h : f =ᶠ[nhds p] fun _ => (0 : ℝ)) :
    partialY f =ᶠ[nhds p] fun _ => (0 : ℝ) := by
  rcases mem_nhds_iff.1 h with ⟨s, hs, hopen, hp⟩
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hmap :
      Tendsto (fun y : ℝ => (q.1, y))
        (nhds q.2) (nhds q) := by
    simpa using
      (continuousAt_const.prodMk continuousAt_id).tendsto
  have hslice :
      (fun y => f (q.1, y)) =ᶠ[nhds q.2]
        fun _ => (0 : ℝ) := by
    filter_upwards [hmap (hopen.mem_nhds hq)] with y hy
    exact hs hy
  unfold partialY
  rw [hslice.deriv_eq]
  simp

private theorem iterX_eventually_zero
    (n : ℕ) {f : Point → ℝ} {p : Point}
    (h : f =ᶠ[nhds p] fun _ => (0 : ℝ)) :
    iterX n f =ᶠ[nhds p] fun _ => (0 : ℝ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [iterX]
      exact partialX_eventually_zero ih

private theorem iterY_eventually_zero
    (m : ℕ) {f : Point → ℝ} {p : Point}
    (h : f =ᶠ[nhds p] fun _ => (0 : ℝ)) :
    iterY m f =ᶠ[nhds p] fun _ => (0 : ℝ) := by
  induction m with
  | zero => exact h
  | succ m ih =>
      rw [iterY]
      exact partialY_eventually_zero ih

private theorem mixed_laplacian_zero
    (n m : ℕ) (p : Point) (hp : p ≠ (0, 0)) :
    mixedDerivative laplacian n m p = 0 := by
  have hnear :
      ∀ᶠ q : Point in nhds p, q ≠ (0, 0) :=
    continuousAt_id.eventually_ne hp
  have hlap :
      laplacian =ᶠ[nhds p] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    exact laplacian_zero q hq
  unfold mixedDerivative
  have hx := iterX_eventually_zero n hlap
  exact (iterY_eventually_zero m hx).self_of_nhds

/- The next group of private lemmas gives a coordinate-free model of
the iterated coordinate derivatives.  It is also the convenient place
to use symmetry of the second Fréchet derivative. -/

private def directionalDerivative
    (d : Point) (F : Point → ℝ) (p : Point) : ℝ :=
  fderiv ℝ F p d

private def iterDirectional (d : Point) :
    ℕ → (Point → ℝ) → Point → ℝ
  | 0, F => F
  | k + 1, F =>
      iterDirectional d k (directionalDerivative d F)

private def orderedMixed
    (n m : ℕ) (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv n
    (fun s => iteratedDeriv m (fun t => u s t) y) x

private theorem directionalDerivative_contDiffAt
    (d : Point) (k : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (k + 1) F p) :
    ContDiffAt ℝ k (directionalDerivative d F) p := by
  unfold directionalDerivative
  exact
    (hF.fderiv_right (m := k) (by simp)).clm_apply
      contDiffAt_const

private theorem hasDerivAt_slice_x
    (F : Point → ℝ) (x y : ℝ)
    (hF : ContDiffAt ℝ 1 F (x, y)) :
    HasDerivAt (fun s => F (s, y))
      (directionalDerivative (1, 0) F (x, y)) x := by
  have hcurve :
      HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hF' :
      HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    hF.differentiableAt_one.hasFDerivAt
  simpa [Function.comp_def, directionalDerivative] using
    hF'.comp_hasDerivAt x hcurve

private theorem hasDerivAt_slice_y
    (F : Point → ℝ) (x y : ℝ)
    (hF : ContDiffAt ℝ 1 F (x, y)) :
    HasDerivAt (fun t => F (x, t))
      (directionalDerivative (0, 1) F (x, y)) y := by
  have hcurve :
      HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hF' :
      HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    hF.differentiableAt_one.hasFDerivAt
  simpa [Function.comp_def, directionalDerivative] using
    hF'.comp_hasDerivAt y hcurve

private theorem eventuallyEq_directionalDerivative
    (d : Point) {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    directionalDerivative d F =ᶠ[nhds p]
      directionalDerivative d G := by
  have hd : fderiv ℝ F =ᶠ[nhds p] fderiv ℝ G := h.fderiv
  filter_upwards [hd] with q hq
  unfold directionalDerivative
  rw [hq]

private theorem eventuallyEq_iterDirectional
    (d : Point) (k : ℕ) {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    iterDirectional d k F =ᶠ[nhds p]
      iterDirectional d k G := by
  induction k generalizing F G with
  | zero => exact h
  | succ k ih =>
      exact ih (eventuallyEq_directionalDerivative d h)

private theorem iterDirectional_contDiffAt
    (d : Point) (n k : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + k) F p) :
    ContDiffAt ℝ k (iterDirectional d n F) p := by
  induction n generalizing F with
  | zero => simpa [iterDirectional] using hF
  | succ n ih =>
      rw [iterDirectional]
      apply ih
      apply directionalDerivative_contDiffAt
      simpa [Nat.succ_eq_add_one, add_assoc, add_comm,
        add_left_comm] using hF

private theorem directionalDerivative_comm_at
    (a b : Point) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ 2 F p) :
    directionalDerivative a (directionalDerivative b F) p =
      directionalDerivative b (directionalDerivative a F) p := by
  have hfderiv_diff :
      DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have happly (d e : Point) :
      directionalDerivative e (directionalDerivative d F) p =
        fderiv ℝ (fderiv ℝ F) p e d := by
    have hmap :=
      congrArg
        (fun L : (Point →L[ℝ] ℝ) => L e)
        (fderiv_clm_apply
          (c := fderiv ℝ F)
          (u := fun _ : Point => d)
          hfderiv_diff (differentiableAt_const d))
    simpa [directionalDerivative] using hmap
  rw [happly, happly]
  exact (hF.isSymmSndFDerivAt (by norm_num)) a b

private theorem eventuallyEq_directional_comm
    (a b : Point) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ 2 F p) :
    directionalDerivative a (directionalDerivative b F) =ᶠ[nhds p]
      directionalDerivative b (directionalDerivative a F) := by
  filter_upwards [
    hF.eventually
      (by norm_num :
        (2 : WithTop ENat) ≠
          (↑(⊤ : ENat) : WithTop ENat))] with q hq
  exact directionalDerivative_comm_at a b F q hq

private theorem eventuallyEq_directional_iterDirectional_comm
    (a b : Point) (n : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + 1) F p) :
    directionalDerivative a (iterDirectional b n F) =ᶠ[nhds p]
      iterDirectional b n (directionalDerivative a F) := by
  induction n generalizing F with
  | zero =>
      exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
      have hb :
          ContDiffAt ℝ (n + 1) (directionalDerivative b F) p := by
        apply directionalDerivative_contDiffAt
        simpa [Nat.succ_eq_add_one, add_assoc] using hF
      have hFtwo : ContDiffAt ℝ 2 F p :=
        hF.of_le (by
          simpa only [Nat.succ_eq_add_one,
            ← one_add_one_eq_two, add_assoc] using
            (self_le_add_left
              (2 : WithTop ENat) (n : WithTop ENat)))
      have h₁ := ih (directionalDerivative b F) hb
      have hcomm :=
        eventuallyEq_directional_comm a b F p hFtwo
      have h₂ := eventuallyEq_iterDirectional b n hcomm
      exact h₁.trans h₂

private theorem contDiffAt_eventually_nat
    (k : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ k F p) :
    ∀ᶠ q in nhds p, ContDiffAt ℝ k F q :=
  hF.eventually (by
    simp :
      (k : WithTop ENat) ≠
        (↑(⊤ : ENat) : WithTop ENat))

private theorem iterDirectional_x_eq_at
    (n : ℕ) (F : Point → ℝ) (x y : ℝ)
    (hF : ContDiffAt ℝ n F (x, y)) :
    iterDirectional (1, 0) n F (x, y) =
      iteratedDeriv n (fun s => F (s, y)) x := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
      have hdir :
          ContDiffAt ℝ n (directionalDerivative (1, 0) F)
            (x, y) := by
        apply directionalDerivative_contDiffAt
        simpa [Nat.succ_eq_add_one] using hF
      have hnear :
          ∀ᶠ s in nhds x, ContDiffAt ℝ 1 F (s, y) := by
        have hall :=
          contDiffAt_eventually_nat (Nat.succ n) F (x, y) hF
        have hmap :
            Tendsto (fun s : ℝ => (s, y))
              (nhds x) (nhds (x, y)) :=
          (continuousAt_id.prodMk continuousAt_const).tendsto
        filter_upwards [hmap hall] with s hs
        change ContDiffAt ℝ (Nat.succ n) F (s, y) at hs
        exact hs.of_le (by simp)
      have hslice :
          (fun s : ℝ =>
              directionalDerivative (1, 0) F (s, y)) =ᶠ[nhds x]
            deriv (fun s : ℝ => F (s, y)) := by
        filter_upwards [hnear] with s hs
        exact (hasDerivAt_slice_x F s y hs).deriv.symm
      calc
        iterDirectional (1, 0) (Nat.succ n) F (x, y) =
            iterDirectional (1, 0) n
              (directionalDerivative (1, 0) F) (x, y) := rfl
        _ = iteratedDeriv n
              (fun s => directionalDerivative (1, 0) F (s, y)) x :=
            ih (directionalDerivative (1, 0) F) hdir
        _ = iteratedDeriv n
              (deriv (fun s : ℝ => F (s, y))) x :=
            Filter.EventuallyEq.iteratedDeriv_eq n hslice
        _ = iteratedDeriv (Nat.succ n)
              (fun s : ℝ => F (s, y)) x := by
            rw [Nat.succ_eq_add_one, iteratedDeriv_succ']

private theorem iterDirectional_y_eq_at
    (n : ℕ) (F : Point → ℝ) (x y : ℝ)
    (hF : ContDiffAt ℝ n F (x, y)) :
    iterDirectional (0, 1) n F (x, y) =
      iteratedDeriv n (fun t => F (x, t)) y := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
      have hdir :
          ContDiffAt ℝ n (directionalDerivative (0, 1) F)
            (x, y) := by
        apply directionalDerivative_contDiffAt
        simpa [Nat.succ_eq_add_one] using hF
      have hnear :
          ∀ᶠ t in nhds y, ContDiffAt ℝ 1 F (x, t) := by
        have hall :=
          contDiffAt_eventually_nat (Nat.succ n) F (x, y) hF
        have hmap :
            Tendsto (fun t : ℝ => (x, t))
              (nhds y) (nhds (x, y)) :=
          (continuousAt_const.prodMk continuousAt_id).tendsto
        filter_upwards [hmap hall] with t ht
        change ContDiffAt ℝ (Nat.succ n) F (x, t) at ht
        exact ht.of_le (by simp)
      have hslice :
          (fun t : ℝ =>
              directionalDerivative (0, 1) F (x, t)) =ᶠ[nhds y]
            deriv (fun t : ℝ => F (x, t)) := by
        filter_upwards [hnear] with t ht
        exact (hasDerivAt_slice_y F x t ht).deriv.symm
      calc
        iterDirectional (0, 1) (Nat.succ n) F (x, y) =
            iterDirectional (0, 1) n
              (directionalDerivative (0, 1) F) (x, y) := rfl
        _ = iteratedDeriv n
              (fun t => directionalDerivative (0, 1) F (x, t)) y :=
            ih (directionalDerivative (0, 1) F) hdir
        _ = iteratedDeriv n
              (deriv (fun t : ℝ => F (x, t))) y :=
            Filter.EventuallyEq.iteratedDeriv_eq n hslice
        _ = iteratedDeriv (Nat.succ n)
              (fun t : ℝ => F (x, t)) y := by
            rw [Nat.succ_eq_add_one, iteratedDeriv_succ']

private theorem orderedMixed_eq_iterDirectional_at
    (n m : ℕ) (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiffAt ℝ (n + m)
      (Function.uncurry u) (x, y)) :
    orderedMixed n m u x y =
      iterDirectional (1, 0) n
        (iterDirectional (0, 1) m
          (Function.uncurry u)) (x, y) := by
  let U : Point → ℝ := Function.uncurry u
  let Y : Point → ℝ := iterDirectional (0, 1) m U
  have hu_mn : ContDiffAt ℝ (m + n) U (x, y) := by
    simpa [U, add_comm] using hu
  have hY : ContDiffAt ℝ n Y (x, y) :=
    iterDirectional_contDiffAt
      (0, 1) m n U (x, y) hu_mn
  have hnear :
      ∀ᶠ s in nhds x, ContDiffAt ℝ (n + m) U (s, y) := by
    have hall :=
      contDiffAt_eventually_nat (n + m) U (x, y)
        (by simpa [U] using hu)
    have hmap :
        Tendsto (fun s : ℝ => (s, y))
          (nhds x) (nhds (x, y)) :=
      (continuousAt_id.prodMk continuousAt_const).tendsto
    filter_upwards [hmap hall] with s hs
    exact hs
  have hinner :
      (fun s : ℝ => iteratedDeriv m (fun t => u s t) y) =ᶠ[nhds x]
        (fun s => Y (s, y)) := by
    filter_upwards [hnear] with s hs
    have hm_le :
        (m : WithTop ENat) ≤ (n + m : ℕ) := by
      simpa only [Nat.cast_add] using
        (self_le_add_left
          (m : WithTop ENat) (n : WithTop ENat))
    have heq :=
      iterDirectional_y_eq_at m U s y (hs.of_le hm_le)
    simpa [U, Y] using heq.symm
  unfold orderedMixed
  calc
    iteratedDeriv n
        (fun s => iteratedDeriv m (fun t => u s t) y) x =
      iteratedDeriv n (fun s => Y (s, y)) x :=
        Filter.EventuallyEq.iteratedDeriv_eq n hinner
    _ = iterDirectional (1, 0) n Y (x, y) :=
      (iterDirectional_x_eq_at n Y x y hY).symm
    _ = iterDirectional (1, 0) n
        (iterDirectional (0, 1) m
          (Function.uncurry u)) (x, y) := by rfl

private theorem iterX_eq_iteratedDeriv
    (n : ℕ) (F : Point → ℝ) (x y : ℝ) :
    iterX n F (x, y) =
      iteratedDeriv n (fun s => F (s, y)) x := by
  induction n generalizing F x y with
  | zero => rfl
  | succ n ih =>
      change deriv (fun s => iterX n F (s, y)) x =
        iteratedDeriv (n + 1) (fun s => F (s, y)) x
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih F s y

private theorem iterY_eq_iteratedDeriv
    (m : ℕ) (F : Point → ℝ) (x y : ℝ) :
    iterY m F (x, y) =
      iteratedDeriv m (fun t => F (x, t)) y := by
  induction m generalizing F x y with
  | zero => rfl
  | succ m ih =>
      change deriv (fun t => iterY m F (x, t)) y =
        iteratedDeriv (m + 1) (fun t => F (x, t)) y
      rw [iteratedDeriv_succ]
      congr 1
      funext t
      exact ih F x t

private theorem eventuallyEq_partialX
    {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    partialX F =ᶠ[nhds p] partialX G := by
  rcases mem_nhds_iff.1 h with ⟨s, hs, hopen, hp⟩
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hmap :
      Tendsto (fun x : ℝ => (x, q.2))
        (nhds q.1) (nhds q) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).tendsto
  have hslice :
      (fun x => F (x, q.2)) =ᶠ[nhds q.1]
        (fun x => G (x, q.2)) := by
    filter_upwards [hmap (hopen.mem_nhds hq)] with x hx
    exact hs hx
  unfold partialX
  exact hslice.deriv_eq

private theorem eventuallyEq_partialY
    {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    partialY F =ᶠ[nhds p] partialY G := by
  rcases mem_nhds_iff.1 h with ⟨s, hs, hopen, hp⟩
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hmap :
      Tendsto (fun y : ℝ => (q.1, y))
        (nhds q.2) (nhds q) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).tendsto
  have hslice :
      (fun y => F (q.1, y)) =ᶠ[nhds q.2]
        (fun y => G (q.1, y)) := by
    filter_upwards [hmap (hopen.mem_nhds hq)] with y hy
    exact hs hy
  unfold partialY
  exact hslice.deriv_eq

private theorem eventuallyEq_iterX
    (n : ℕ) {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    iterX n F =ᶠ[nhds p] iterX n G := by
  induction n generalizing F G with
  | zero => exact h
  | succ n ih => exact eventuallyEq_partialX (ih h)

private theorem eventuallyEq_iterY
    (m : ℕ) {F G : Point → ℝ} {p : Point}
    (h : F =ᶠ[nhds p] G) :
    iterY m F =ᶠ[nhds p] iterY m G := by
  induction m generalizing F G with
  | zero => exact h
  | succ m ih => exact eventuallyEq_partialY (ih h)

private theorem iterX_eq_iterDirectional_at
    (n : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ n F p) :
    iterX n F p = iterDirectional (1, 0) n F p := by
  calc
    iterX n F p =
        iteratedDeriv n (fun s => F (s, p.2)) p.1 :=
      iterX_eq_iteratedDeriv n F p.1 p.2
    _ = iterDirectional (1, 0) n F p :=
      (iterDirectional_x_eq_at n F p.1 p.2 hF).symm

private theorem iterY_eq_iterDirectional_at
    (m : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ m F p) :
    iterY m F p = iterDirectional (0, 1) m F p := by
  calc
    iterY m F p =
        iteratedDeriv m (fun t => F (p.1, t)) p.2 :=
      iterY_eq_iteratedDeriv m F p.1 p.2
    _ = iterDirectional (0, 1) m F p :=
      (iterDirectional_y_eq_at m F p.1 p.2 hF).symm

private theorem eventuallyEq_iterDirectional_blocks_comm
    (a b : Point) (m n : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + m) F p) :
    iterDirectional a m (iterDirectional b n F) =ᶠ[nhds p]
      iterDirectional b n (iterDirectional a m F) := by
  induction m generalizing F with
  | zero =>
      exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ m ih =>
      have hcomm :
          directionalDerivative a (iterDirectional b n F) =ᶠ[nhds p]
            iterDirectional b n (directionalDerivative a F) := by
        apply eventuallyEq_directional_iterDirectional_comm
        apply hF.of_le
        simpa only [Nat.cast_add, Nat.cast_one,
          add_comm, add_left_comm, add_assoc] using
          (add_le_add_left
            (show (1 : WithTop ENat) ≤
                (m : WithTop ENat) + 1 by simp)
            (n : WithTop ENat))
      have hlift :=
        eventuallyEq_iterDirectional a m hcomm
      have hDF :
          ContDiffAt ℝ (n + m) (directionalDerivative a F) p := by
        apply directionalDerivative_contDiffAt
        simpa [Nat.succ_eq_add_one, add_assoc] using hF
      exact hlift.trans (ih (directionalDerivative a F) hDF)

private theorem mixedDerivative_eq_orderedMixed_at
    (n m : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + m) F p) :
    mixedDerivative F n m p =
      orderedMixed n m (fun x y => F (x, y)) p.1 p.2 := by
  have hn : ContDiffAt ℝ n F p := by
    apply hF.of_le
    simpa only [Nat.cast_add] using
      (le_add_right (le_refl (n : WithTop ENat)) :
        (n : WithTop ENat) ≤
          (n : WithTop ENat) + (m : WithTop ENat))
  have hnear :
      ∀ᶠ q in nhds p, ContDiffAt ℝ n F q :=
    contDiffAt_eventually_nat n F p hn
  have hx :
      iterX n F =ᶠ[nhds p]
        iterDirectional (1, 0) n F := by
    filter_upwards [hnear] with q hq
    exact iterX_eq_iterDirectional_at n F q hq
  have hdirX :
      ContDiffAt ℝ m (iterDirectional (1, 0) n F) p := by
    exact iterDirectional_contDiffAt
      (1, 0) n m F p hF
  have hcurrent :
      mixedDerivative F n m p =
        iterDirectional (0, 1) m
          (iterDirectional (1, 0) n F) p := by
    unfold mixedDerivative
    calc
      iterY m (iterX n F) p =
          iterY m (iterDirectional (1, 0) n F) p :=
        (eventuallyEq_iterY m hx).self_of_nhds
      _ = iterDirectional (0, 1) m
          (iterDirectional (1, 0) n F) p :=
        iterY_eq_iterDirectional_at m
          (iterDirectional (1, 0) n F) p hdirX
  have hcomm :
      iterDirectional (0, 1) m
          (iterDirectional (1, 0) n F) =ᶠ[nhds p]
        iterDirectional (1, 0) n
          (iterDirectional (0, 1) m F) :=
    eventuallyEq_iterDirectional_blocks_comm
      (0, 1) (1, 0) m n F p hF
  calc
    mixedDerivative F n m p =
        iterDirectional (0, 1) m
          (iterDirectional (1, 0) n F) p := hcurrent
    _ = iterDirectional (1, 0) n
          (iterDirectional (0, 1) m F) p :=
      hcomm.self_of_nhds
    _ = orderedMixed n m (fun x y => F (x, y)) p.1 p.2 := by
      symm
      exact orderedMixed_eq_iterDirectional_at
        n m (fun x y => F (x, y)) p.1 p.2 hF

private def angleC (x y : ℝ) : ℝ :=
  Real.arctan (x / y)

private def logC (x y : ℝ) : ℝ :=
  Real.log (1 / Real.sqrt (x ^ 2 + y ^ 2))

private theorem conjugate_contDiffAt
    (k : ℕ) (p : Point) (hy : p.2 ≠ 0) :
    ContDiffAt ℝ k conjugate p := by
  unfold conjugate
  apply ContDiffAt.arctan
  apply ContDiffAt.div
  · fun_prop
  · fun_prop
  · exact hy

private theorem fundamental_contDiffAt
    (p : Point) (hy : p.2 ≠ 0) :
    ContDiffAt ℝ ⊤ fundamental p := by
  have hs : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hy]
  have hsqrt :
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ≠ 0 := by
    exact (Real.sqrt_ne_zero (by positivity)).2 hs
  unfold fundamental radius
  apply ContDiffAt.log
  · apply ContDiffAt.div
    · fun_prop
    · apply ContDiffAt.sqrt
      · fun_prop
      · exact hs
    · exact hsqrt
  · exact one_div_ne_zero hsqrt

private theorem fundamental_contDiffAt_ne_origin
    (p : Point) (hp : p ≠ (0, 0)) :
    ContDiffAt ℝ ⊤ fundamental p := by
  have hpos : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    point_sq_pos p hp
  have hs : p.1 ^ 2 + p.2 ^ 2 ≠ 0 :=
    ne_of_gt hpos
  have hsqrt :
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  unfold fundamental radius
  apply ContDiffAt.log
  · apply ContDiffAt.div
    · fun_prop
    · apply ContDiffAt.sqrt
      · fun_prop
      · exact hs
    · exact hsqrt
  · exact one_div_ne_zero hsqrt

private theorem angleC_hasDerivAt_x
    (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun s => angleC s y)
      (y / (x ^ 2 + y ^ 2)) x := by
  have hquot :
      HasDerivAt (fun s : ℝ => s / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  have h :=
    (Real.hasDerivAt_arctan (x / y)).comp x hquot
  convert h using 1
  field_simp [hy]
  <;> ring

private theorem angleC_hasDerivAt_y
    (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t => angleC x t)
      (-x / (x ^ 2 + y ^ 2)) y := by
  have hquot :
      HasDerivAt (fun t : ℝ => x / t)
        ((0 * y - x * 1) / y ^ 2) y :=
    (hasDerivAt_const y x).div (hasDerivAt_id y) hy
  have h :=
    (Real.hasDerivAt_arctan (x / y)).comp y hquot
  convert h using 1
  field_simp [hy]
  <;> ring

private theorem logC_hasDerivAt_x
    (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun s => logC s y)
      (-x / (x ^ 2 + y ^ 2)) x := by
  have hs : x ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hy]
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hsqrt :
      Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    (Real.sqrt_ne_zero hnonneg).2 hs
  have hr :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x := by
    convert
      ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1 <;>
      simp [mul_comm]
  have hsqrtDeriv := hr.sqrt hs
  have hinvDeriv := hsqrtDeriv.inv hsqrt
  have hlogDeriv := hinvDeriv.log (inv_ne_zero hsqrt)
  convert hlogDeriv using 1
  · simp [logC, one_div]
  · rw [Real.sq_sqrt hnonneg]
    simp only [Pi.inv_apply]
    field_simp [hs, hsqrt]
    <;> ring

private theorem logC_hasDerivAt_y
    (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t => logC x t)
      (-y / (x ^ 2 + y ^ 2)) y := by
  have hs : x ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hy]
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hsqrt :
      Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    (Real.sqrt_ne_zero hnonneg).2 hs
  have hr :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert
      (hasDerivAt_const y (x ^ 2)).add
        ((hasDerivAt_id y).pow 2) using 1 <;>
      simp [mul_comm]
  have hsqrtDeriv := hr.sqrt hs
  have hinvDeriv := hsqrtDeriv.inv hsqrt
  have hlogDeriv := hinvDeriv.log (inv_ne_zero hsqrt)
  convert hlogDeriv using 1
  · simp [logC, one_div]
  · rw [Real.sq_sqrt hnonneg]
    simp only [Pi.inv_apply]
    field_simp [hs, hsqrt]
    <;> ring

private theorem directional_conjugate_x
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (1, 0) conjugate (x, y) =
      y / (x ^ 2 + y ^ 2) := by
  have hgeneral :=
    hasDerivAt_slice_x conjugate x y
      (conjugate_contDiffAt 1 (x, y) hy)
  have hexplicit :
      HasDerivAt (fun s => conjugate (s, y))
        (y / (x ^ 2 + y ^ 2)) x := by
    simpa [conjugate, angleC] using
      angleC_hasDerivAt_x x y hy
  exact hgeneral.unique hexplicit

private theorem directional_conjugate_y
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (0, 1) conjugate (x, y) =
      -x / (x ^ 2 + y ^ 2) := by
  have hgeneral :=
    hasDerivAt_slice_y conjugate x y
      (conjugate_contDiffAt 1 (x, y) hy)
  have hexplicit :
      HasDerivAt (fun t => conjugate (x, t))
        (-x / (x ^ 2 + y ^ 2)) y := by
    simpa [conjugate, angleC] using
      angleC_hasDerivAt_y x y hy
  exact hgeneral.unique hexplicit

private theorem directional_fundamental_x
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (1, 0) fundamental (x, y) =
      -x / (x ^ 2 + y ^ 2) := by
  have hgeneral :=
    hasDerivAt_slice_x fundamental x y
      ((fundamental_contDiffAt (x, y) hy).of_le le_top)
  have hexplicit :
      HasDerivAt (fun s => fundamental (s, y))
        (-x / (x ^ 2 + y ^ 2)) x := by
    simpa [fundamental, radius, logC] using
      logC_hasDerivAt_x x y hy
  exact hgeneral.unique hexplicit

private theorem directional_fundamental_y
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (0, 1) fundamental (x, y) =
      -y / (x ^ 2 + y ^ 2) := by
  have hgeneral :=
    hasDerivAt_slice_y fundamental x y
      ((fundamental_contDiffAt (x, y) hy).of_le le_top)
  have hexplicit :
      HasDerivAt (fun t => fundamental (x, t))
        (-y / (x ^ 2 + y ^ 2)) y := by
    simpa [fundamental, radius, logC] using
      logC_hasDerivAt_y x y hy
  exact hgeneral.unique hexplicit

private theorem eventuallyEq_CR_x
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (1, 0) conjugate =ᶠ[nhds (x, y)]
      (fun q =>
        -directionalDerivative (0, 1) fundamental q) := by
  have hnear :
      ∀ᶠ q : Point in nhds (x, y), q.2 ≠ 0 :=
    continuousAt_snd.eventually_ne hy
  filter_upwards [hnear] with q hq
  rw [directional_conjugate_x q.1 q.2 hq,
    directional_fundamental_y q.1 q.2 hq]
  ring

private theorem eventuallyEq_CR_y
    (x y : ℝ) (hy : y ≠ 0) :
    directionalDerivative (0, 1) conjugate =ᶠ[nhds (x, y)]
      directionalDerivative (1, 0) fundamental := by
  have hnear :
      ∀ᶠ q : Point in nhds (x, y), q.2 ≠ 0 :=
    continuousAt_snd.eventually_ne hy
  filter_upwards [hnear] with q hq
  rw [directional_conjugate_y q.1 q.2 hq,
    directional_fundamental_x q.1 q.2 hq]

private theorem directionalDerivative_neg
    (d : Point) (F : Point → ℝ) :
    directionalDerivative d (fun q => -F q) =
      fun q => -directionalDerivative d F q := by
  funext q
  unfold directionalDerivative
  rw [show (fun q => -F q) = -F by rfl, fderiv_neg]
  rfl

private theorem iterDirectional_neg
    (d : Point) (n : ℕ) (F : Point → ℝ) :
    iterDirectional d n (fun q => -F q) =
      fun q => -iterDirectional d n F q := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
      rw [iterDirectional, directionalDerivative_neg, ih]
      rfl

private theorem orderedMixed_hasDerivAt
    (n m : ℕ) (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiffAt ℝ (n + m + 1)
      (Function.uncurry u) (x, y)) :
    HasDerivAt
        (fun s => orderedMixed n m u s y)
        (orderedMixed (n + 1) m u x y) x ∧
      HasDerivAt
        (fun t => orderedMixed n m u x t)
        (orderedMixed n (m + 1) u x y) y := by
  let U : Point → ℝ := Function.uncurry u
  let Y : Point → ℝ :=
    iterDirectional (0, 1) m U
  let F : Point → ℝ :=
    iterDirectional (1, 0) n Y
  have hU_nm :
      ContDiffAt ℝ (n + m) U (x, y) :=
    (by
      apply hu.of_le
      simpa [U] using
        (self_le_add_right
          ((n : WithTop ENat) + (m : WithTop ENat)) 1))
  have hU_mn1 :
      ContDiffAt ℝ (m + (n + 1)) U (x, y) := by
    simpa [U, add_assoc, add_comm, add_left_comm] using hu
  have hY :
      ContDiffAt ℝ (n + 1) Y (x, y) :=
    iterDirectional_contDiffAt
      (0, 1) m (n + 1) U (x, y) hU_mn1
  have hF : ContDiffAt ℝ 1 F (x, y) :=
    iterDirectional_contDiffAt
      (1, 0) n 1 Y (x, y) hY
  have hnear :
      ∀ᶠ q in nhds (x, y),
        ContDiffAt ℝ (n + m) U q :=
    contDiffAt_eventually_nat
      (n + m) U (x, y) hU_nm
  have hmap_x :
      Tendsto (fun s : ℝ => (s, y))
        (nhds x) (nhds (x, y)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmap_y :
      Tendsto (fun t : ℝ => (x, t))
        (nhds y) (nhds (x, y)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hsource_x :
      (fun s => orderedMixed n m u s y) =ᶠ[nhds x]
        (fun s => F (s, y)) := by
    filter_upwards [hmap_x hnear] with s hs
    change ContDiffAt ℝ (n + m) U (s, y) at hs
    simpa [U, Y, F] using
      orderedMixed_eq_iterDirectional_at
        n m u s y (by simpa [U] using hs)
  have hsource_y :
      (fun t => orderedMixed n m u x t) =ᶠ[nhds y]
        (fun t => F (x, t)) := by
    filter_upwards [hmap_y hnear] with t ht
    change ContDiffAt ℝ (n + m) U (x, t) at ht
    simpa [U, Y, F] using
      orderedMixed_eq_iterDirectional_at
        n m u x t (by simpa [U] using ht)
  have hdxF :
      directionalDerivative (1, 0) F (x, y) =
        iterDirectional (1, 0) (n + 1) Y (x, y) := by
    have hcomm :=
      (eventuallyEq_directional_iterDirectional_comm
        (1, 0) (1, 0) n Y (x, y) hY).self_of_nhds
    simpa [F, Nat.succ_eq_add_one] using hcomm
  have hU_n1m :
      ContDiffAt ℝ ((n + 1) + m) U (x, y) := by
    simpa [U, add_assoc, add_comm, add_left_comm] using hu
  have hdx_value :
      directionalDerivative (1, 0) F (x, y) =
        orderedMixed (n + 1) m u x y := by
    calc
      directionalDerivative (1, 0) F (x, y) =
          iterDirectional (1, 0) (n + 1) Y (x, y) := hdxF
      _ = orderedMixed (n + 1) m u x y := by
        simpa [U, Y] using
          (orderedMixed_eq_iterDirectional_at
            (n + 1) m u x y
            (by simpa [U] using hU_n1m)).symm
  have hU_m1 :
      ContDiffAt ℝ (m + 1) U (x, y) := by
    apply hu.of_le
    simpa only [Nat.cast_add, add_assoc] using
      (self_le_add_left
        ((m : WithTop ENat) + 1) (n : WithTop ENat))
  have hdyY :
      directionalDerivative (0, 1) Y =ᶠ[nhds (x, y)]
        iterDirectional (0, 1) (m + 1) U := by
    simpa [Y, Nat.succ_eq_add_one] using
      eventuallyEq_directional_iterDirectional_comm
        (0, 1) (0, 1) m U (x, y) hU_m1
  have hdyF :
      directionalDerivative (0, 1) F =ᶠ[nhds (x, y)]
        iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 1) U) := by
    have hcomm :=
      eventuallyEq_directional_iterDirectional_comm
        (0, 1) (1, 0) n Y (x, y) hY
    exact hcomm.trans
      (eventuallyEq_iterDirectional (1, 0) n hdyY)
  have hU_nm1 :
      ContDiffAt ℝ (n + (m + 1)) U (x, y) := by
    simpa [U, add_assoc] using hu
  have hdy_value :
      directionalDerivative (0, 1) F (x, y) =
        orderedMixed n (m + 1) u x y := by
    calc
      directionalDerivative (0, 1) F (x, y) =
          iterDirectional (1, 0) n
            (iterDirectional (0, 1) (m + 1) U) (x, y) :=
        hdyF.self_of_nhds
      _ = orderedMixed n (m + 1) u x y := by
        simpa [U] using
          (orderedMixed_eq_iterDirectional_at
            n (m + 1) u x y
            (by simpa [U] using hU_nm1)).symm
  constructor
  · exact
      ((hasDerivAt_slice_x F x y hF).congr_deriv
        hdx_value).congr_of_eventuallyEq hsource_x
  · exact
      ((hasDerivAt_slice_y F x y hF).congr_deriv
        hdy_value).congr_of_eventuallyEq hsource_y

private theorem currentMixed_hasDerivAt
    (n m : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + m + 1) F p) :
    HasDerivAt
        (fun x => mixedDerivative F n m (x, p.2))
        (mixedDerivative F (n + 1) m p) p.1 ∧
      HasDerivAt
        (fun y => mixedDerivative F n m (p.1, y))
        (mixedDerivative F n (m + 1) p) p.2 := by
  let u : ℝ → ℝ → ℝ := fun x y => F (x, y)
  have hordered :=
    orderedMixed_hasDerivAt n m u p.1 p.2
      (by simpa [u] using hF)
  have hbase : ContDiffAt ℝ (n + m) F p := by
    apply hF.of_le
    simpa only [Nat.cast_add, add_assoc] using
      (self_le_add_right
        ((n : WithTop ENat) + (m : WithTop ENat)) 1)
  have hnear :
      ∀ᶠ q in nhds p, ContDiffAt ℝ (n + m) F q :=
    contDiffAt_eventually_nat (n + m) F p hbase
  have hmap_x :
      Tendsto (fun x : ℝ => (x, p.2))
        (nhds p.1) (nhds p) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmap_y :
      Tendsto (fun y : ℝ => (p.1, y))
        (nhds p.2) (nhds p) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hxsource :
      (fun x => mixedDerivative F n m (x, p.2)) =ᶠ[nhds p.1]
        (fun x => orderedMixed n m u x p.2) := by
    filter_upwards [hmap_x hnear] with x hx
    simpa [u] using
      mixedDerivative_eq_orderedMixed_at
        n m F (x, p.2) hx
  have hysource :
      (fun y => mixedDerivative F n m (p.1, y)) =ᶠ[nhds p.2]
        (fun y => orderedMixed n m u p.1 y) := by
    filter_upwards [hmap_y hnear] with y hy
    simpa [u] using
      mixedDerivative_eq_orderedMixed_at
        n m F (p.1, y) hy
  have hxvalue :
      mixedDerivative F (n + 1) m p =
        orderedMixed (n + 1) m u p.1 p.2 := by
    apply mixedDerivative_eq_orderedMixed_at
    simpa [Nat.succ_eq_add_one, add_assoc, add_comm,
      add_left_comm] using hF
  have hyvalue :
      mixedDerivative F n (m + 1) p =
        orderedMixed n (m + 1) u p.1 p.2 := by
    apply mixedDerivative_eq_orderedMixed_at
    simpa [add_assoc] using hF
  constructor
  · exact
      (hordered.1.congr_deriv hxvalue.symm).congr_of_eventuallyEq
        hxsource
  · exact
      (hordered.2.congr_deriv hyvalue.symm).congr_of_eventuallyEq
        hysource

private theorem currentMixed_contDiffAt
    (n m k : ℕ) (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (n + m + k) F p) :
    ContDiffAt ℝ k (mixedDerivative F n m) p := by
  let D : Point → ℝ :=
    iterDirectional (1, 0) n
      (iterDirectional (0, 1) m F)
  have hmnk :
      ContDiffAt ℝ (m + (n + k)) F p := by
    simpa [add_assoc, add_comm, add_left_comm] using hF
  have hY :
      ContDiffAt ℝ (n + k)
        (iterDirectional (0, 1) m F) p :=
    iterDirectional_contDiffAt
      (0, 1) m (n + k) F p hmnk
  have hD : ContDiffAt ℝ k D p := by
    exact iterDirectional_contDiffAt
      (1, 0) n k
      (iterDirectional (0, 1) m F) p hY
  have hbase : ContDiffAt ℝ (n + m) F p := by
    apply hF.of_le
    simpa only [Nat.cast_add, add_assoc] using
      (self_le_add_right
        ((n : WithTop ENat) + (m : WithTop ENat))
        (k : WithTop ENat))
  have hnear :
      ∀ᶠ q in nhds p, ContDiffAt ℝ (n + m) F q :=
    contDiffAt_eventually_nat (n + m) F p hbase
  have heq :
      mixedDerivative F n m =ᶠ[nhds p] D := by
    filter_upwards [hnear] with q hq
    calc
      mixedDerivative F n m q =
          orderedMixed n m (fun x y => F (x, y)) q.1 q.2 :=
        mixedDerivative_eq_orderedMixed_at n m F q hq
      _ = D q := by
        simpa [D] using
          orderedMixed_eq_iterDirectional_at
            n m (fun x y => F (x, y)) q.1 q.2 hq
  exact hD.congr_of_eventuallyEq heq

private theorem orderedMixed_angle_x_identity
    (n m : ℕ) (hm : 1 ≤ m)
    (x y : ℝ) (hy : y ≠ 0) :
    orderedMixed (n + 1) m angleC x y =
      orderedMixed (n + 2) (m - 1) logC x y := by
  let A : Point → ℝ := conjugate
  let L : Point → ℝ := fundamental
  have hm_form : m - 1 + 1 = m :=
    Nat.sub_add_cancel hm
  have hA :
      ContDiffAt ℝ ((n + 1) + m) A (x, y) := by
    simpa [A] using
      conjugate_contDiffAt ((n + 1) + m) (x, y) hy
  have hL :
      ContDiffAt ℝ ((n + 2) + (m - 1)) L (x, y) :=
    (fundamental_contDiffAt (x, y) hy).of_le le_top
  have hcommL :
      iterDirectional (0, 1) (m - 1)
          (directionalDerivative (1, 0) L) =ᶠ[nhds (x, y)]
        directionalDerivative (1, 0)
          (iterDirectional (0, 1) (m - 1) L) := by
    exact
      (eventuallyEq_directional_iterDirectional_comm
        (1, 0) (0, 1) (m - 1) L (x, y)
        ((fundamental_contDiffAt (x, y) hy).of_le le_top)).symm
  have hinner :
      iterDirectional (0, 1) (m - 1)
          (directionalDerivative (0, 1) A) =ᶠ[nhds (x, y)]
        directionalDerivative (1, 0)
          (iterDirectional (0, 1) (m - 1) L) := by
    have hcr :
        directionalDerivative (0, 1) A =ᶠ[nhds (x, y)]
          directionalDerivative (1, 0) L := by
      simpa [A, L] using eventuallyEq_CR_y x y hy
    exact
      (eventuallyEq_iterDirectional
        (0, 1) (m - 1) hcr).trans hcommL
  have hlift :
      iterDirectional (1, 0) (n + 1)
          (iterDirectional (0, 1) (m - 1)
            (directionalDerivative (0, 1) A)) =ᶠ[nhds (x, y)]
        iterDirectional (1, 0) (n + 1)
          (directionalDerivative (1, 0)
            (iterDirectional (0, 1) (m - 1) L)) :=
    eventuallyEq_iterDirectional (1, 0) (n + 1) hinner
  calc
    orderedMixed (n + 1) m angleC x y =
        iterDirectional (1, 0) (n + 1)
          (iterDirectional (0, 1) m A) (x, y) := by
      simpa [A, angleC, conjugate] using
        orderedMixed_eq_iterDirectional_at
          (n + 1) m angleC x y
          (by simpa [A, angleC, conjugate] using hA)
    _ = iterDirectional (1, 0) (n + 1)
          (iterDirectional (0, 1) (m - 1)
            (directionalDerivative (0, 1) A)) (x, y) := by
      rw [← hm_form]
      rfl
    _ = iterDirectional (1, 0) (n + 1)
          (directionalDerivative (1, 0)
            (iterDirectional (0, 1) (m - 1) L)) (x, y) :=
      hlift.self_of_nhds
    _ = iterDirectional (1, 0) (n + 2)
          (iterDirectional (0, 1) (m - 1) L) (x, y) := by
      rfl
    _ = orderedMixed (n + 2) (m - 1) logC x y := by
      simpa [L, logC, fundamental, radius] using
        (orderedMixed_eq_iterDirectional_at
          (n + 2) (m - 1) logC x y
          (by
            simpa [L, logC, fundamental, radius] using hL)).symm

private theorem orderedMixed_angle_y_identity
    (n m : ℕ) (hn : 1 ≤ n)
    (x y : ℝ) (hy : y ≠ 0) :
    orderedMixed n (m + 1) angleC x y =
      -orderedMixed (n - 1) (m + 2) logC x y := by
  let A : Point → ℝ := conjugate
  let L : Point → ℝ := fundamental
  have hn_form : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hA :
      ContDiffAt ℝ (n + (m + 1)) A (x, y) := by
    simpa [A] using
      conjugate_contDiffAt (n + (m + 1)) (x, y) hy
  have hL :
      ContDiffAt ℝ ((n - 1) + (m + 2)) L (x, y) :=
    (fundamental_contDiffAt (x, y) hy).of_le le_top
  have hcommA :
      directionalDerivative (1, 0)
          (iterDirectional (0, 1) (m + 1) A) =ᶠ[nhds (x, y)]
        iterDirectional (0, 1) (m + 1)
          (directionalDerivative (1, 0) A) := by
    apply
      eventuallyEq_directional_iterDirectional_comm
        (1, 0) (0, 1) (m + 1) A (x, y)
    simpa [A] using
      conjugate_contDiffAt (m + 2) (x, y) hy
  have hcr :
      directionalDerivative (1, 0) A =ᶠ[nhds (x, y)]
        (fun q =>
          -directionalDerivative (0, 1) L q) := by
    simpa [A, L] using eventuallyEq_CR_x x y hy
  have hnegY :
      iterDirectional (0, 1) (m + 1)
          (fun q => -directionalDerivative (0, 1) L q) =
        fun q =>
          -iterDirectional (0, 1) (m + 2) L q := by
    calc
      iterDirectional (0, 1) (m + 1)
          (fun q => -directionalDerivative (0, 1) L q) =
        (fun q =>
          -iterDirectional (0, 1) (m + 1)
            (directionalDerivative (0, 1) L) q) :=
          iterDirectional_neg
            (0, 1) (m + 1)
              (directionalDerivative (0, 1) L)
      _ = fun q =>
          -iterDirectional (0, 1) (m + 2) L q := by
        rfl
  have hinner :
      directionalDerivative (1, 0)
          (iterDirectional (0, 1) (m + 1) A) =ᶠ[nhds (x, y)]
        (fun q =>
          -iterDirectional (0, 1) (m + 2) L q) := by
    exact hcommA.trans
      ((eventuallyEq_iterDirectional
        (0, 1) (m + 1) hcr).trans
          (Filter.Eventually.of_forall
            (fun q => congrFun hnegY q)))
  have hlift :
      iterDirectional (1, 0) (n - 1)
          (directionalDerivative (1, 0)
            (iterDirectional (0, 1) (m + 1) A)) =ᶠ[nhds (x, y)]
        iterDirectional (1, 0) (n - 1)
          (fun q =>
            -iterDirectional (0, 1) (m + 2) L q) :=
    eventuallyEq_iterDirectional (1, 0) (n - 1) hinner
  have hnegX :
      iterDirectional (1, 0) (n - 1)
          (fun q =>
            -iterDirectional (0, 1) (m + 2) L q) =
        fun q =>
          -iterDirectional (1, 0) (n - 1)
            (iterDirectional (0, 1) (m + 2) L) q :=
    iterDirectional_neg
      (1, 0) (n - 1)
        (iterDirectional (0, 1) (m + 2) L)
  calc
    orderedMixed n (m + 1) angleC x y =
        iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 1) A) (x, y) := by
      simpa [A, angleC, conjugate] using
        orderedMixed_eq_iterDirectional_at
          n (m + 1) angleC x y
          (by simpa [A, angleC, conjugate] using hA)
    _ = iterDirectional (1, 0) (n - 1)
          (directionalDerivative (1, 0)
            (iterDirectional (0, 1) (m + 1) A)) (x, y) := by
      rw [← hn_form]
      rfl
    _ = iterDirectional (1, 0) (n - 1)
          (fun q =>
            -iterDirectional (0, 1) (m + 2) L q) (x, y) :=
      hlift.self_of_nhds
    _ = -iterDirectional (1, 0) (n - 1)
          (iterDirectional (0, 1) (m + 2) L) (x, y) :=
      congrFun hnegX (x, y)
    _ = -orderedMixed (n - 1) (m + 2) logC x y := by
      have hrep :
          orderedMixed (n - 1) (m + 2) logC x y =
            iterDirectional (1, 0) (n - 1)
              (iterDirectional (0, 1) (m + 2) L) (x, y) := by
        simpa [L, logC, fundamental, radius] using
          orderedMixed_eq_iterDirectional_at
            (n - 1) (m + 2) logC x y
            (by
              simpa [L, logC, fundamental, radius] using hL)
      exact congrArg Neg.neg hrep.symm

private theorem mixedDerivative_conjugate_x_identity
    (n m : ℕ) (hm : 1 ≤ m)
    (p : Point) (hy : p.2 ≠ 0) :
    mixedDerivative conjugate (n + 1) m p =
      mixedDerivative fundamental (n + 2) (m - 1) p := by
  rw [
    mixedDerivative_eq_orderedMixed_at
      (n + 1) m conjugate p
      (conjugate_contDiffAt ((n + 1) + m) p hy),
    mixedDerivative_eq_orderedMixed_at
      (n + 2) (m - 1) fundamental p
      ((fundamental_contDiffAt p hy).of_le le_top)]
  change orderedMixed (n + 1) m angleC p.1 p.2 =
    orderedMixed (n + 2) (m - 1) logC p.1 p.2
  exact orderedMixed_angle_x_identity n m hm p.1 p.2 hy

private theorem mixedDerivative_conjugate_y_identity
    (n m : ℕ) (hn : 1 ≤ n)
    (p : Point) (hy : p.2 ≠ 0) :
    mixedDerivative conjugate n (m + 1) p =
      -mixedDerivative fundamental (n - 1) (m + 2) p := by
  rw [
    mixedDerivative_eq_orderedMixed_at
      n (m + 1) conjugate p
      (conjugate_contDiffAt (n + (m + 1)) p hy),
    mixedDerivative_eq_orderedMixed_at
      (n - 1) (m + 2) fundamental p
      ((fundamental_contDiffAt p hy).of_le le_top)]
  change orderedMixed n (m + 1) angleC p.1 p.2 =
    -orderedMixed (n - 1) (m + 2) logC p.1 p.2
  exact orderedMixed_angle_y_identity n m hn p.1 p.2 hy

private theorem derivedPotential_gradient
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hy : p.2 ≠ 0) :
    HasCoordinateGradientAt
      (derivedPotential n m) (derivedField n m p) p := by
  have hmix :=
    currentMixed_hasDerivAt n m conjugate p
      (conjugate_contDiffAt (n + m + 1) p hy)
  have hx :=
    hmix.1.congr_deriv
      (mixedDerivative_conjugate_x_identity n m hm p hy)
  have hy' :=
    hmix.2.congr_deriv
      (mixedDerivative_conjugate_y_identity n m hn p hy)
  exact ⟨by simpa [derivedPotential, derivedField] using hx,
    by simpa [derivedPotential, derivedField] using hy'⟩

private theorem derivedPotential_contDiffAt
    (n m k : ℕ) (p : Point) (hy : p.2 ≠ 0) :
    ContDiffAt ℝ k (derivedPotential n m) p := by
  unfold derivedPotential
  apply currentMixed_contDiffAt
  exact conjugate_contDiffAt (n + m + k) p hy

private theorem partial_comm_at
    (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ 2 F p) :
    partialY (partialX F) p = partialX (partialY F) p := by
  have hFone : ContDiffAt ℝ 1 F p := hF.of_le (by norm_num)
  have hnear :
      ∀ᶠ q in nhds p, ContDiffAt ℝ 1 F q :=
    contDiffAt_eventually_nat 1 F p hFone
  have hx :
      partialX F =ᶠ[nhds p]
        directionalDerivative (1, 0) F := by
    filter_upwards [hnear] with q hq
    exact (hasDerivAt_slice_x F q.1 q.2 hq).deriv
  have hy :
      partialY F =ᶠ[nhds p]
        directionalDerivative (0, 1) F := by
    filter_upwards [hnear] with q hq
    exact (hasDerivAt_slice_y F q.1 q.2 hq).deriv
  have hdx :
      ContDiffAt ℝ 1 (directionalDerivative (1, 0) F) p := by
    exact directionalDerivative_contDiffAt (1, 0) 1 F p hF
  have hdy :
      ContDiffAt ℝ 1 (directionalDerivative (0, 1) F) p := by
    exact directionalDerivative_contDiffAt (0, 1) 1 F p hF
  calc
    partialY (partialX F) p =
        partialY (directionalDerivative (1, 0) F) p :=
      (eventuallyEq_partialY hx).self_of_nhds
    _ = directionalDerivative (0, 1)
          (directionalDerivative (1, 0) F) p :=
      (hasDerivAt_slice_y
        (directionalDerivative (1, 0) F) p.1 p.2 hdx).deriv
    _ = directionalDerivative (1, 0)
          (directionalDerivative (0, 1) F) p :=
      directionalDerivative_comm_at (0, 1) (1, 0) F p hF
    _ = partialX (directionalDerivative (0, 1) F) p :=
      (hasDerivAt_slice_x
        (directionalDerivative (0, 1) F) p.1 p.2 hdy).deriv.symm
    _ = partialX (partialY F) p :=
      (eventuallyEq_partialX hy).self_of_nhds.symm

private theorem upper_solution_iff_potential
    (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsUpperSolution z n m ↔
      ∃ C : ℝ, ∀ p, 0 < p.2 →
        z p = derivedPotential n m p + C := by
  constructor
  · intro hz
    let C : ℝ :=
      z (0, 1) - derivedPotential n m (0, 1)
    refine ⟨C, ?_⟩
    intro p hp
    let horizontal : ℝ → ℝ :=
      fun x =>
        z (x, p.2) - derivedPotential n m (x, p.2)
    have hhorizontal (x : ℝ) :
        HasDerivAt horizontal 0 x := by
      have hz' := (hz (x, p.2) hp).1
      have hpot :=
        (derivedPotential_gradient n m hn hm
          (x, p.2) (ne_of_gt hp)).1
      simpa [horizontal] using hz'.sub hpot
    have hconstx :
        horizontal p.1 = horizontal 0 :=
      is_const_of_deriv_eq_zero
        (fun x => (hhorizontal x).differentiableAt)
        (fun x => (hhorizontal x).deriv) p.1 0
    let vertical : ℝ → ℝ :=
      fun y =>
        z (0, y) - derivedPotential n m (0, y)
    have hvertical (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) :
        HasDerivAt vertical 0 y := by
      have hz' := (hz (0, y) hy).2
      have hpot :=
        (derivedPotential_gradient n m hn hm
          (0, y) (ne_of_gt hy)).2
      simpa [vertical] using hz'.sub hpot
    have hconsty :
        vertical p.2 = vertical 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero
        isPreconnected_Ioi
        (fun y hy =>
          (hvertical y hy).differentiableAt.differentiableWithinAt)
        (fun y hy => (hvertical y hy).deriv)
        hp (by norm_num)
    dsimp only [horizontal] at hconstx
    dsimp only [vertical, C] at hconsty ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro p hp
    have hpot :=
      derivedPotential_gradient n m hn hm p (ne_of_gt hp)
    constructor
    · have hfun :
          (fun x => z (x, p.2)) =
            (fun x =>
              derivedPotential n m (x, p.2) + C) := by
          funext x
          exact hC (x, p.2) hp
      rw [hfun]
      exact hpot.1.add_const C
    · have hnear :
          ∀ᶠ y in nhds p.2, 0 < y :=
        isOpen_Ioi.mem_nhds hp
      have hfun :
          (fun y => z (p.1, y)) =ᶠ[nhds p.2]
            (fun y =>
              derivedPotential n m (p.1, y) + C) := by
        filter_upwards [hnear] with y hy
        exact hC (p.1, y) hy
      exact (hpot.2.add_const C).congr_of_eventuallyEq hfun

private theorem lower_solution_iff_potential
    (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsLowerSolution z n m ↔
      ∃ C : ℝ, ∀ p, p.2 < 0 →
        z p = derivedPotential n m p + C := by
  constructor
  · intro hz
    let C : ℝ :=
      z (0, -1) - derivedPotential n m (0, -1)
    refine ⟨C, ?_⟩
    intro p hp
    let horizontal : ℝ → ℝ :=
      fun x =>
        z (x, p.2) - derivedPotential n m (x, p.2)
    have hhorizontal (x : ℝ) :
        HasDerivAt horizontal 0 x := by
      have hz' := (hz (x, p.2) hp).1
      have hpot :=
        (derivedPotential_gradient n m hn hm
          (x, p.2) (ne_of_lt hp)).1
      simpa [horizontal] using hz'.sub hpot
    have hconstx :
        horizontal p.1 = horizontal 0 :=
      is_const_of_deriv_eq_zero
        (fun x => (hhorizontal x).differentiableAt)
        (fun x => (hhorizontal x).deriv) p.1 0
    let vertical : ℝ → ℝ :=
      fun y =>
        z (0, y) - derivedPotential n m (0, y)
    have hvertical (y : ℝ) (hy : y ∈ Set.Iio (0 : ℝ)) :
        HasDerivAt vertical 0 y := by
      have hz' := (hz (0, y) hy).2
      have hpot :=
        (derivedPotential_gradient n m hn hm
          (0, y) (ne_of_lt hy)).2
      simpa [vertical] using hz'.sub hpot
    have hconsty :
        vertical p.2 = vertical (-1) :=
      isOpen_Iio.is_const_of_deriv_eq_zero
        isPreconnected_Iio
        (fun y hy =>
          (hvertical y hy).differentiableAt.differentiableWithinAt)
        (fun y hy => (hvertical y hy).deriv)
        hp (by norm_num)
    dsimp only [horizontal] at hconstx
    dsimp only [vertical, C] at hconsty ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro p hp
    have hpot :=
      derivedPotential_gradient n m hn hm p (ne_of_lt hp)
    constructor
    · have hfun :
          (fun x => z (x, p.2)) =
            (fun x =>
              derivedPotential n m (x, p.2) + C) := by
          funext x
          exact hC (x, p.2) hp
      rw [hfun]
      exact hpot.1.add_const C
    · have hnear :
          ∀ᶠ y in nhds p.2, y < 0 :=
        isOpen_Iio.mem_nhds hp
      have hfun :
          (fun y => z (p.1, y)) =ᶠ[nhds p.2]
            (fun y =>
              derivedPotential n m (p.1, y) + C) := by
        filter_upwards [hnear] with y hy
        exact hC (p.1, y) hy
      exact (hpot.2.add_const C).congr_of_eventuallyEq hfun

private theorem derivedField_first_horizontal_continuous
    (n m : ℕ) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun x => (derivedField n m (x, y)).1) := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt
    (fun x =>
      mixedDerivative fundamental (n + 2) (m - 1) (x, y)) x
  have hfull :
      ContinuousAt
        (mixedDerivative fundamental (n + 2) (m - 1))
        (x, y) :=
    (currentMixed_contDiffAt
      (n + 2) (m - 1) 0 fundamental (x, y)
      ((fundamental_contDiffAt (x, y) hy).of_le le_top)).continuousAt
  have hpair :
      ContinuousAt (fun s : ℝ => (s, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  exact hfull.comp' (f := fun s : ℝ => (s, y)) hpair

private theorem derivedField_second_vertical_continuousAt
    (n m : ℕ) (x y : ℝ) (hy : y ≠ 0) :
    ContinuousAt (fun t => (derivedField n m (x, t)).2) y := by
  change ContinuousAt
    (fun t =>
      -mixedDerivative fundamental (n - 1) (m + 2) (x, t)) y
  have hfull :
      ContinuousAt
        (mixedDerivative fundamental (n - 1) (m + 2))
        (x, y) :=
    (currentMixed_contDiffAt
      (n - 1) (m + 2) 0 fundamental (x, y)
      ((fundamental_contDiffAt (x, y) hy).of_le le_top)).continuousAt
  have hpair :
      ContinuousAt (fun t : ℝ => (x, t)) y :=
    continuousAt_const.prodMk continuousAt_id
  exact (hfull.comp' (f := fun t : ℝ => (x, t)) hpair).neg

private theorem constructedUpper_eq_potential_sub
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hp : 0 < p.2) :
    constructedUpper n m p =
      derivedPotential n m p -
        derivedPotential n m (0, 1) := by
  have hxder (x : ℝ) :
      HasDerivAt
        (fun s => derivedPotential n m (s, p.2))
        ((derivedField n m (x, p.2)).1) x :=
    (derivedPotential_gradient n m hn hm
      (x, p.2) (ne_of_gt hp)).1
  have hxint :
      IntervalIntegrable
        (fun x => (derivedField n m (x, p.2)).1)
        MeasureTheory.volume 0 p.1 :=
    (derivedField_first_horizontal_continuous
      n m p.2 (ne_of_gt hp)).intervalIntegrable 0 p.1
  have hxFTC :
      (∫ x in (0 : ℝ)..p.1,
        (derivedField n m (x, p.2)).1) =
        derivedPotential n m (p.1, p.2) -
          derivedPotential n m (0, p.2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hxder x) hxint
  have htpos (t : ℝ)
      (ht : t ∈ Set.uIcc (1 : ℝ) p.2) :
      0 < t := by
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht <;> linarith
  have hyder (t : ℝ)
      (ht : t ∈ Set.uIcc (1 : ℝ) p.2) :
      HasDerivAt
        (fun s => derivedPotential n m (0, s))
        ((derivedField n m (0, t)).2) t :=
    (derivedPotential_gradient n m hn hm
      (0, t) (ne_of_gt (htpos t ht))).2
  have hycont :
      ContinuousOn
        (fun t => (derivedField n m (0, t)).2)
        (Set.uIcc (1 : ℝ) p.2) := by
    intro t ht
    exact
      (derivedField_second_vertical_continuousAt
        n m 0 t (ne_of_gt (htpos t ht))).continuousWithinAt
  have hyFTC :
      (∫ t in (1 : ℝ)..p.2,
        (derivedField n m (0, t)).2) =
        derivedPotential n m (0, p.2) -
          derivedPotential n m (0, 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hyder hycont.intervalIntegrable
  unfold constructedUpper
  rw [hxFTC, hyFTC]
  ring

private theorem constructedLower_eq_potential_sub
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hp : p.2 < 0) :
    constructedLower n m p =
      derivedPotential n m p -
        derivedPotential n m (0, -1) := by
  have hxder (x : ℝ) :
      HasDerivAt
        (fun s => derivedPotential n m (s, p.2))
        ((derivedField n m (x, p.2)).1) x :=
    (derivedPotential_gradient n m hn hm
      (x, p.2) (ne_of_lt hp)).1
  have hxint :
      IntervalIntegrable
        (fun x => (derivedField n m (x, p.2)).1)
        MeasureTheory.volume 0 p.1 :=
    (derivedField_first_horizontal_continuous
      n m p.2 (ne_of_lt hp)).intervalIntegrable 0 p.1
  have hxFTC :
      (∫ x in (0 : ℝ)..p.1,
        (derivedField n m (x, p.2)).1) =
        derivedPotential n m (p.1, p.2) -
          derivedPotential n m (0, p.2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hxder x) hxint
  have htneg (t : ℝ)
      (ht : t ∈ Set.uIcc (-1 : ℝ) p.2) :
      t < 0 := by
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht <;> linarith
  have hyder (t : ℝ)
      (ht : t ∈ Set.uIcc (-1 : ℝ) p.2) :
      HasDerivAt
        (fun s => derivedPotential n m (0, s))
        ((derivedField n m (0, t)).2) t :=
    (derivedPotential_gradient n m hn hm
      (0, t) (ne_of_lt (htneg t ht))).2
  have hycont :
      ContinuousOn
        (fun t => (derivedField n m (0, t)).2)
        (Set.uIcc (-1 : ℝ) p.2) := by
    intro t ht
    exact
      (derivedField_second_vertical_continuousAt
        n m 0 t (ne_of_lt (htneg t ht))).continuousWithinAt
  have hyFTC :
      (∫ t in (-1 : ℝ)..p.2,
        (derivedField n m (0, t)).2) =
        derivedPotential n m (0, p.2) -
          derivedPotential n m (0, -1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hyder hycont.intervalIntegrable
  unfold constructedLower
  rw [hxFTC, hyFTC]
  ring

private theorem curlDefect_eq_mixed_sum
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hp : p ≠ (0, 0)) :
    curlDefect n m p =
      mixedDerivative fundamental (n + 2) m p +
        mixedDerivative fundamental n (m + 2) p := by
  have hsmooth :=
    fundamental_contDiffAt_ne_origin p hp
  have hfirst :=
    (currentMixed_hasDerivAt
      (n + 2) (m - 1) fundamental p
      (hsmooth.of_le le_top)).2
  have hfirst' :
      HasDerivAt
        (fun y => (derivedField n m (p.1, y)).1)
        (mixedDerivative fundamental (n + 2) m p) p.2 := by
    simpa [derivedField, Nat.sub_add_cancel hm] using hfirst
  have hsecond :=
    (currentMixed_hasDerivAt
      (n - 1) (m + 2) fundamental p
      (hsmooth.of_le le_top)).1.neg
  have hsecond' :
      HasDerivAt
        (fun x => (derivedField n m (x, p.2)).2)
        (-mixedDerivative fundamental n (m + 2) p) p.1 := by
    simpa [derivedField, Nat.sub_add_cancel hn] using hsecond
  unfold curlDefect partialX partialY
  rw [hfirst'.deriv, hsecond'.deriv]
  ring

private theorem mixed_fundamental_sum_zero
    (n m : ℕ) (p : Point) (hp : p ≠ (0, 0)) :
    mixedDerivative fundamental (n + 2) m p +
        mixedDerivative fundamental n (m + 2) p = 0 := by
  have hsmooth :=
    fundamental_contDiffAt_ne_origin p hp
  have hnear :
      ∀ᶠ q : Point in nhds p, q ≠ (0, 0) :=
    continuousAt_id.eventually_ne hp
  have hbase :
      iterDirectional (1, 0) 2 fundamental =ᶠ[nhds p]
        (fun q =>
          -iterDirectional (0, 1) 2 fundamental q) := by
    filter_upwards [hnear] with q hq
    have htwo :
        ContDiffAt ℝ 2 fundamental q :=
      (fundamental_contDiffAt_ne_origin q hq).of_le le_top
    have hx :
        partialX (partialX fundamental) q =
          iterDirectional (1, 0) 2 fundamental q := by
      change iterX 2 fundamental q =
        iterDirectional (1, 0) 2 fundamental q
      exact iterX_eq_iterDirectional_at 2 fundamental q htwo
    have hy :
        partialY (partialY fundamental) q =
          iterDirectional (0, 1) 2 fundamental q := by
      change iterY 2 fundamental q =
        iterDirectional (0, 1) 2 fundamental q
      exact iterY_eq_iterDirectional_at 2 fundamental q htwo
    have hz := laplacian_zero q hq
    unfold laplacian at hz
    rw [hx, hy] at hz
    linarith
  have hlift :=
    eventuallyEq_iterDirectional (1, 0) n
      (eventuallyEq_iterDirectional (0, 1) m hbase)
  have hneg :
      iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (fun q =>
              -iterDirectional (0, 1) 2 fundamental q)) p =
        -iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (0, 1) 2 fundamental)) p := by
    rw [iterDirectional_neg, iterDirectional_neg]
  have hrel0 :
      iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (1, 0) 2 fundamental)) p =
        -iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (0, 1) 2 fundamental)) p :=
    hlift.self_of_nhds.trans hneg
  have hcomm :
      iterDirectional (0, 1) m
          (iterDirectional (1, 0) 2 fundamental) =ᶠ[nhds p]
        iterDirectional (1, 0) 2
          (iterDirectional (0, 1) m fundamental) :=
    eventuallyEq_iterDirectional_blocks_comm
      (0, 1) (1, 0) m 2 fundamental p
        (hsmooth.of_le le_top)
  have hleft :
      iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (1, 0) 2 fundamental)) p =
        iterDirectional (1, 0) (n + 2)
          (iterDirectional (0, 1) m fundamental) p := by
    calc
      iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (1, 0) 2 fundamental)) p =
        iterDirectional (1, 0) n
          (iterDirectional (1, 0) 2
            (iterDirectional (0, 1) m fundamental)) p :=
          (eventuallyEq_iterDirectional (1, 0) n hcomm).self_of_nhds
      _ = iterDirectional (1, 0) (n + 2)
          (iterDirectional (0, 1) m fundamental) p := by
        rfl
  have hright :
      iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (0, 1) 2 fundamental)) p =
        iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 2) fundamental) p := by
    rfl
  have hrep1 :
      mixedDerivative fundamental (n + 2) m p =
        iterDirectional (1, 0) (n + 2)
          (iterDirectional (0, 1) m fundamental) p := by
    calc
      mixedDerivative fundamental (n + 2) m p =
          orderedMixed (n + 2) m
            (fun x y => fundamental (x, y)) p.1 p.2 :=
        mixedDerivative_eq_orderedMixed_at
          (n + 2) m fundamental p (hsmooth.of_le le_top)
      _ = iterDirectional (1, 0) (n + 2)
          (iterDirectional (0, 1) m fundamental) p := by
        simpa using
          orderedMixed_eq_iterDirectional_at
            (n + 2) m (fun x y => fundamental (x, y))
            p.1 p.2 (hsmooth.of_le le_top)
  have hrep2 :
      mixedDerivative fundamental n (m + 2) p =
        iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 2) fundamental) p := by
    calc
      mixedDerivative fundamental n (m + 2) p =
          orderedMixed n (m + 2)
            (fun x y => fundamental (x, y)) p.1 p.2 :=
        mixedDerivative_eq_orderedMixed_at
          n (m + 2) fundamental p (hsmooth.of_le le_top)
      _ = iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 2) fundamental) p := by
        simpa using
          orderedMixed_eq_iterDirectional_at
            n (m + 2) (fun x y => fundamental (x, y))
            p.1 p.2 (hsmooth.of_le le_top)
  have hrel :
      mixedDerivative fundamental (n + 2) m p =
        -mixedDerivative fundamental n (m + 2) p := by
    calc
      mixedDerivative fundamental (n + 2) m p =
          iterDirectional (1, 0) (n + 2)
            (iterDirectional (0, 1) m fundamental) p := hrep1
      _ = iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (1, 0) 2 fundamental)) p :=
        hleft.symm
      _ = -iterDirectional (1, 0) n
          (iterDirectional (0, 1) m
            (iterDirectional (0, 1) 2 fundamental)) p := hrel0
      _ = -iterDirectional (1, 0) n
          (iterDirectional (0, 1) (m + 2) fundamental) p :=
        congrArg Neg.neg hright
      _ = -mixedDerivative fundamental n (m + 2) p :=
        congrArg Neg.neg hrep2.symm
  linarith

theorem gap1 (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun x => fundamental (x, p.2))
      (-p.1 / radius p ^ 2) p.1 := by
  exact fundamental_hasDerivAt_x p hp

theorem gap2 (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun y => fundamental (p.1, y))
      (-p.2 / radius p ^ 2) p.2 := by
  exact fundamental_hasDerivAt_y p hp

theorem gap3 (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun x => partialX fundamental (x, p.2))
      (-(radius p ^ 2 - 2 * p.1 ^ 2) / radius p ^ 4) p.1 := by
  exact fundamental_second_x p hp

theorem gap4 (p : Point) (hp : p ≠ (0, 0)) :
    HasDerivAt (fun y => partialY fundamental (p.1, y))
      (-(radius p ^ 2 - 2 * p.2 ^ 2) / radius p ^ 4) p.2 := by
  exact fundamental_second_y p hp

theorem gap5 (p : Point) (hp : p ≠ (0, 0)) :
    laplacian p = 0 := by
  exact laplacian_zero p hp

theorem gap6 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hp : p ≠ (0, 0)) :
    curlDefect n m p = mixedDerivative laplacian n m p := by
  calc
    curlDefect n m p =
        mixedDerivative fundamental (n + 2) m p +
          mixedDerivative fundamental n (m + 2) p :=
      curlDefect_eq_mixed_sum n m hn hm p hp
    _ = 0 := mixed_fundamental_sum_zero n m p hp
    _ = mixedDerivative laplacian n m p :=
      (mixed_laplacian_zero n m p hp).symm

theorem gap7 (n m : ℕ) (p : Point) (hp : p ≠ (0, 0)) :
    mixedDerivative laplacian n m p = 0 := by
  exact mixed_laplacian_zero n m p hp

theorem gap8 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : Point) (hp : p ≠ (0, 0)) :
    curlDefect n m p = 0 := by
  calc
    curlDefect n m p =
        mixedDerivative fundamental (n + 2) m p +
          mixedDerivative fundamental n (m + 2) p :=
      curlDefect_eq_mixed_sum n m hn hm p hp
    _ = 0 := mixed_fundamental_sum_zero n m p hp

theorem gap9 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p v : Point) (hp : p.2 ≠ 0) :
    coordinateDifferential (derivedField n m p) v =
      differential (derivedPotential n m) p v := by
  have hgrad := derivedPotential_gradient n m hn hm p hp
  unfold coordinateDifferential differential partialX partialY
  rw [hgrad.1.deriv, hgrad.2.deriv]

theorem gap10 (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsUpperSolution z n m ↔
      ∃ C : ℝ, ∀ p, 0 < p.2 →
        z p = constructedUpper n m p + C := by
  constructor
  · intro hz
    rcases (upper_solution_iff_potential z n m hn hm).1 hz with
      ⟨C, hC⟩
    refine
      ⟨C + derivedPotential n m (0, 1), ?_⟩
    intro p hp
    rw [hC p hp,
      constructedUpper_eq_potential_sub n m hn hm p hp]
    ring
  · rintro ⟨C, hC⟩
    apply (upper_solution_iff_potential z n m hn hm).2
    refine
      ⟨C - derivedPotential n m (0, 1), ?_⟩
    intro p hp
    rw [hC p hp,
      constructedUpper_eq_potential_sub n m hn hm p hp]
    ring

theorem gap11 (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsUpperSolution z n m ↔
      ∃ C₁ : ℝ, ∀ p, 0 < p.2 →
        z p = derivedPotential n m p + C₁ := by
  exact upper_solution_iff_potential z n m hn hm

theorem gap12 (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsLowerSolution z n m ↔
      ∃ C : ℝ, ∀ p, p.2 < 0 →
        z p = constructedLower n m p + C := by
  constructor
  · intro hz
    rcases (lower_solution_iff_potential z n m hn hm).1 hz with
      ⟨C, hC⟩
    refine
      ⟨C + derivedPotential n m (0, -1), ?_⟩
    intro p hp
    rw [hC p hp,
      constructedLower_eq_potential_sub n m hn hm p hp]
    ring
  · rintro ⟨C, hC⟩
    apply (lower_solution_iff_potential z n m hn hm).2
    refine
      ⟨C - derivedPotential n m (0, -1), ?_⟩
    intro p hp
    rw [hC p hp,
      constructedLower_eq_potential_sub n m hn hm p hp]
    ring

theorem gap13 (z : Point → ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsLowerSolution z n m ↔
      ∃ C₂ : ℝ, ∀ p, p.2 < 0 →
        z p = derivedPotential n m p + C₂ := by
  exact lower_solution_iff_potential z n m hn hm

theorem gap14 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (C₁ C₂ : ℝ) :
    IsUpperSolution (splitPotential n m C₁ C₂) n m ∧
      IsLowerSolution (splitPotential n m C₁ C₂) n m := by
  constructor
  · apply
      (upper_solution_iff_potential
        (splitPotential n m C₁ C₂) n m hn hm).2
    refine ⟨C₁, ?_⟩
    intro p hp
    simp [splitPotential, hp]
  · apply
      (lower_solution_iff_potential
        (splitPotential n m C₁ C₂) n m hn hm).2
    refine ⟨C₂, ?_⟩
    intro p hp
    have hnot : ¬ 0 < p.2 := not_lt_of_ge (le_of_lt hp)
    simp [splitPotential, hnot]

end

end ProofGap.Exercise4276
