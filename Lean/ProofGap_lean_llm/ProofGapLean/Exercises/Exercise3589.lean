import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor

namespace ProofGap.Exercise3589

noncomputable section

abbrev Point2 := ℝ × ℝ

def iterX (n : ℕ) (f : Point2 → ℝ) (p : Point2) : ℝ :=
  (deriv^[n]) (fun t => f (t, p.2)) p.1

def iterY (n : ℕ) (f : Point2 → ℝ) (p : Point2) : ℝ :=
  (deriv^[n]) (fun t => f (p.1, t)) p.2

def fourNeighborDifference (f : Point2 → ℝ) (p : Point2) (h : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
      (f (p.1 + h, p.2) + f (p.1, p.2 + h) +
        f (p.1 - h, p.2) + f (p.1, p.2 - h)) -
    f p

def regroupedDifference (f : Point2 → ℝ) (p : Point2) (h : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    ((f (p.1 + h, p.2) - f p) + (f (p.1, p.2 + h) - f p) +
      (f (p.1 - h, p.2) - f p) + (f (p.1, p.2 - h) - f p))

def rawTaylor4 (f : Point2 → ℝ) (p : Point2) (h : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (h * iterX 1 f p + (1 / 2 : ℝ) * h ^ 2 * iterX 2 f p +
      (1 / 6 : ℝ) * h ^ 3 * iterX 3 f p +
      (1 / 24 : ℝ) * h ^ 4 * iterX 4 f p +
      h * iterY 1 f p + (1 / 2 : ℝ) * h ^ 2 * iterY 2 f p +
      (1 / 6 : ℝ) * h ^ 3 * iterY 3 f p +
      (1 / 24 : ℝ) * h ^ 4 * iterY 4 f p +
      (-h) * iterX 1 f p + (1 / 2 : ℝ) * h ^ 2 * iterX 2 f p -
      (1 / 6 : ℝ) * h ^ 3 * iterX 3 f p +
      (1 / 24 : ℝ) * h ^ 4 * iterX 4 f p +
      (-h) * iterY 1 f p + (1 / 2 : ℝ) * h ^ 2 * iterY 2 f p -
      (1 / 6 : ℝ) * h ^ 3 * iterY 3 f p +
      (1 / 24 : ℝ) * h ^ 4 * iterY 4 f p)

def evenTaylor4 (f : Point2 → ℝ) (p : Point2) (h : ℝ) : ℝ :=
  h ^ 2 / 4 * (iterX 2 f p + iterY 2 f p) +
    h ^ 4 / 48 * (iterX 4 f p + iterY 4 f p)

private theorem taylor4_add_isLittleO (g : ℝ → ℝ) (x : ℝ)
    (hg : ContDiff ℝ 5 g) :
    Asymptotics.IsLittleO (nhds 0)
      (fun h => g (x + h) - taylorWithinEval g 4 Set.univ x (x + h))
      (fun h : ℝ => h ^ 4) := by
  have ht := taylor_isLittleO_univ (x₀ := x) (n := 4)
    (hg.of_le (by norm_num))
  have hlim : Filter.Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
    convert
      (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : ℝ => x + h) 0).tendsto using 1 <;> simp
  have hc := ht.comp_tendsto hlim
  convert hc using 1 <;> ext h <;> simp only [Function.comp_apply] <;> ring

private theorem taylor4_sub_isLittleO (g : ℝ → ℝ) (x : ℝ)
    (hg : ContDiff ℝ 5 g) :
    Asymptotics.IsLittleO (nhds 0)
      (fun h => g (x - h) - taylorWithinEval g 4 Set.univ x (x - h))
      (fun h : ℝ => h ^ 4) := by
  have ht := taylor_isLittleO_univ (x₀ := x) (n := 4)
    (hg.of_le (by norm_num))
  have hlim : Filter.Tendsto (fun h : ℝ => x - h) (nhds 0) (nhds x) := by
    convert
      (continuousAt_const.sub continuousAt_id :
        ContinuousAt (fun h : ℝ => x - h) 0).tendsto using 1 <;> simp
  have hc := ht.comp_tendsto hlim
  convert hc using 1 <;> ext h <;> simp only [Function.comp_apply] <;> ring

theorem gap1 (f : Point2 → ℝ) :
    ∀ p h, fourNeighborDifference f p h = regroupedDifference f p h := by
  intro p h
  simp only [fourNeighborDifference, regroupedDifference]
  ring

theorem gap2 (f : Point2 → ℝ) (p : Point2)
    (hf : ContDiff ℝ 5 f) :
    Asymptotics.IsLittleO (nhds 0)
      (fun h => fourNeighborDifference f p h - rawTaylor4 f p h)
      (fun h : ℝ => h ^ 4) := by
  have hfx : ContDiff ℝ 5 (fun t : ℝ => f (t, p.2)) :=
    hf.fun_comp (contDiff_id.prodMk contDiff_const)
  have hfy : ContDiff ℝ 5 (fun t : ℝ => f (p.1, t)) :=
    hf.fun_comp (contDiff_const.prodMk contDiff_id)
  have hxp := taylor4_add_isLittleO (fun t : ℝ => f (t, p.2)) p.1 hfx
  have hyp := taylor4_add_isLittleO (fun t : ℝ => f (p.1, t)) p.2 hfy
  have hxm := taylor4_sub_isLittleO (fun t : ℝ => f (t, p.2)) p.1 hfx
  have hym := taylor4_sub_isLittleO (fun t : ℝ => f (p.1, t)) p.2 hfy
  have hsum := (((hxp.add hyp).add hxm).add hym).const_mul_left (1 / 4 : ℝ)
  convert hsum using 1
  funext h
  simp [fourNeighborDifference, rawTaylor4, iterX, iterY,
    sub_eq_add_neg]
  norm_num [Nat.factorial, iteratedDeriv_eq_iterate]
  ring

theorem gap3 (f : Point2 → ℝ) (p : Point2)
    (hf : ContDiff ℝ 5 f) :
    Asymptotics.IsLittleO (nhds 0)
      (fun h => fourNeighborDifference f p h - evenTaylor4 f p h)
      (fun h : ℝ => h ^ 4) := by
  have hraw : ∀ h, rawTaylor4 f p h = evenTaylor4 f p h := by
    intro h
    simp only [rawTaylor4, evenTaylor4]
    ring
  simpa only [hraw] using gap2 f p hf

end

end ProofGap.Exercise3589
