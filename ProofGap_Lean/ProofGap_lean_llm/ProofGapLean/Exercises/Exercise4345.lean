import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4345

noncomputable section

open scoped Interval Topology

abbrev Point3 := ℝ × (ℝ × ℝ)

def tetrahedron : Set Point3 :=
  {p |
    p.1 + p.2.1 + p.2.2 ≤ 1 ∧
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}

def slantedFace : Set Point3 :=
  {p |
    p.1 + p.2.1 + p.2.2 = 1 ∧
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}

def xFace : Set Point3 :=
  {p |
    p.1 = 0 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
      p.2.1 + p.2.2 ≤ 1}

def yFace : Set Point3 :=
  {p |
    p.2.1 = 0 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧
      p.1 + p.2.2 ≤ 1}

def zFace : Set Point3 :=
  {p |
    p.2.2 = 0 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧
      p.1 + p.2.1 ≤ 1}

def triangularIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..1 - x,
      1 / (1 + x + y) ^ 2

def coordinateFaceIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ z in (0 : ℝ)..1 - x,
      1 / (1 + x) ^ 2

def boundaryMoment : ℝ :=
  Real.sqrt 3 * triangularIntegral +
    coordinateFaceIntegral + coordinateFaceIntegral + triangularIntegral

private theorem triangularIntegral_eval :
    triangularIntegral = Real.log 2 - 1 / 2 := by
  unfold triangularIntegral
  have hinner : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (∫ y in (0 : ℝ)..1 - x, 1 / (1 + x + y) ^ 2) =
        1 / (1 + x) - 1 / 2 := by
    intro x hx
    have hx' : 0 ≤ x ∧ x ≤ 1 := by
      simpa [Set.mem_uIcc] using hx
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) (1 - x),
        HasDerivAt (fun t : ℝ => -1 / (1 + x + t))
          (1 / (1 + x + y) ^ 2) y := by
      intro y hy
      have hy' : 0 ≤ y ∧ y ≤ 1 - x := by
        rw [Set.uIcc_of_le (by linarith)] at hy
        simpa only [Set.mem_Icc] using hy
      have hden : 1 + x + y ≠ 0 := by linarith
      convert
        (hasDerivAt_const y (-1 : ℝ)).div
          ((hasDerivAt_const y (1 + x)).add (hasDerivAt_id y)) hden using 1 <;>
        simp only [Pi.add_apply, id_eq] <;>
        field_simp [hden] <;>
        ring_nf
    have hint : IntervalIntegrable
        (fun y : ℝ => 1 / (1 + x + y) ^ 2) MeasureTheory.volume 0 (1 - x) := by
      apply ContinuousOn.intervalIntegrable
      intro y hy
      have hy' : 0 ≤ y ∧ y ≤ 1 - x := by
        rw [Set.uIcc_of_le (by linarith)] at hy
        simpa only [Set.mem_Icc] using hy
      have hden : 1 + x + y ≠ 0 := by linarith
      exact
        (continuousAt_const.div
          ((continuousAt_const.add continuousAt_id).pow 2)
          (pow_ne_zero 2 hden)).continuousWithinAt
    calc
      (∫ y in (0 : ℝ)..1 - x, 1 / (1 + x + y) ^ 2) =
          (-1 / (1 + x + (1 - x))) - (-1 / (1 + x + 0)) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      _ = 1 / (1 + x) - 1 / 2 := by
        have hden : 1 + x ≠ 0 := by linarith
        field_simp [hden]
        <;> ring_nf
  calc
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1 - x, 1 / (1 + x + y) ^ 2) =
        ∫ x in (0 : ℝ)..1, (1 / (1 + x) - 1 / 2) := by
      apply intervalIntegral.integral_congr
      exact hinner
    _ = Real.log 2 - 1 / 2 := by
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => Real.log (1 + t) - t / 2)
            (1 / (1 + x) - 1 / 2) x := by
        intro x hx
        have hx' : 0 ≤ x ∧ x ≤ 1 := by
          simpa [Set.mem_uIcc] using hx
        have hden : 1 + x ≠ 0 := by linarith
        convert
          ((Real.hasDerivAt_log hden).comp x
            ((hasDerivAt_const x 1).add (hasDerivAt_id x))).sub
              ((hasDerivAt_id x).div_const 2) using 1 <;>
          (try simp only [Pi.add_apply, id_eq]) <;>
          (try field_simp [hden]) <;>
          ring_nf
      have hint : IntervalIntegrable
          (fun x : ℝ => 1 / (1 + x) - 1 / 2) MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        intro x hx
        have hx' : 0 ≤ x ∧ x ≤ 1 := by
          simpa [Set.mem_uIcc] using hx
        have hden : 1 + x ≠ 0 := by linarith
        exact
          ((continuousAt_const.div (continuousAt_const.add continuousAt_id) hden).sub
            continuousAt_const).continuousWithinAt
      calc
        (∫ x in (0 : ℝ)..1, (1 / (1 + x) - 1 / 2)) =
            (Real.log (1 + 1) - 1 / 2) -
              (Real.log (1 + 0) - 0 / 2) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
        _ = Real.log 2 - 1 / 2 := by norm_num

private theorem coordinateFaceIntegral_eval :
    coordinateFaceIntegral = 1 - Real.log 2 := by
  unfold coordinateFaceIntegral
  have hinner : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (∫ z in (0 : ℝ)..1 - x, 1 / (1 + x) ^ 2) =
        (1 - x) / (1 + x) ^ 2 := by
    intro x hx
    simp [div_eq_mul_inv]
    <;> ring_nf
  calc
    (∫ x in (0 : ℝ)..1,
      ∫ z in (0 : ℝ)..1 - x, 1 / (1 + x) ^ 2) =
        ∫ x in (0 : ℝ)..1, (1 - x) / (1 + x) ^ 2 := by
      apply intervalIntegral.integral_congr
      exact hinner
    _ = 1 - Real.log 2 := by
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => -2 / (1 + t) - Real.log (1 + t))
            ((1 - x) / (1 + x) ^ 2) x := by
        intro x hx
        have hx' : 0 ≤ x ∧ x ≤ 1 := by
          simpa [Set.mem_uIcc] using hx
        have hden : 1 + x ≠ 0 := by linarith
        convert
          ((hasDerivAt_const x (-2 : ℝ)).div
            ((hasDerivAt_const x 1).add (hasDerivAt_id x)) hden).sub
              ((Real.hasDerivAt_log hden).comp x
                ((hasDerivAt_const x 1).add (hasDerivAt_id x))) using 1 <;>
          simp only [Pi.add_apply, id_eq] <;>
          field_simp [hden] <;>
          ring_nf
      have hint : IntervalIntegrable
          (fun x : ℝ => (1 - x) / (1 + x) ^ 2) MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        intro x hx
        have hx' : 0 ≤ x ∧ x ≤ 1 := by
          simpa [Set.mem_uIcc] using hx
        have hden : (1 + x) ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 (by linarith)
        exact
          ((continuousAt_const.sub continuousAt_id).div
            ((continuousAt_const.add continuousAt_id).pow 2) hden).continuousWithinAt
      calc
        (∫ x in (0 : ℝ)..1, (1 - x) / (1 + x) ^ 2) =
            (-2 / (1 + 1) - Real.log (1 + 1)) -
              (-2 / (1 + 0) - Real.log (1 + 0)) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
        _ = 1 - Real.log 2 := by
          norm_num
          ring

theorem gap1 :
    frontier tetrahedron =
      slantedFace ∪ xFace ∪ yFace ∪ zFace := by
  ext p
  have cx : Continuous (fun q : Point3 => q.1) := continuous_fst
  have cy : Continuous (fun q : Point3 => q.2.1) :=
    continuous_fst.comp continuous_snd
  have cz : Continuous (fun q : Point3 => q.2.2) :=
    continuous_snd.comp continuous_snd
  have csum : Continuous (fun q : Point3 => q.1 + q.2.1 + q.2.2) :=
    (cx.add cy).add cz
  have hclosed : IsClosed tetrahedron := by
    change IsClosed
      ({q : Point3 | q.1 + q.2.1 + q.2.2 ≤ 1} ∩
        ({q : Point3 | 0 ≤ q.1} ∩
          ({q : Point3 | 0 ≤ q.2.1} ∩ {q : Point3 | 0 ≤ q.2.2})))
    exact
      (isClosed_le csum continuous_const).inter
        ((isClosed_le continuous_const cx).inter
          ((isClosed_le continuous_const cy).inter
            (isClosed_le continuous_const cz)))
  have hopen : IsOpen
      {q : Point3 |
        q.1 + q.2.1 + q.2.2 < 1 ∧
          0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2} := by
    change IsOpen
      ({q : Point3 | q.1 + q.2.1 + q.2.2 < 1} ∩
        ({q : Point3 | 0 < q.1} ∩
          ({q : Point3 | 0 < q.2.1} ∩ {q : Point3 | 0 < q.2.2})))
    exact
      (isOpen_lt csum continuous_const).inter
        ((isOpen_lt continuous_const cx).inter
          ((isOpen_lt continuous_const cy).inter
            (isOpen_lt continuous_const cz)))
  have notInt_sum (q : Point3)
      (hq : q.1 + q.2.1 + q.2.2 = 1) : q ∉ interior tetrahedron := by
    intro hi
    rcases Metric.isOpen_iff.mp isOpen_interior q hi with ⟨ε, hε, hball⟩
    let r : Point3 := (q.1 + ε / 2, q.2)
    have hehalf : 0 ≤ ε / 2 := by linarith
    have hcoord : dist (q.1 + ε / 2) q.1 = ε / 2 := by
      rw [Real.dist_eq]
      have hd : q.1 + ε / 2 - q.1 = ε / 2 := by ring
      rw [hd, abs_of_nonneg hehalf]
    have hrball : r ∈ Metric.ball q ε := by
      rw [Metric.mem_ball]
      calc
        dist r q = ε / 2 := by
          dsimp [r]
          simp only [Prod.dist_eq]
          rw [hcoord]
          simp [hehalf]
        _ < ε := by linarith
    have hrt : r ∈ tetrahedron := interior_subset (hball hrball)
    change
      r.1 + r.2.1 + r.2.2 ≤ 1 ∧
        0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 at hrt
    have hsumr : r.1 + r.2.1 + r.2.2 = 1 + ε / 2 := by
      dsimp [r]
      linarith
    have hle := hrt.1
    rw [hsumr] at hle
    linarith
  have notInt_x (q : Point3) (hq : q.1 = 0) : q ∉ interior tetrahedron := by
    intro hi
    rcases Metric.isOpen_iff.mp isOpen_interior q hi with ⟨ε, hε, hball⟩
    let r : Point3 := (q.1 - ε / 2, q.2)
    have hehalf : 0 ≤ ε / 2 := by linarith
    have hcoord : dist (q.1 - ε / 2) q.1 = ε / 2 := by
      rw [Real.dist_eq]
      have hd : q.1 - ε / 2 - q.1 = -(ε / 2) := by ring
      rw [hd, abs_neg, abs_of_nonneg hehalf]
    have hrball : r ∈ Metric.ball q ε := by
      rw [Metric.mem_ball]
      calc
        dist r q = ε / 2 := by
          dsimp [r]
          simp only [Prod.dist_eq]
          rw [hcoord]
          simp [hehalf]
        _ < ε := by linarith
    have hrt : r ∈ tetrahedron := interior_subset (hball hrball)
    change
      r.1 + r.2.1 + r.2.2 ≤ 1 ∧
        0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 at hrt
    have hxr : r.1 = -ε / 2 := by
      dsimp [r]
      linarith
    have hxnonneg := hrt.2.1
    rw [hxr] at hxnonneg
    linarith
  have notInt_y (q : Point3) (hq : q.2.1 = 0) : q ∉ interior tetrahedron := by
    intro hi
    rcases Metric.isOpen_iff.mp isOpen_interior q hi with ⟨ε, hε, hball⟩
    let r : Point3 := (q.1, (q.2.1 - ε / 2, q.2.2))
    have hehalf : 0 ≤ ε / 2 := by linarith
    have hcoord : dist (q.2.1 - ε / 2) q.2.1 = ε / 2 := by
      rw [Real.dist_eq]
      have hd : q.2.1 - ε / 2 - q.2.1 = -(ε / 2) := by ring
      rw [hd, abs_neg, abs_of_nonneg hehalf]
    have hrball : r ∈ Metric.ball q ε := by
      rw [Metric.mem_ball]
      calc
        dist r q = ε / 2 := by
          dsimp [r]
          simp only [Prod.dist_eq]
          rw [hcoord]
          simp [hehalf]
        _ < ε := by linarith
    have hrt : r ∈ tetrahedron := interior_subset (hball hrball)
    change
      r.1 + r.2.1 + r.2.2 ≤ 1 ∧
        0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 at hrt
    have hyr : r.2.1 = -ε / 2 := by
      dsimp [r]
      linarith
    have hynonneg := hrt.2.2.1
    rw [hyr] at hynonneg
    linarith
  have notInt_z (q : Point3) (hq : q.2.2 = 0) : q ∉ interior tetrahedron := by
    intro hi
    rcases Metric.isOpen_iff.mp isOpen_interior q hi with ⟨ε, hε, hball⟩
    let r : Point3 := (q.1, (q.2.1, q.2.2 - ε / 2))
    have hehalf : 0 ≤ ε / 2 := by linarith
    have hcoord : dist (q.2.2 - ε / 2) q.2.2 = ε / 2 := by
      rw [Real.dist_eq]
      have hd : q.2.2 - ε / 2 - q.2.2 = -(ε / 2) := by ring
      rw [hd, abs_neg, abs_of_nonneg hehalf]
    have hrball : r ∈ Metric.ball q ε := by
      rw [Metric.mem_ball]
      calc
        dist r q = ε / 2 := by
          dsimp [r]
          simp only [Prod.dist_eq]
          rw [hcoord]
          simp [hehalf]
        _ < ε := by linarith
    have hrt : r ∈ tetrahedron := interior_subset (hball hrball)
    change
      r.1 + r.2.1 + r.2.2 ≤ 1 ∧
        0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 at hrt
    have hzr : r.2.2 = -ε / 2 := by
      dsimp [r]
      linarith
    have hznonneg := hrt.2.2.2
    rw [hzr] at hznonneg
    linarith
  simp only [Set.mem_union, slantedFace, xFace, yFace, zFace,
    Set.mem_setOf_eq]
  constructor
  · intro hp
    have hp' : p ∈ closure tetrahedron ∧ p ∉ interior tetrahedron := by
      simpa [frontier] using hp
    have ht : p ∈ tetrahedron := by
      rw [hclosed.closure_eq] at hp'
      exact hp'.1
    change
      p.1 + p.2.1 + p.2.2 ≤ 1 ∧
        0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 at ht
    rcases ht with ⟨hsum, hx, hy, hz⟩
    by_cases hs : p.1 + p.2.1 + p.2.2 = 1
    · exact Or.inl (Or.inl (Or.inl ⟨hs, hx, hy, hz⟩))
    by_cases hxeq : p.1 = 0
    · exact Or.inl (Or.inl (Or.inr ⟨hxeq, hy, hz, by linarith⟩))
    by_cases hyeq : p.2.1 = 0
    · exact Or.inl (Or.inr ⟨hyeq, hx, hz, by linarith⟩)
    by_cases hzeq : p.2.2 = 0
    · exact Or.inr ⟨hzeq, hx, hy, by linarith⟩
    exfalso
    apply hp'.2
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset
      (hopen.mem_nhds
        ⟨lt_of_le_of_ne hsum hs,
          lt_of_le_of_ne hx (Ne.symm hxeq),
          lt_of_le_of_ne hy (Ne.symm hyeq),
          lt_of_le_of_ne hz (Ne.symm hzeq)⟩)
    intro q hq
    exact ⟨le_of_lt hq.1, le_of_lt hq.2.1,
      le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
  · intro hp
    rcases hp with hp | hz
    · rcases hp with hp | hy
      · rcases hp with hs | hx
        · have ht : p ∈ tetrahedron := by
            exact ⟨le_of_eq hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
          have hc : p ∈ closure tetrahedron := by
            rw [hclosed.closure_eq]
            exact ht
          simpa [frontier] using And.intro hc (notInt_sum p hs.1)
        · have ht : p ∈ tetrahedron := by
            exact ⟨by linarith [hx.2.2.2], by linarith [hx.1],
              hx.2.1, hx.2.2.1⟩
          have hc : p ∈ closure tetrahedron := by
            rw [hclosed.closure_eq]
            exact ht
          simpa [frontier] using And.intro hc (notInt_x p hx.1)
      · have ht : p ∈ tetrahedron := by
          exact ⟨by linarith [hy.2.2.2], hy.2.1,
            by linarith [hy.1], hy.2.2.1⟩
        have hc : p ∈ closure tetrahedron := by
          rw [hclosed.closure_eq]
          exact ht
        simpa [frontier] using And.intro hc (notInt_y p hy.1)
    · have ht : p ∈ tetrahedron := by
        exact ⟨by linarith [hz.2.2.2], hz.2.1, hz.2.2.1,
          by linarith [hz.1]⟩
      have hc : p ∈ closure tetrahedron := by
        rw [hclosed.closure_eq]
        exact ht
      simpa [frontier] using And.intro hc (notInt_z p hz.1)

theorem gap2 :
    boundaryMoment =
      Real.sqrt 3 *
          (∫ x in (0 : ℝ)..1,
            ∫ y in (0 : ℝ)..1 - x,
              1 / (1 + x + y) ^ 2) +
        (∫ y in (0 : ℝ)..1,
          ∫ z in (0 : ℝ)..1 - y,
            1 / (1 + y) ^ 2) +
        (∫ x in (0 : ℝ)..1,
          ∫ z in (0 : ℝ)..1 - x,
            1 / (1 + x) ^ 2) +
        (∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x,
            1 / (1 + x + y) ^ 2) := by
  rfl

theorem gap3 :
    boundaryMoment =
      (Real.sqrt 3 + 1) * triangularIntegral +
        2 * coordinateFaceIntegral := by
  unfold boundaryMoment
  ring

theorem gap4 :
    boundaryMoment =
      (Real.sqrt 3 + 1) * (Real.log 2 - 1 / 2) +
        2 * (1 - Real.log 2) := by
  calc
    boundaryMoment =
        (Real.sqrt 3 + 1) * triangularIntegral +
          2 * coordinateFaceIntegral := gap3
    _ = (Real.sqrt 3 + 1) * (Real.log 2 - 1 / 2) +
          2 * (1 - Real.log 2) := by
      rw [triangularIntegral_eval, coordinateFaceIntegral_eval]

theorem gap5 :
    (Real.sqrt 3 + 1) * (Real.log 2 - 1 / 2) +
        2 * (1 - Real.log 2) =
      (3 - Real.sqrt 3) / 2 +
        (Real.sqrt 3 - 1) * Real.log 2 := by
  ring

theorem gap6 :
    boundaryMoment =
      (3 - Real.sqrt 3) / 2 +
        (Real.sqrt 3 - 1) * Real.log 2 := by
  calc
    boundaryMoment =
        (Real.sqrt 3 + 1) * (Real.log 2 - 1 / 2) +
          2 * (1 - Real.log 2) := gap4
    _ = (3 - Real.sqrt 3) / 2 +
          (Real.sqrt 3 - 1) * Real.log 2 := gap5

end

end ProofGap.Exercise4345
