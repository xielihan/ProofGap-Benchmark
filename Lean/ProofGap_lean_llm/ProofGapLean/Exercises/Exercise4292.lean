import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4292

noncomputable section

abbrev Point3 := ℝ × ℝ × ℝ

def s (p : Point3) : ℝ :=
  p.1 + p.2.1

def denominator (p : Point3) : ℝ :=
  s p ^ 2 + p.2.2 ^ 2

def field (p : Point3) : Point3 :=
  ((s p - p.2.2) / denominator p,
    (s p - p.2.2) / denominator p,
    (s p + p.2.2) / denominator p)

def InPositiveChart (p : Point3) : Prop :=
  0 < s p

def potential (p : Point3) : ℝ :=
  Real.log (Real.sqrt (denominator p)) +
    Real.arctan (p.2.2 / s p)

def coordinateDifferential (V v : Point3) : ℝ :=
  V.1 * v.1 + V.2.1 * v.2.1 + V.2.2 * v.2.2

def differential (F : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv (fun x => F (x, p.2.1, p.2.2)) p.1 * v.1 +
    deriv (fun y => F (p.1, y, p.2.2)) p.2.1 * v.2.1 +
      deriv (fun z => F (p.1, p.2.1, z)) p.2.2 * v.2.2

def rawNumerator (p v : Point3) : ℝ :=
  (s p - p.2.2) * v.1 + (s p - p.2.2) * v.2.1 +
    (s p + p.2.2) * v.2.2

def expandedNumerator (p v : Point3) : ℝ :=
  p.1 * v.1 + p.2.1 * v.2.1 + p.2.1 * v.1 + p.1 * v.2.1 +
    s p * v.2.2 - p.2.2 * (v.1 + v.2.1) + p.2.2 * v.2.2

def structuredNumerator (p v : Point3) : ℝ :=
  (1 / 2 : ℝ) *
      (2 * s p * (v.1 + v.2.1) + 2 * p.2.2 * v.2.2) +
    s p * v.2.2 - p.2.2 * (v.1 + v.2.1)

def HasCoordinateGradientAt
    (F : Point3 → ℝ) (V : Point3) (p : Point3) : Prop :=
  HasDerivAt (fun x => F (x, p.2.1, p.2.2)) V.1 p.1 ∧
    HasDerivAt (fun y => F (p.1, y, p.2.2)) V.2.1 p.2.1 ∧
      HasDerivAt (fun z => F (p.1, p.2.1, z)) V.2.2 p.2.2

def IsSolution (u : Point3 → ℝ) : Prop :=
  ∀ p, InPositiveChart p → HasCoordinateGradientAt u (field p) p

private theorem potential_hasDerivAt_first
    (a z : ℝ) (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + z ^ 2)) +
        Real.arctan (z / t))
      ((a - z) / (a ^ 2 + z ^ 2)) a := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hD : 0 < a ^ 2 + z ^ 2 := by
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    nlinarith [sq_nonneg z]
  have hD0 : a ^ 2 + z ^ 2 ≠ 0 := ne_of_gt hD
  have hsqrt0 : Real.sqrt (a ^ 2 + z ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hD)
  have hatden : 0 < 1 + (z / a) ^ 2 := by
    nlinarith [sq_nonneg (z / a)]
  have hpoly := ((hasDerivAt_id a).pow 2).add_const (z ^ 2)
  have hroot := (Real.hasDerivAt_sqrt hD0).comp a hpoly
  have hlog := (Real.hasDerivAt_log hsqrt0).comp a hroot
  have hquot := (hasDerivAt_const a z).div (hasDerivAt_id a) ha0
  have hatan := (Real.hasDerivAt_arctan (z / a)).comp a hquot
  have hcoeff :
      (Real.sqrt (a ^ 2 + z ^ 2))⁻¹ *
          (1 / (2 * Real.sqrt (a ^ 2 + z ^ 2)) * (2 * a)) +
        1 / (1 + (z / a) ^ 2) * (-z / a ^ 2) =
          (a - z) / (a ^ 2 + z ^ 2) := by
    field_simp [ha0, hD0, hsqrt0, ne_of_gt hatden]
    rw [Real.sq_sqrt (le_of_lt hD)]
    ring
  rw [← hcoeff]
  simpa [Function.comp_def] using hlog.add hatan

private theorem potential_hasDerivAt_third
    (a z : ℝ) (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ => Real.log (Real.sqrt (a ^ 2 + t ^ 2)) +
        Real.arctan (t / a))
      ((a + z) / (a ^ 2 + z ^ 2)) z := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hD : 0 < a ^ 2 + z ^ 2 := by
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    nlinarith [sq_nonneg z]
  have hD0 : a ^ 2 + z ^ 2 ≠ 0 := ne_of_gt hD
  have hsqrt0 : Real.sqrt (a ^ 2 + z ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hD)
  have hatden : 0 < 1 + (z / a) ^ 2 := by
    nlinarith [sq_nonneg (z / a)]
  have hpoly := (hasDerivAt_const z (a ^ 2)).add ((hasDerivAt_id z).pow 2)
  have hroot := (Real.hasDerivAt_sqrt hD0).comp z hpoly
  have hlog := (Real.hasDerivAt_log hsqrt0).comp z hroot
  have hquot := (hasDerivAt_id z).div (hasDerivAt_const z a) ha0
  have hatan := (Real.hasDerivAt_arctan (z / a)).comp z hquot
  have hcoeff :
      (Real.sqrt (a ^ 2 + z ^ 2))⁻¹ *
          (1 / (2 * Real.sqrt (a ^ 2 + z ^ 2)) * (2 * z)) +
        1 / (1 + (z / a) ^ 2) * (a / a ^ 2) =
          (a + z) / (a ^ 2 + z ^ 2) := by
    field_simp [ha0, hD0, hsqrt0, ne_of_gt hatden]
    rw [Real.sq_sqrt (le_of_lt hD)]
    ring
  rw [← hcoeff]
  simpa [Function.comp_def] using hlog.add hatan

private theorem potential_hasCoordinateGradientAt
    (p : Point3) (hp : InPositiveChart p) :
    HasCoordinateGradientAt potential (field p) p := by
  have hs : 0 < s p := hp
  have hxbase : HasDerivAt (fun x : ℝ => x + p.2.1) 1 p.1 := by
    simpa using (hasDerivAt_id p.1).add_const p.2.1
  have hybase : HasDerivAt (fun y : ℝ => p.1 + y) 1 p.2.1 := by
    simpa using (hasDerivAt_const p.2.1 p.1).add (hasDerivAt_id p.2.1)
  have hx := (potential_hasDerivAt_first (s p) p.2.2 hs).comp p.1 hxbase
  have hy := (potential_hasDerivAt_first (s p) p.2.2 hs).comp p.2.1 hybase
  have hz := potential_hasDerivAt_third (s p) p.2.2 hs
  constructor
  · simpa [potential, field, denominator, s, Function.comp_def] using hx
  constructor
  · simpa [potential, field, denominator, s, Function.comp_def] using hy
  · simpa [potential, field, denominator, s, Function.comp_def] using hz

private theorem eq_of_hasDerivAt_zero_on_Ioo
    (f : ℝ → ℝ) (l r x y : ℝ)
    (hx : x ∈ Set.Ioo l r) (hy : y ∈ Set.Ioo l r)
    (hderiv : ∀ z ∈ Set.Ioo l r, HasDerivAt f 0 z) :
    f x = f y := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro z hz
    exact (hderiv z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hderiv z hz).deriv
  · exact hx
  · exact hy

theorem gap1 (p v : Point3) (hp : InPositiveChart p) :
    rawNumerator p v = expandedNumerator p v := by
  unfold rawNumerator expandedNumerator s
  ring

theorem gap2 (p v : Point3) (hp : InPositiveChart p) :
    expandedNumerator p v = structuredNumerator p v := by
  unfold expandedNumerator structuredNumerator s
  ring

theorem gap3 (p v : Point3) (hp : InPositiveChart p) :
    coordinateDifferential (field p) v =
      structuredNumerator p v / denominator p := by
  have hdpos : 0 < denominator p := by
    unfold denominator
    have hspos : 0 < s p := hp
    nlinarith [sq_nonneg (p.2.2), pow_pos hspos 2]
  have hd : denominator p ≠ 0 := ne_of_gt hdpos
  rw [← gap2 p v hp, ← gap1 p v hp]
  unfold coordinateDifferential field rawNumerator
  simp only [Prod.fst, Prod.snd]
  field_simp [hd]

theorem gap4 (p v : Point3) (hp : InPositiveChart p) :
    coordinateDifferential (field p) v = differential potential p v := by
  have hgrad := potential_hasCoordinateGradientAt p hp
  unfold differential
  rw [hgrad.1.deriv, hgrad.2.1.deriv, hgrad.2.2.deriv]
  rfl

theorem gap5 (u : Point3 → ℝ) :
    IsSolution u ↔
      ∃ C : ℝ, ∀ p, InPositiveChart p → u p = potential p + C := by
  constructor
  · intro hu
    have hconst : ∀ p q, InPositiveChart p → InPositiveChart q →
        u p - potential p = u q - potential q := by
      intro p q hp hq
      let R : ℝ :=
        max (max p.1 q.1) (max (-p.2.1) (-q.2.1)) + 1
      have hpR : p.1 < R := by
        dsimp [R]
        linarith [le_max_left p.1 q.1,
          le_max_left (max p.1 q.1) (max (-p.2.1) (-q.2.1))]
      have hqR : q.1 < R := by
        dsimp [R]
        linarith [le_max_right p.1 q.1,
          le_max_left (max p.1 q.1) (max (-p.2.1) (-q.2.1))]
      have hpyR : -p.2.1 < R := by
        dsimp [R]
        linarith [le_max_left (-p.2.1) (-q.2.1),
          le_max_right (max p.1 q.1) (max (-p.2.1) (-q.2.1))]
      have hqyR : -q.2.1 < R := by
        dsimp [R]
        linarith [le_max_right (-p.2.1) (-q.2.1),
          le_max_right (max p.1 q.1) (max (-p.2.1) (-q.2.1))]
      have hxp :
          u p - potential p =
            u (R, p.2.1, p.2.2) - potential (R, p.2.1, p.2.2) := by
        refine eq_of_hasDerivAt_zero_on_Ioo
          (f := fun x => u (x, p.2.1, p.2.2) -
            potential (x, p.2.1, p.2.2))
          (l := -p.2.1) (r := R + 1) (x := p.1) (y := R) ?_ ?_ ?_
        · constructor
          · have hsp : 0 < p.1 + p.2.1 := hp
            linarith
          · linarith
        · constructor <;> linarith
        · intro x hx
          have hc : InPositiveChart (x, p.2.1, p.2.2) := by
            unfold InPositiveChart s
            linarith [hx.1]
          simpa using
            ((hu (x, p.2.1, p.2.2) hc).1.sub
              (potential_hasCoordinateGradientAt (x, p.2.1, p.2.2) hc).1)
      have hyp :
          u (R, p.2.1, p.2.2) - potential (R, p.2.1, p.2.2) =
            u (R, q.2.1, p.2.2) - potential (R, q.2.1, p.2.2) := by
        refine eq_of_hasDerivAt_zero_on_Ioo
          (f := fun y => u (R, y, p.2.2) - potential (R, y, p.2.2))
          (l := -R) (r := max p.2.1 q.2.1 + 1)
          (x := p.2.1) (y := q.2.1) ?_ ?_ ?_
        · constructor
          · linarith
          · linarith [le_max_left p.2.1 q.2.1]
        · constructor
          · linarith
          · linarith [le_max_right p.2.1 q.2.1]
        · intro y hy
          have hc : InPositiveChart (R, y, p.2.2) := by
            unfold InPositiveChart s
            linarith [hy.1]
          simpa using
            ((hu (R, y, p.2.2) hc).2.1.sub
              (potential_hasCoordinateGradientAt (R, y, p.2.2) hc).2.1)
      have hzp :
          u (R, q.2.1, p.2.2) - potential (R, q.2.1, p.2.2) =
            u (R, q.2.1, q.2.2) - potential (R, q.2.1, q.2.2) := by
        refine eq_of_hasDerivAt_zero_on_Ioo
          (f := fun z => u (R, q.2.1, z) - potential (R, q.2.1, z))
          (l := min p.2.2 q.2.2 - 1) (r := max p.2.2 q.2.2 + 1)
          (x := p.2.2) (y := q.2.2) ?_ ?_ ?_
        · constructor
          · linarith [min_le_left p.2.2 q.2.2]
          · linarith [le_max_left p.2.2 q.2.2]
        · constructor
          · linarith [min_le_right p.2.2 q.2.2]
          · linarith [le_max_right p.2.2 q.2.2]
        · intro z hz
          have hc : InPositiveChart (R, q.2.1, z) := by
            unfold InPositiveChart s
            linarith
          simpa using
            ((hu (R, q.2.1, z) hc).2.2.sub
              (potential_hasCoordinateGradientAt (R, q.2.1, z) hc).2.2)
      have hxq :
          u (R, q.2.1, q.2.2) - potential (R, q.2.1, q.2.2) =
            u q - potential q := by
        refine eq_of_hasDerivAt_zero_on_Ioo
          (f := fun x => u (x, q.2.1, q.2.2) -
            potential (x, q.2.1, q.2.2))
          (l := -q.2.1) (r := R + 1) (x := R) (y := q.1) ?_ ?_ ?_
        · constructor <;> linarith
        · constructor
          · have hsq : 0 < q.1 + q.2.1 := hq
            linarith
          · linarith
        · intro x hx
          have hc : InPositiveChart (x, q.2.1, q.2.2) := by
            unfold InPositiveChart s
            linarith [hx.1]
          simpa using
            ((hu (x, q.2.1, q.2.2) hc).1.sub
              (potential_hasCoordinateGradientAt (x, q.2.1, q.2.2) hc).1)
      exact hxp.trans (hyp.trans (hzp.trans hxq))
    refine ⟨u (1, 0, 0) - potential (1, 0, 0), ?_⟩
    intro p hp
    have hb : InPositiveChart (1, 0, 0) := by
      norm_num [InPositiveChart, s]
    have heq := hconst p (1, 0, 0) hp hb
    linarith
  · rintro ⟨C, hu⟩
    intro p hp
    have hpot := potential_hasCoordinateGradientAt p hp
    refine ⟨?_, ?_, ?_⟩
    · have hlower : -p.2.1 < p.1 := by
        have hs : 0 < p.1 + p.2.1 := hp
        linarith
      have he :
          (fun x => u (x, p.2.1, p.2.2)) =ᶠ[nhds p.1]
            (fun x => potential (x, p.2.1, p.2.2) + C) := by
        refine Filter.mem_of_superset (Ioi_mem_nhds hlower) ?_
        intro x hx
        exact hu (x, p.2.1, p.2.2) (by
          change 0 < x + p.2.1
          change -p.2.1 < x at hx
          linarith)
      exact (hpot.1.add_const C).congr_of_eventuallyEq he
    · have hlower : -p.1 < p.2.1 := by
        have hs : 0 < p.1 + p.2.1 := hp
        linarith
      have he :
          (fun y => u (p.1, y, p.2.2)) =ᶠ[nhds p.2.1]
            (fun y => potential (p.1, y, p.2.2) + C) := by
        refine Filter.mem_of_superset (Ioi_mem_nhds hlower) ?_
        intro y hy
        exact hu (p.1, y, p.2.2) (by
          change 0 < p.1 + y
          change -p.1 < y at hy
          linarith)
      exact (hpot.2.1.add_const C).congr_of_eventuallyEq he
    · have he :
          (fun z => u (p.1, p.2.1, z)) =ᶠ[nhds p.2.2]
            (fun z => potential (p.1, p.2.1, z) + C) := by
        apply Filter.Eventually.of_forall
        intro z
        exact hu (p.1, p.2.1, z) (by
          unfold InPositiveChart s
          exact hp)
      exact (hpot.2.2.add_const C).congr_of_eventuallyEq he

theorem gap6 (C : ℝ) :
    IsSolution (fun p => potential p + C) := by
  intro p hp
  have hpot := potential_hasCoordinateGradientAt p hp
  exact ⟨hpot.1.add_const C, hpot.2.1.add_const C, hpot.2.2.add_const C⟩

end

end ProofGap.Exercise4292
