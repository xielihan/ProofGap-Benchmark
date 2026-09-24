import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4272

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def denominator (x y : ℝ) : ℝ :=
  3 * x ^ 2 - 2 * x * y + 3 * y ^ 2

def P (x y : ℝ) : ℝ :=
  y / denominator x y

def Q (x y : ℝ) : ℝ :=
  -x / denominator x y

def field (z : Point) : Point :=
  (P z.1 z.2, Q z.1 z.2)

def InUpperHalfPlane (z : Point) : Prop :=
  0 < z.2

def constructedPotential (z : Point) : ℝ :=
  (∫ s in (0 : ℝ)..z.1, P s z.2) +
    ∫ t in (1 : ℝ)..z.2, (0 : ℝ)

def completedSquarePotential (z : Point) : ℝ :=
  z.2 / 3 *
    ∫ s in (0 : ℝ)..z.1,
      1 / ((s - z.2 / 3) ^ 2 + 8 * z.2 ^ 2 / 9)

def arctangentPotential (z : Point) : ℝ :=
  1 / (2 * Real.sqrt 2) *
    Real.arctan ((3 * z.1 - z.2) / (2 * Real.sqrt 2 * z.2))

def arctangentDifference (z : Point) : ℝ :=
  arctangentPotential z - arctangentPotential (0, z.2)

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def IsUpperSolution (z : Point → ℝ) : Prop :=
  ∀ p, InUpperHalfPlane p → HasCoordinateGradientAt z (field p) p

private theorem upper_potential_facts :
    (∀ p : Point, InUpperHalfPlane p →
      HasCoordinateGradientAt arctangentPotential (field p) p) ∧
    (∀ p : Point, InUpperHalfPlane p →
      constructedPotential p = arctangentDifference p) ∧
    (∀ y : ℝ, 0 < y →
      arctangentPotential (0, y) = arctangentPotential (0, 1)) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hgrad : ∀ p : Point, InUpperHalfPlane p →
      HasCoordinateGradientAt arctangentPotential (field p) p := by
    rintro ⟨x, y⟩ hy
    change 0 < y at hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hden : denominator x y ≠ 0 := by
      unfold denominator
      have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
      nlinarith [sq_nonneg (3 * x - y)]
    constructor
    · have harg : HasDerivAt
          (fun t => (3 * t - y) / (2 * Real.sqrt 2 * y))
          (3 / (2 * Real.sqrt 2 * y)) x := by
        convert (((hasDerivAt_id x).const_mul 3).sub_const y).div_const
          (2 * Real.sqrt 2 * y) using 1 <;> ring
      have hraw :=
        ((Real.hasDerivAt_arctan _).comp x harg).const_mul
          (1 / (2 * Real.sqrt 2))
      change HasDerivAt
        (fun t => arctangentPotential (t, y)) (P x y) x
      convert hraw using 1
      unfold P
      field_simp [hs, hy0, hden]
      unfold denominator
      rw [hs2]
      ring
    · have hnum : HasDerivAt (fun t => 3 * x - t) (-1) y := by
        simpa using (hasDerivAt_const y (3 * x)).sub (hasDerivAt_id y)
      have hmul : HasDerivAt
          (fun t => 2 * Real.sqrt 2 * t) (2 * Real.sqrt 2) y := by
        convert (hasDerivAt_id y).const_mul (2 * Real.sqrt 2) using 1 <;> ring
      have hne : 2 * Real.sqrt 2 * y ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hs) hy0
      have harg := hnum.div hmul hne
      have hraw :=
        ((Real.hasDerivAt_arctan _).comp y harg).const_mul
          (1 / (2 * Real.sqrt 2))
      change HasDerivAt
        (fun t => arctangentPotential (x, t)) (Q x y) y
      convert hraw using 1
      unfold Q
      simp only [Pi.div_apply]
      field_simp [hs, hy0, hden]
      unfold denominator
      rw [hs2]
      ring
  have hconstructed : ∀ p : Point, InUpperHalfPlane p →
      constructedPotential p = arctangentDifference p := by
    rintro ⟨x, y⟩ hy
    change 0 < y at hy
    have hden : ∀ t : ℝ, denominator t y ≠ 0 := by
      intro t
      unfold denominator
      have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
      nlinarith [sq_nonneg (3 * t - y)]
    have hden_cont : Continuous (fun t : ℝ => denominator t y) := by
      unfold denominator
      fun_prop
    have hcont : Continuous (fun t => P t y) := by
      unfold P
      exact continuous_const.div hden_cont hden
    let f : ℝ → ℝ := fun t =>
      constructedPotential (t, y) - arctangentDifference (t, y)
    have hf : ∀ t, HasDerivAt f 0 t := by
      intro t
      have hsm : StronglyMeasurableAtFilter
          (fun u : ℝ => P u y) (nhds t) MeasureTheory.volume :=
        hcont.stronglyMeasurable.stronglyMeasurableAtFilter
      have hi : HasDerivAt
          (fun u => constructedPotential (u, y)) (P t y) t := by
        simpa [constructedPotential] using
          intervalIntegral.integral_hasDerivAt_right
            (hcont.intervalIntegrable 0 t) hsm hcont.continuousAt
      have ha := (hgrad (t, y) hy).1
      have had : HasDerivAt
          (fun u => arctangentDifference (u, y)) (P t y) t := by
        simpa [arctangentDifference] using
          ha.sub_const (arctangentPotential (0, y))
      simpa [f] using hi.sub had
    have hc : f x = f 0 := is_const_of_deriv_eq_zero
      (fun t => (hf t).differentiableAt)
      (fun t => (hf t).deriv) x 0
    have hx0 : f x = 0 := by
      calc
        f x = f 0 := hc
        _ = 0 := by
          simp [f, constructedPotential, arctangentDifference]
    exact sub_eq_zero.mp (by simpa [f] using hx0)
  have hbase : ∀ y : ℝ, 0 < y →
      arctangentPotential (0, y) = arctangentPotential (0, 1) := by
    intro y hy
    let f : ℝ → ℝ := fun t => arctangentPotential (0, Real.exp t)
    have hf : ∀ t, HasDerivAt f 0 t := by
      intro t
      have he : 0 < Real.exp t := Real.exp_pos t
      have hd := (hgrad (0, Real.exp t) he).2
      have hc := hd.comp t (Real.hasDerivAt_exp t)
      simpa [f, field, Q] using hc
    have hc := is_const_of_deriv_eq_zero
      (fun t => (hf t).differentiableAt)
      (fun t => (hf t).deriv) (Real.log y) 0
    simpa [f, Real.exp_log hy] using hc
  exact ⟨hgrad, hconstructed, hbase⟩

theorem gap1 (z : Point → ℝ) :
    IsUpperSolution z ↔
      ∃ C : ℝ, ∀ p, InUpperHalfPlane p →
        z p = constructedPotential p + C := by
  constructor
  · intro hz
    refine ⟨z (0, 1), ?_⟩
    intro p hp
    rcases p with ⟨x, y⟩
    change 0 < y at hp
    have hhor :
        z (x, y) - arctangentPotential (x, y) =
          z (0, y) - arctangentPotential (0, y) := by
      let f : ℝ → ℝ := fun t =>
        z (t, y) - arctangentPotential (t, y)
      have hf : ∀ t, HasDerivAt f 0 t := by
        intro t
        have hz' := (hz (t, y) hp).1
        have ha' := (upper_potential_facts.1 (t, y) hp).1
        simpa [f] using hz'.sub ha'
      exact is_const_of_deriv_eq_zero
        (fun t => (hf t).differentiableAt)
        (fun t => (hf t).deriv) x 0
    have hvert :
        z (0, y) - arctangentPotential (0, y) =
          z (0, 1) - arctangentPotential (0, 1) := by
      let f : ℝ → ℝ := fun t =>
        z (0, Real.exp t) - arctangentPotential (0, Real.exp t)
      have hf : ∀ t, HasDerivAt f 0 t := by
        intro t
        have he : 0 < Real.exp t := Real.exp_pos t
        have hz' := (hz (0, Real.exp t) he).2
        have ha' := (upper_potential_facts.1 (0, Real.exp t) he).2
        have hd : HasDerivAt
            (fun u => z (0, u) - arctangentPotential (0, u)) 0
            (Real.exp t) := by
          simpa using hz'.sub ha'
        simpa [f] using hd.comp t (Real.hasDerivAt_exp t)
      have hc := is_const_of_deriv_eq_zero
        (fun t => (hf t).differentiableAt)
        (fun t => (hf t).deriv) (Real.log y) 0
      simpa [f, Real.exp_log hp] using hc
    have hpotential := upper_potential_facts.2.1 (x, y) hp
    have hbase := upper_potential_facts.2.2 y hp
    rw [hpotential]
    unfold arctangentDifference
    rw [hbase]
    linarith
  · rintro ⟨C, hC⟩ p hp
    rcases p with ⟨x, y⟩
    change 0 < y at hp
    have hvalue : ∀ q : Point, InUpperHalfPlane q →
        z q = arctangentPotential q +
          (C - arctangentPotential (0, 1)) := by
      intro q hq
      rw [hC q hq, upper_potential_facts.2.1 q hq]
      unfold arctangentDifference
      rw [upper_potential_facts.2.2 q.2 hq]
      ring
    constructor
    · have heq : (fun t => z (t, y)) =
          fun t => arctangentPotential (t, y) +
            (C - arctangentPotential (0, 1)) := by
        funext t
        exact hvalue (t, y) hp
      rw [heq]
      exact (upper_potential_facts.1 (x, y) hp).1.add_const _
    · have hd := (upper_potential_facts.1 (x, y) hp).2.add_const
        (C - arctangentPotential (0, 1))
      have hevent :
          (fun t => z (x, t)) =ᶠ[nhds y]
            fun t => arctangentPotential (x, t) +
              (C - arctangentPotential (0, 1)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hp] with t ht
        exact hvalue (x, t) ht
      exact hd.congr_of_eventuallyEq hevent

theorem gap2 (p : Point) (hp : InUpperHalfPlane p) :
    constructedPotential p = completedSquarePotential p := by
  rcases p with ⟨x, y⟩
  change 0 < y at hp
  have hden : ∀ s : ℝ, denominator s y ≠ 0 := by
    intro s
    unfold denominator
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hp
    nlinarith [sq_nonneg (3 * s - y)]
  have hsq : ∀ s : ℝ,
      (s - y / 3) ^ 2 + 8 * y ^ 2 / 9 ≠ 0 := by
    intro s
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hp
    nlinarith [sq_nonneg (s - y / 3)]
  simp only [constructedPotential, completedSquarePotential,
    intervalIntegral.integral_zero, add_zero]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  unfold P
  field_simp [hden s, hsq s]
  unfold denominator
  ring

theorem gap3 (z : Point → ℝ) :
    IsUpperSolution z ↔
      ∃ C : ℝ, ∀ p, InUpperHalfPlane p →
        z p = completedSquarePotential p + C := by
  constructor
  · intro hz
    rcases (gap1 z).mp hz with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro p hp
    rw [hC p hp, gap2 p hp]
  · rintro ⟨C, hC⟩
    apply (gap1 z).2
    refine ⟨C, ?_⟩
    intro p hp
    rw [hC p hp, gap2 p hp]

theorem gap4 (p : Point) (hp : InUpperHalfPlane p) :
    completedSquarePotential p = arctangentDifference p := by
  rw [← gap2 p hp]
  exact upper_potential_facts.2.1 p hp

theorem gap5 (C : ℝ) :
    ∃ C₁ : ℝ, ∀ p, InUpperHalfPlane p →
      arctangentDifference p + C = arctangentPotential p + C₁ := by
  refine ⟨C - arctangentPotential (0, 1), ?_⟩
  intro p hp
  unfold arctangentDifference
  rw [upper_potential_facts.2.2 p.2 hp]
  ring

theorem gap6 (z : Point → ℝ) :
    IsUpperSolution z ↔
      ∃ C₁ : ℝ, ∀ p, InUpperHalfPlane p →
        z p = arctangentPotential p + C₁ := by
  constructor
  · intro hz
    rcases (gap3 z).mp hz with ⟨C, hC⟩
    rcases gap5 C with ⟨C₁, hC₁⟩
    refine ⟨C₁, ?_⟩
    intro p hp
    rw [hC p hp, gap4 p hp, hC₁ p hp]
  · rintro ⟨C₁, hC₁⟩
    apply (gap3 z).2
    refine ⟨C₁ + arctangentPotential (0, 1), ?_⟩
    intro p hp
    rw [hC₁ p hp, gap4 p hp]
    unfold arctangentDifference
    rw [upper_potential_facts.2.2 p.2 hp]
    ring

theorem gap7 (C₁ : ℝ) :
    IsUpperSolution (fun p => arctangentPotential p + C₁) := by
  apply (gap6 (fun p => arctangentPotential p + C₁)).2
  exact ⟨C₁, fun p hp => rfl⟩

end

end ProofGap.Exercise4272
