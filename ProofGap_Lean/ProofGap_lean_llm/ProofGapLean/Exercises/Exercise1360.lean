import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1360

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def f₀ (a x : ℝ) : ℝ :=
  (Real.rpow (a + x) x - Real.rpow a x) / x ^ 2
def f₁ (a x : ℝ) : ℝ :=
  (Real.rpow (a + x) x * (Real.log (a + x) + x / (a + x)) -
    Real.rpow a x * Real.log a) / (2 * x)
def secondExpr (a x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.rpow (a + x) x * (Real.log (a + x) + x / (a + x)) ^ 2 +
      Real.rpow (a + x) x * (1 / (a + x) + a / (a + x) ^ 2) -
      Real.rpow a x * Real.log a ^ 2)

private theorem limits_at_zero (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (f₀ a) (1 / a) ∧
      HasLimitAtZero (f₁ a) (1 / a) ∧
        HasLimitAtZero (secondExpr a) (1 / a) := by
  let l : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have slope_limit : ∀ (g : ℝ → ℝ) (c : ℝ),
      HasDerivAt g c 0 → g 0 = 0 →
        Filter.Tendsto (fun x => g x / x) l (nhds c) := by
    intro g c hg hg0
    have hs := hasDerivAt_iff_tendsto_slope.mp hg
    apply hs.congr'
    filter_upwards with x
    change (x - 0)⁻¹ • (g x - g 0) = g x / x
    rw [hg0]
    simp [div_eq_mul_inv, mul_comm]
  have hax : HasDerivAt (fun x : ℝ => a + x) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) a).add (hasDerivAt_id (0 : ℝ))
  have haxT : Filter.Tendsto (fun x : ℝ => a + x) l (nhds a) := by
    convert hax.continuousAt.tendsto.mono_left
      (show l ≤ nhds 0 from inf_le_left) using 1 <;> simp
  have hlogBase : HasDerivAt Real.log (1 / a) (a + 0) := by
    simpa [div_eq_mul_inv] using Real.hasDerivAt_log ha.ne'
  have hlog : HasDerivAt (fun x : ℝ => Real.log (a + x)) (1 / a) 0 := by
    simpa only [Function.comp_apply, mul_one] using hlogBase.comp 0 hax
  have hden : a + 0 ≠ 0 := by
    simpa using ha.ne'
  have hfrac : HasDerivAt (fun x : ℝ => x / (a + x)) (1 / a) 0 := by
    have hdiv := (hasDerivAt_id (0 : ℝ)).div hax hden
    convert hdiv using 1 <;>
      simp [id_eq, ha.ne'] <;>
      field_simp [ha.ne'] <;> ring
  have hlogMul : HasDerivAt
      (fun x : ℝ => Real.log (a + x) * x) (Real.log a) 0 := by
    convert hlog.mul (hasDerivAt_id (0 : ℝ)) using 1 <;> simp [id_eq]
  have hEA : HasDerivAt
      (fun x : ℝ => Real.exp (Real.log (a + x) * x)) (Real.log a) 0 := by
    simpa using hlogMul.exp
  have hconstLogMul : HasDerivAt
      (fun x : ℝ => Real.log a * x) (Real.log a) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (Real.log a)).mul
      (hasDerivAt_id (0 : ℝ)) using 1 <;> simp [id_eq]
  have hEB : HasDerivAt
      (fun x : ℝ => Real.exp (Real.log a * x)) (Real.log a) 0 := by
    simpa using hconstLogMul.exp
  have hbracket : HasDerivAt
      (fun x : ℝ => Real.log (a + x) + x / (a + x)) (2 / a) 0 := by
    convert hlog.add hfrac using 1 <;>
      simp [id_eq, ha.ne'] <;>
      field_simp [ha.ne'] <;> ring
  have hpos : ∀ᶠ x in l, 0 < a + x :=
    haxT.eventually (Ioi_mem_nhds ha)
  have hxne : ∀ᶠ x in l, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hlogDiff : HasDerivAt
      ((fun x : ℝ => Real.log (a + x)) - (fun _ : ℝ => Real.log a))
      (1 / a) 0 := by
    convert hlog.sub (hasDerivAt_const (0 : ℝ) (Real.log a)) using 1 <;>
      simp only [Pi.sub_apply, sub_zero]
  have hqlog : Filter.Tendsto
      (fun x : ℝ => (Real.log (a + x) - Real.log a) / x) l
      (nhds (1 / a)) := by
    simpa only [Pi.sub_apply] using
      slope_limit _ _ hlogDiff (by simp)
  have hexpDiff : HasDerivAt
      (Real.exp - (fun _ : ℝ => 1)) 1 0 := by
    simpa [Real.exp_zero] using
      (Real.hasDerivAt_exp 0).sub (hasDerivAt_const (0 : ℝ) 1)
  have hqexp : Filter.Tendsto
      (fun x : ℝ => (Real.exp x - 1) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Pi.sub_apply] using
      slope_limit (Real.exp - (fun _ : ℝ => 1)) 1 hexpDiff (by simp)
  have hid : Filter.Tendsto (fun x : ℝ => x) l (nhds 0) :=
    (hasDerivAt_id (0 : ℝ)).continuousAt.tendsto.mono_left
      (show l ≤ nhds 0 from inf_le_left)
  have hdiff : Filter.Tendsto
      (fun x : ℝ => Real.log (a + x) - Real.log a) l (nhds 0) := by
    have ht : Filter.Tendsto
        ((fun x : ℝ => Real.log (a + x)) - (fun _ : ℝ => Real.log a))
        l (nhds 0) := by
      convert hlogDiff.continuousAt.tendsto.mono_left
        (show l ≤ nhds 0 from inf_le_left) using 1 <;> simp
    simpa only [Pi.sub_apply] using ht
  have hu0 : Filter.Tendsto
      (fun x : ℝ => x * (Real.log (a + x) - Real.log a)) l (nhds 0) := by
    simpa using hid.mul hdiff
  have hune : ∀ᶠ x in l,
      x * (Real.log (a + x) - Real.log a) ≠ 0 := by
    filter_upwards [hpos, hxne] with x hxpos hx
    apply mul_ne_zero hx
    apply sub_ne_zero.mpr
    intro heq
    have he := congrArg Real.exp heq
    rw [Real.exp_log hxpos, Real.exp_log ha] at he
    exact hx (by linarith [he])
  have hu : Filter.Tendsto
      (fun x : ℝ => x * (Real.log (a + x) - Real.log a)) l
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hu0, ?_⟩
    filter_upwards [hune] with x hx
    simpa using hx
  have hB : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.log a * x)) l (nhds 1) := by
    simpa using hEB.continuousAt.tendsto.mono_left
      (show l ≤ nhds 0 from inf_le_left)
  have hf0raw : Filter.Tendsto
      (fun x : ℝ =>
        Real.exp (Real.log a * x) *
          (((Real.exp (x * (Real.log (a + x) - Real.log a)) - 1) /
              (x * (Real.log (a + x) - Real.log a))) *
            ((Real.log (a + x) - Real.log a) / x)))
      l (nhds (1 / a)) := by
    convert hB.mul ((hqexp.comp hu).mul hqlog) using 1 <;> simp
  have hf0 : HasLimitAtZero (f₀ a) (1 / a) := by
    unfold HasLimitAtZero
    apply hf0raw.congr'
    filter_upwards [hpos, hxne] with x hxpos hx
    have hd : Real.log (a + x) - Real.log a ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have he := congrArg Real.exp heq
      rw [Real.exp_log hxpos, Real.exp_log ha] at he
      exact hx (by linarith [he])
    have he : Real.exp (Real.log (a + x) * x) =
        Real.exp (Real.log a * x) *
          Real.exp (x * (Real.log (a + x) - Real.log a)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hrA : Real.rpow (a + x) x =
        Real.exp (Real.log (a + x) * x) := by
      exact Real.rpow_def_of_pos hxpos x
    have hrB : Real.rpow a x = Real.exp (Real.log a * x) := by
      exact Real.rpow_def_of_pos ha x
    change
      Real.exp (Real.log a * x) *
          (((Real.exp (x * (Real.log (a + x) - Real.log a)) - 1) /
              (x * (Real.log (a + x) - Real.log a))) *
            ((Real.log (a + x) - Real.log a) / x)) =
        (Real.rpow (a + x) x - Real.rpow a x) / x ^ 2
    rw [hrA, hrB, he]
    field_simp [hx, hd]
  have hg : HasDerivAt
      (fun x : ℝ =>
        Real.exp (Real.log (a + x) * x) *
            (Real.log (a + x) + x / (a + x)) -
          Real.exp (Real.log a * x) * Real.log a)
      (2 / a) 0 := by
    have hgraw := (hEA.mul hbracket).sub
      (hEB.mul (hasDerivAt_const (0 : ℝ) (Real.log a)))
    convert hgraw using 1 <;> simp [ha.ne'] <;>
      field_simp [ha.ne'] <;> ring
  have hgq : Filter.Tendsto
      (fun x : ℝ =>
        (Real.exp (Real.log (a + x) * x) *
              (Real.log (a + x) + x / (a + x)) -
            Real.exp (Real.log a * x) * Real.log a) / x)
      l (nhds (2 / a)) := by
    apply slope_limit _ _ hg
    simp
  have hf1raw : Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) *
        ((Real.exp (Real.log (a + x) * x) *
              (Real.log (a + x) + x / (a + x)) -
            Real.exp (Real.log a * x) * Real.log a) / x))
      l (nhds (1 / a)) := by
    have hhalf : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) l
        (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
    have ht := hhalf.mul hgq
    convert ht using 1 <;> field_simp [ha.ne'] <;> ring
  have hf1 : HasLimitAtZero (f₁ a) (1 / a) := by
    unfold HasLimitAtZero
    apply hf1raw.congr'
    filter_upwards [hpos, hxne] with x hxpos hx
    have hrA : Real.rpow (a + x) x =
        Real.exp (Real.log (a + x) * x) := by
      exact Real.rpow_def_of_pos hxpos x
    have hrB : Real.rpow a x = Real.exp (Real.log a * x) := by
      exact Real.rpow_def_of_pos ha x
    change
      (1 / 2 : ℝ) *
          ((Real.exp (Real.log (a + x) * x) *
                (Real.log (a + x) + x / (a + x)) -
              Real.exp (Real.log a * x) * Real.log a) / x) =
        (Real.rpow (a + x) x *
              (Real.log (a + x) + x / (a + x)) -
            Real.rpow a x * Real.log a) / (2 * x)
    rw [hrA, hrB]
    field_simp [hx]
  have hlogT : Filter.Tendsto (fun x : ℝ => Real.log (a + x)) l
      (nhds (Real.log a)) := by
    have ht := hlog.continuousAt.tendsto.mono_left
      (show l ≤ nhds 0 from inf_le_left)
    convert ht using 1 <;> simp
  have hfracT : Filter.Tendsto (fun x : ℝ => x / (a + x)) l
      (nhds (0 / a)) :=
    hid.div haxT ha.ne'
  have hRA : Filter.Tendsto (fun x : ℝ => Real.rpow (a + x) x) l
      (nhds 1) := by
    have ht : Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (a + x) * x)) l (nhds 1) := by
      simpa using hEA.continuousAt.tendsto.mono_left
        (show l ≤ nhds 0 from inf_le_left)
    refine ht.congr' ?_
    filter_upwards [hpos] with x hxpos
    have hrA : Real.rpow (a + x) x =
        Real.exp (Real.log (a + x) * x) := by
      exact Real.rpow_def_of_pos hxpos x
    exact hrA.symm
  have hRB : Filter.Tendsto (fun x : ℝ => Real.rpow a x) l
      (nhds 1) := by
    have ht : Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log a * x)) l (nhds 1) := by
      simpa using hEB.continuousAt.tendsto.mono_left
        (show l ≤ nhds 0 from inf_le_left)
    refine ht.congr' ?_
    filter_upwards with x
    have hrB : Real.rpow a x = Real.exp (Real.log a * x) := by
      exact Real.rpow_def_of_pos ha x
    exact hrB.symm
  have honeDiv : Filter.Tendsto (fun x : ℝ => 1 / (a + x)) l
      (nhds (1 / a)) :=
    tendsto_const_nhds.div haxT ha.ne'
  have haDivSq : Filter.Tendsto (fun x : ℝ => a / (a + x) ^ 2) l
      (nhds (a / a ^ 2)) :=
    tendsto_const_nhds.div (haxT.pow 2) (pow_ne_zero 2 ha.ne')
  have hhalf : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) l
      (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have hlogConst : Filter.Tendsto (fun _ : ℝ => Real.log a) l
      (nhds (Real.log a)) := tendsto_const_nhds
  have hsPart1 : Filter.Tendsto
      (fun x : ℝ => Real.rpow (a + x) x *
        (Real.log (a + x) + x / (a + x)) ^ 2) l
      (nhds (1 * (Real.log a + 0 / a) ^ 2)) :=
    hRA.mul ((hlogT.add hfracT).pow 2)
  have hsPart2 : Filter.Tendsto
      (fun x : ℝ => Real.rpow (a + x) x *
        (1 / (a + x) + a / (a + x) ^ 2)) l
      (nhds (1 * (1 / a + a / a ^ 2))) :=
    hRA.mul (honeDiv.add haDivSq)
  have hsPart3 : Filter.Tendsto
      (fun x : ℝ => Real.rpow a x * Real.log a ^ 2) l
      (nhds (1 * Real.log a ^ 2)) :=
    hRB.mul (hlogConst.pow 2)
  have hsInside := hsPart1.add (hsPart2.sub hsPart3)
  have hsraw := hhalf.mul hsInside
  have hs : HasLimitAtZero (secondExpr a) (1 / a) := by
    unfold HasLimitAtZero
    have hfun :
        (fun x : ℝ => (1 / 2 : ℝ) *
          (Real.rpow (a + x) x *
              (Real.log (a + x) + x / (a + x)) ^ 2 +
            (Real.rpow (a + x) x *
                (1 / (a + x) + a / (a + x) ^ 2) -
              Real.rpow a x * Real.log a ^ 2))) = secondExpr a := by
      funext x
      unfold secondExpr
      ring
    have hvalue :
        (1 / 2 : ℝ) *
            (1 * (Real.log a + 0 / a) ^ 2 +
              (1 * (1 / a + a / a ^ 2) -
                1 * Real.log a ^ 2)) =
          1 / a := by
      field_simp [ha.ne']
      ring
    rw [← hfun, ← hvalue]
    exact hsraw
  exact ⟨hf0, hf1, hs⟩

theorem gap1 (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (f₀ a) (1 / a) ↔ HasLimitAtZero (f₁ a) (1 / a) := by
  constructor
  · intro _
    exact (limits_at_zero a ha).2.1
  · intro _
    exact (limits_at_zero a ha).1

theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (f₀ a) (1 / a) ↔
      HasLimitAtZero (secondExpr a) (1 / a) := by
  constructor
  · intro _
    exact (limits_at_zero a ha).2.2
  · intro _
    exact (limits_at_zero a ha).1

theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (secondExpr a) (1 / a) := by
  exact (limits_at_zero a ha).2.2

theorem gap4 (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (f₀ a) (1 / a) := by
  exact (limits_at_zero a ha).1

end

end ProofGap.Exercise1360
