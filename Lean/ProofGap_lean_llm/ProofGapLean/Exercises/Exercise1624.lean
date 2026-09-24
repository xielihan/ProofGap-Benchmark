import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1624

noncomputable section

def f (x : ℝ) := x + Real.exp x
def approximant : ℕ → ℝ
  | 1 => -0.5
  | 2 => -0.56631
  | 3 => -0.567132
  | 4 => -0.567145
  | _ => 0
def ApproxRoot (sample tolerance : ℝ) : Prop :=
  ∃ r ∈ Set.Ioo (-1 : ℝ) 0, f r = 0 ∧ |sample - r| < tolerance

private theorem residual_bound :
    |f (-0.567145)| < (5 : ℝ) / 1000000 := by
  set_option maxRecDepth 4096 in
    set_option maxHeartbeats 2000000 in
      let u : ℝ := (567145 : ℝ) / 1000000 / 65536
      have hlow0 : 1 - u ≤ Real.exp (-u) := by
        nlinarith [Real.add_one_le_exp (-u)]
      have hb : 1 + u ≤ Real.exp u := by
        nlinarith [Real.add_one_le_exp u]
      have hupos : 0 < 1 + u := by
        dsimp [u]
        norm_num
      have hupp0 : Real.exp (-u) ≤ 1 / (1 + u) := by
        have hrec := one_div_le_one_div_of_le hupos hb
        simpa [Real.exp_neg, one_div] using hrec
      have hexp16 (x : ℝ) :
          (Real.exp x) ^ (16 : ℕ) = Real.exp (16 * x) := by
        symm
        simpa using (Real.exp_nat_mul x 16)
      have hlow1 :
          (0.9998615458 : ℝ) < Real.exp (-16 * u) := by
        calc
          (0.9998615458 : ℝ) < (1 - u) ^ (16 : ℕ) := by
            norm_num [u]
          _ ≤ (Real.exp (-u)) ^ (16 : ℕ) := by
            gcongr
          _ = Real.exp (16 * (-u)) := hexp16 (-u)
          _ = Real.exp (-16 * u) := by
            congr 1
            ring
      have hupp1 :
          Real.exp (-16 * u) < (0.9998615471 : ℝ) := by
        calc
          Real.exp (-16 * u) = Real.exp (16 * (-u)) := by
            congr 1
            ring
          _ = (Real.exp (-u)) ^ (16 : ℕ) := (hexp16 (-u)).symm
          _ ≤ (1 / (1 + u)) ^ (16 : ℕ) := by
            gcongr
          _ < (0.9998615471 : ℝ) := by
            norm_num [u]
      have hlow2 :
          (0.9977870316 : ℝ) < Real.exp (-256 * u) := by
        calc
          (0.9977870316 : ℝ) < (0.9998615458 : ℝ) ^ (16 : ℕ) := by
            norm_num
          _ ≤ (Real.exp (-16 * u)) ^ (16 : ℕ) := by
            gcongr
          _ = Real.exp (16 * (-16 * u)) := hexp16 (-16 * u)
          _ = Real.exp (-256 * u) := by
            congr 1
            ring
      have hupp2 :
          Real.exp (-256 * u) < (0.9977870525 : ℝ) := by
        calc
          Real.exp (-256 * u) = Real.exp (16 * (-16 * u)) := by
            congr 1
            ring
          _ = (Real.exp (-16 * u)) ^ (16 : ℕ) :=
            (hexp16 (-16 * u)).symm
          _ ≤ (0.9998615471 : ℝ) ^ (16 : ℕ) := by
            gcongr
          _ < (0.9977870525 : ℝ) := by
            norm_num
      have hlow3 :
          (0.9651741 : ℝ) < Real.exp (-4096 * u) := by
        calc
          (0.9651741 : ℝ) < (0.9977870316 : ℝ) ^ (16 : ℕ) := by
            norm_num
          _ ≤ (Real.exp (-256 * u)) ^ (16 : ℕ) := by
            gcongr
          _ = Real.exp (16 * (-256 * u)) := hexp16 (-256 * u)
          _ = Real.exp (-4096 * u) := by
            congr 1
            ring
      have hupp3 :
          Real.exp (-4096 * u) < (0.9651745 : ℝ) := by
        calc
          Real.exp (-4096 * u) = Real.exp (16 * (-256 * u)) := by
            congr 1
            ring
          _ = (Real.exp (-256 * u)) ^ (16 : ℕ) :=
            (hexp16 (-256 * u)).symm
          _ ≤ (0.9977870525 : ℝ) ^ (16 : ℕ) := by
            gcongr
          _ < (0.9651745 : ℝ) := by
            norm_num
      have hlow4 :
          (0.56714 : ℝ) < Real.exp (-65536 * u) := by
        calc
          (0.56714 : ℝ) < (0.9651741 : ℝ) ^ (16 : ℕ) := by
            norm_num
          _ ≤ (Real.exp (-4096 * u)) ^ (16 : ℕ) := by
            gcongr
          _ = Real.exp (16 * (-4096 * u)) := hexp16 (-4096 * u)
          _ = Real.exp (-65536 * u) := by
            congr 1
            ring
      have hupp4 :
          Real.exp (-65536 * u) < (0.56715 : ℝ) := by
        calc
          Real.exp (-65536 * u) = Real.exp (16 * (-4096 * u)) := by
            congr 1
            ring
          _ = (Real.exp (-4096 * u)) ^ (16 : ℕ) :=
            (hexp16 (-4096 * u)).symm
          _ ≤ (0.9651745 : ℝ) ^ (16 : ℕ) := by
            gcongr
          _ < (0.56715 : ℝ) := by
            norm_num
      have hu : (-65536 : ℝ) * u = (-0.567145 : ℝ) := by
        norm_num [u]
      have hexplow : (0.56714 : ℝ) < Real.exp (-0.567145) := by
        calc
          (0.56714 : ℝ) < Real.exp ((-65536 : ℝ) * u) := hlow4
          _ = Real.exp (-0.567145) := congrArg Real.exp hu
      have hexpupp : Real.exp (-0.567145) < (0.56715 : ℝ) := by
        calc
          Real.exp (-0.567145) = Real.exp ((-65536 : ℝ) * u) :=
            (congrArg Real.exp hu).symm
          _ < (0.56715 : ℝ) := hupp4
      rw [abs_lt]
      constructor <;> dsimp [f] <;> norm_num at * <;> linarith

theorem gap1 (x : ℝ) :
    deriv f x = 1 + Real.exp x := by
  change deriv (fun y : ℝ => y + Real.exp y) x = 1 + Real.exp x
  exact ((hasDerivAt_id x).add (Real.hasDerivAt_exp x)).deriv
theorem gap2 (x : ℝ) : 1 + Real.exp x > 0 := by
  have h := Real.exp_pos x
  linarith
theorem gap3 (x : ℝ) : deriv f x > 0 := by
  rw [gap1]
  exact gap2 x
theorem gap4 (x : ℝ) :
    deriv (deriv f) x = Real.exp x := by
  rw [show deriv f = fun y => 1 + Real.exp y from funext gap1]
  simpa using
    ((hasDerivAt_const (x : ℝ) (1 : ℝ)).add Real.hasDerivAt_exp).deriv
theorem gap5 (x : ℝ) : Real.exp x > 0 := by
  exact Real.exp_pos x
theorem gap6 (x : ℝ) : deriv (deriv f) x > 0 := by
  rw [gap4]
  exact gap5 x
theorem gap7 : f 0 = 1 := by
  norm_num [f]
theorem gap8 : f (-1) = 1 / Real.exp 1 - 1 := by
  calc
    f (-1) = -1 + Real.exp (-1) := by rfl
    _ = 1 / Real.exp 1 - 1 := by
      rw [Real.exp_neg]
      ring
theorem gap9 : 1 / Real.exp 1 - 1 < 0 := by
  have he : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  have hd : (1 : ℝ) / Real.exp 1 < 1 :=
    (div_lt_one hp).2 he
  linarith
theorem gap10 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (-1 : ℝ) 0 ∧ f ξ = 0 := by
  have hcont : Continuous f := by
    simpa [f] using continuous_id.add Real.continuous_exp
  have hmem : (0 : ℝ) ∈ Set.Icc (f (-1)) (f 0) := by
    rw [gap8, gap7]
    constructor <;> linarith [gap9]
  rcases
      (intermediate_value_Icc (f := f) (a := (-1 : ℝ)) (b := 0)
        (by norm_num) hcont.continuousOn) hmem with
    ⟨ξ, hξ, hzero⟩
  have hleft : (-1 : ℝ) < ξ := by
    apply lt_of_le_of_ne hξ.1
    intro heq
    subst ξ
    rw [gap8] at hzero
    linarith [gap9]
  have hright : ξ < 0 := by
    apply lt_of_le_of_ne hξ.2
    intro heq
    subst ξ
    rw [gap7] at hzero
    norm_num at hzero
  have hmono : StrictMono f := by
    intro a b hab
    dsimp [f]
    exact add_lt_add hab (Real.exp_lt_exp.mpr hab)
  refine ⟨ξ, ⟨⟨hleft, hright⟩, hzero⟩, ?_⟩
  intro y hy
  apply hmono.injective
  rw [hy.2, hzero]
theorem gap11 : approximant 1 = -0.5 := by
  rfl
theorem gap12 : approximant 2 = -0.56631 := by
  rfl
theorem gap13 : approximant 3 = -0.567132 := by
  rfl
theorem gap14 : approximant 4 = -0.567145 := by
  rfl
theorem gap15 :
    ∃ ξ : ℝ, ξ ∈ Set.Ioo (-1 : ℝ) 0 ∧ f ξ = 0 ∧
      |approximant 4 - ξ| ≤ |f (-0.567145)| / (1 + Real.exp (-1)) := by
  rcases gap10.exists with ⟨ξ, hξ, hzero⟩
  refine ⟨ξ, hξ, hzero, ?_⟩
  rw [gap14]
  have hmpos : 0 < 1 + Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  by_cases hx : (-0.567145 : ℝ) ≤ ξ
  · have hd : 0 ≤ ξ - (-0.567145 : ℝ) := sub_nonneg.mpr hx
    have hbase : Real.exp (-1) ≤ Real.exp (-0.567145) := by
      exact (Real.exp_le_exp).2 (by norm_num)
    have ht := Real.add_one_le_exp (ξ - (-0.567145 : ℝ))
    have hmul := mul_le_mul_of_nonneg_left ht
      (le_of_lt (Real.exp_pos (-0.567145)))
    have hbaseMul :
        Real.exp (-1) * (ξ - (-0.567145 : ℝ)) ≤
          Real.exp (-0.567145) * (ξ - (-0.567145 : ℝ)) :=
      mul_le_mul_of_nonneg_right hbase hd
    have harg :
        ξ = (-0.567145 : ℝ) + (ξ - (-0.567145 : ℝ)) := by
      ring
    have hexp :
        Real.exp ξ =
          Real.exp (-0.567145) * Real.exp (ξ - (-0.567145 : ℝ)) := by
      calc
        Real.exp ξ =
            Real.exp ((-0.567145 : ℝ) + (ξ - (-0.567145 : ℝ))) :=
          congrArg Real.exp harg
        _ = Real.exp (-0.567145) *
            Real.exp (ξ - (-0.567145 : ℝ)) :=
          Real.exp_add _ _
    have hmain :
        (1 + Real.exp (-1)) * (ξ - (-0.567145 : ℝ)) ≤
          f ξ - f (-0.567145) := by
      dsimp [f]
      rw [hexp]
      nlinarith [hmul, hbaseMul]
    have hfx : f (-0.567145) ≤ 0 := by
      nlinarith [hmain]
    apply (le_div_iff₀ hmpos).2
    rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos hfx]
    nlinarith [hmain]
  · have hξx : ξ ≤ (-0.567145 : ℝ) := le_of_lt (lt_of_not_ge hx)
    have hd : 0 ≤ (-0.567145 : ℝ) - ξ := sub_nonneg.mpr hξx
    have hbase : Real.exp (-1) ≤ Real.exp ξ := by
      exact (Real.exp_le_exp).2 (le_of_lt hξ.1)
    have ht := Real.add_one_le_exp ((-0.567145 : ℝ) - ξ)
    have hmul := mul_le_mul_of_nonneg_left ht
      (le_of_lt (Real.exp_pos ξ))
    have hbaseMul :
        Real.exp (-1) * ((-0.567145 : ℝ) - ξ) ≤
          Real.exp ξ * ((-0.567145 : ℝ) - ξ) :=
      mul_le_mul_of_nonneg_right hbase hd
    have harg :
        (-0.567145 : ℝ) = ξ + ((-0.567145 : ℝ) - ξ) := by
      ring
    have hexp :
        Real.exp (-0.567145) =
          Real.exp ξ * Real.exp ((-0.567145 : ℝ) - ξ) := by
      calc
        Real.exp (-0.567145) =
            Real.exp (ξ + ((-0.567145 : ℝ) - ξ)) :=
          congrArg Real.exp harg
        _ = Real.exp ξ * Real.exp ((-0.567145 : ℝ) - ξ) :=
          Real.exp_add _ _
    have hmain :
        (1 + Real.exp (-1)) * ((-0.567145 : ℝ) - ξ) ≤
          f (-0.567145) - f ξ := by
      dsimp [f]
      rw [hexp]
      nlinarith [hmul, hbaseMul]
    have hfx : 0 ≤ f (-0.567145) := by
      nlinarith [hmain]
    apply (le_div_iff₀ hmpos).2
    rw [abs_of_nonneg (sub_nonneg.mpr hξx), abs_of_nonneg hfx]
    nlinarith [hmain]
theorem gap16 :
    |f (-0.567145)| / (1 + Real.exp (-1)) < 10 ^ (-5 : ℤ) := by
  have hmpos : 0 < 1 + Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  have hmone : 1 < 1 + Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  have hhalf :
      |f (-0.567145)| / (1 + Real.exp (-1)) < (5 : ℝ) / 1000000 := by
    apply (div_lt_iff₀ hmpos).2
    have hr := residual_bound
    nlinarith [abs_nonneg (f (-0.567145))]
  have hz : (10 : ℝ) ^ (-5 : ℤ) = (1 : ℝ) / 100000 := by
    norm_num
  rw [hz]
  nlinarith
theorem gap17 : ApproxRoot (approximant 4) (10 ^ (-5 : ℤ)) := by
  rcases gap15 with ⟨ξ, hξ, hzero, herr⟩
  refine ⟨ξ, hξ, hzero, ?_⟩
  exact lt_of_le_of_lt herr gap16
theorem gap18 : ApproxRoot (-0.56715) (10 ^ (-5 : ℤ)) := by
  rcases gap15 with ⟨ξ, hξ, hzero, herr⟩
  refine ⟨ξ, hξ, hzero, ?_⟩
  have hmpos : 0 < 1 + Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  have hmone : 1 < 1 + Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  have hhalf :
      |f (-0.567145)| / (1 + Real.exp (-1)) < (5 : ℝ) / 1000000 := by
    apply (div_lt_iff₀ hmpos).2
    have hr := residual_bound
    nlinarith [abs_nonneg (f (-0.567145))]
  have hsamp :
      |(-0.56715 : ℝ) - approximant 4| = (5 : ℝ) / 1000000 := by
    rw [gap14]
    norm_num
  have htri :
      |(-0.56715 : ℝ) - ξ| ≤
        |(-0.56715 : ℝ) - approximant 4| + |approximant 4 - ξ| := by
    have h := abs_add_le
      ((-0.56715 : ℝ) - approximant 4) (approximant 4 - ξ)
    convert h using 1 <;> ring
  have hz : (10 : ℝ) ^ (-5 : ℤ) = (1 : ℝ) / 100000 := by
    norm_num
  rw [hz]
  nlinarith

end
end ProofGap.Exercise1624
