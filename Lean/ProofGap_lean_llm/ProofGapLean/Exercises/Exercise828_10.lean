import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise828_10

noncomputable section

def y (x : ℝ) : ℝ := Real.arctan x
def Δy (x Δx : ℝ) : ℝ := y (x + Δx) - y x
def q (x Δx : ℝ) : ℝ := Δx / (1 + x * (x + Δx))

private theorem arctan_div_tendsto_zero :
    Filter.Tendsto (fun t : ℝ => Real.arctan t / t)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have h :=
    hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_arctan 0)
  have heq :
      (fun t : ℝ => Real.arctan t / t) = slope Real.arctan 0 := by
    funext t
    dsimp only [slope]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa using h

private theorem tan_reciprocal_tendsto_one :
    Filter.Tendsto (fun u : ℝ => u / Real.tan u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hcos0 :
      Filter.Tendsto Real.cos (nhds (0 : ℝ)) (nhds (Real.cos 0)) :=
    Real.continuous_cos.continuousAt
  have hcos : Filter.Tendsto Real.cos l (nhds 1) := by
    have h := hcos0.mono_left (show l ≤ nhds 0 from inf_le_left)
    simpa using h
  have hsin0 :
      Filter.Tendsto (fun u : ℝ => Real.sin u / u) l (nhds 1) := by
    have h :=
      hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sin 0)
    have heq :
        (fun u : ℝ => Real.sin u / u) = slope Real.sin 0 := by
      funext u
      dsimp only [slope]
      simp [div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa [l] using h
  have hsin :
      Filter.Tendsto (fun u : ℝ => u / Real.sin u) l (nhds 1) := by
    simpa [inv_div] using hsin0.inv₀ one_ne_zero
  simpa [l, Real.tan_eq_sin_div_cos, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hcos.mul hsin

theorem gap1 (x Δx : ℝ) :
    Δy x Δx / Δx = (Real.arctan (x + Δx) - Real.arctan x) / Δx := by
  rfl
theorem gap2 (x Δx : ℝ)
    (hbranch : Real.arctan (x + Δx) - Real.arctan x = Real.arctan (q x Δx)) :
    (Real.arctan (x + Δx) - Real.arctan x) / Δx =
      Real.arctan (q x Δx) / Δx := by
  rw [hbranch]
theorem gap3 (x Δx : ℝ) (hΔ : Δx ≠ 0)
    (hden : 1 + x * (x + Δx) ≠ 0) :
    Real.arctan (q x Δx) / Δx =
      (Real.arctan (q x Δx) / q x Δx) * (1 / (1 + x * (x + Δx))) := by
  unfold q
  field_simp [hΔ, hden]
theorem gap4 (x Δx : ℝ) (hΔ : Δx ≠ 0)
    (hbranch : Δy x Δx = Real.arctan (q x Δx))
    (hden : 1 + x * (x + Δx) ≠ 0) :
    Δy x Δx / Δx =
      (Real.arctan (q x Δx) / q x Δx) * (1 / (1 + x * (x + Δx))) := by
  calc
    Δy x Δx / Δx = Real.arctan (q x Δx) / Δx := by rw [hbranch]
    _ = (Real.arctan (q x Δx) / q x Δx) *
          (1 / (1 + x * (x + Δx))) := gap3 x Δx hΔ hden
theorem gap5 (x : ℝ) :
    HasDerivAt y (deriv y x) x ↔
      Filter.Tendsto (fun Δx => Δy x Δx / Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (deriv y x)) := by
  constructor
  · intro h
    let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
    have hid : Filter.Tendsto (fun t : ℝ => t) l (nhds 0) := by
      exact continuousAt_id.mono_left inf_le_left
    have hto : Filter.Tendsto (fun t : ℝ => x + t) l (nhds x) := by
      simpa using tendsto_const_nhds.add hid
    have hshift :
        Filter.Tendsto (fun t : ℝ => x + t) l
          (nhdsWithin x ({x} : Set ℝ)ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hto, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    have hs := hasDerivAt_iff_tendsto_slope.mp h
    have heq :
        (fun t : ℝ => Δy x t / t) =
          (slope y x ∘ fun t : ℝ => x + t) := by
      funext t
      dsimp only [Function.comp_apply, slope]
      simp [Δy, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact hs.comp hshift
  · intro _
    have hy : DifferentiableAt ℝ y x := by
      simpa [y] using (Real.hasDerivAt_arctan x).differentiableAt
    exact hy.hasDerivAt
theorem gap6 (x : ℝ) :
    Filter.Tendsto (fun Δx =>
      (Real.arctan (q x Δx) / q x Δx) * (1 / (1 + x * (x + Δx))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / (1 + x ^ 2))) := by
  let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hid : Filter.Tendsto (fun t : ℝ => t) l (nhds 0) := by
    exact
      (show Filter.Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0) from
        continuousAt_id).mono_left inf_le_left
  have hsum :
      Filter.Tendsto (fun t : ℝ => x + t) l (nhds (x + 0)) :=
    tendsto_const_nhds.add hid
  have hprod :
      Filter.Tendsto (fun t : ℝ => x * (x + t)) l
        (nhds (x * (x + 0))) :=
    tendsto_const_nhds.mul hsum
  have hdenraw :
      Filter.Tendsto (fun t : ℝ => 1 + x * (x + t)) l
        (nhds (1 + x * (x + 0))) :=
    tendsto_const_nhds.add hprod
  have hdenlim :
      Filter.Tendsto (fun t : ℝ => 1 + x * (x + t)) l
        (nhds (1 + x ^ 2)) := by
    simpa [pow_two] using hdenraw
  have hne : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hq0 : Filter.Tendsto (q x) l (nhds 0) := by
    simpa [q] using hid.div hdenlim hne
  have hevden : ∀ᶠ t in l, 1 + x * (x + t) ≠ 0 :=
    hdenlim.eventually (eventually_ne_nhds hne)
  have hq :
      Filter.Tendsto (q x) l (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hq0, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hevden] with t ht htden
    have ht0 : t ≠ 0 := by
      simpa using ht
    have hqt : q x t ≠ 0 := by
      simpa [q] using div_ne_zero ht0 htden
    simpa using hqt
  have ha := arctan_div_tendsto_zero.comp hq
  have hb :
      Filter.Tendsto
        (fun t : ℝ => 1 / (1 + x * (x + t))) l
        (nhds (1 / (1 + x ^ 2))) := by
    simpa only [one_div] using hdenlim.inv₀ hne
  simpa using ha.mul hb
theorem gap7 (x : ℝ) :
    deriv y x = 1 / (1 + x ^ 2) := by
  have h : HasDerivAt y (1 / (1 + x ^ 2)) x := by
    simpa [y] using Real.hasDerivAt_arctan x
  exact h.deriv
theorem gap8 (x : ℝ) :
    deriv (fun z : ℝ => Real.arctan z) x = 1 / (1 + x ^ 2) := by
  exact (Real.hasDerivAt_arctan x).deriv
theorem gap9 :
    Filter.Tendsto (fun t : ℝ => Real.arctan t / t)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) ↔
    Filter.Tendsto (fun u : ℝ => u / Real.tan u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  constructor
  · intro _
    exact tan_reciprocal_tendsto_one
  · intro _
    exact arctan_div_tendsto_zero
theorem gap10 :
    Filter.Tendsto (fun u : ℝ => u / Real.tan u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact tan_reciprocal_tendsto_one
theorem gap11 :
    Filter.Tendsto (fun t : ℝ => Real.arctan t / t)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact arctan_div_tendsto_zero

end

end ProofGap.Exercise828_10
