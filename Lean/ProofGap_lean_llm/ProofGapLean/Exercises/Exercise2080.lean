import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2080
noncomputable section

def square (t : ℝ) := t ^ 2
def xIntegrand (x : ℝ) := Real.cos (Real.sqrt x) ^ 2
def tIntegrand (t : ℝ) := t * (1 + Real.cos (2 * t))
def xPrimitive (x : ℝ) :=
  x / 2 + Real.sqrt x / 2 * Real.sin (2 * Real.sqrt x) +
    Real.cos (2 * Real.sqrt x) / 4
def XDomain : Set ℝ := Set.Ioi 0
def TDomain : Set ℝ := Set.Ioi 0
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def PullbackFamily (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ TDomain, G t = F (square t)}
def ScaledCosFamily :=
  {G : ℝ → ℝ | ∃ H ∈ Family TDomain (fun t => t * Real.cos t ^ 2),
    ∃ C, ∀ t ∈ TDomain, G t = 2 * H t + C}
def Parts1 := {G : ℝ → ℝ |
  ∃ H ∈ Family TDomain (fun t => t * deriv (fun u => Real.sin (2 * u)) t),
  ∃ C, ∀ t ∈ TDomain, G t = t ^ 2 / 2 + H t / 2 + C}
def Parts2 := {G : ℝ → ℝ |
  ∃ H ∈ Family TDomain (fun t => Real.sin (2 * t)), ∃ C, ∀ t ∈ TDomain,
  G t = t ^ 2 / 2 + t * Real.sin (2 * t) / 2 - H t / 2 + C}
def TPrimitive := {G : ℝ → ℝ | ∃ C, ∀ t ∈ TDomain,
  G t = t ^ 2 / 2 + t * Real.sin (2 * t) / 2 + Real.cos (2 * t) / 4 + C}
def XTranslates := {F : ℝ → ℝ | ∃ C, ∀ x ∈ XDomain, F x = xPrimitive x + C}

private theorem hasDerivAt_congr_Ioi
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ Set.Ioi 0)
    (hfg : ∀ y ∈ Set.Ioi 0, f y = g y)
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hfg y hy

theorem gap1 (t : ℝ) : square t = t ^ 2 := by
  rfl
theorem gap2 (t : ℝ) : HasDerivAt square (2 * t) t := by
  convert (hasDerivAt_id t).pow 2 using 1 <;> simp [square] <;> ring
theorem gap3 :
    PullbackFamily (Family XDomain xIntegrand) = ScaledCosFamily := by
  ext G
  constructor
  · rintro ⟨F, hF, hG⟩
    refine ⟨fun u => F (square u) / 2, ?_, 0, ?_⟩
    · intro t ht
      have hspos : square t ∈ XDomain := by
        change 0 < t ^ 2
        exact pow_pos ht 2
      have hsqrt : Real.sqrt (square t) = t := by
        rw [square, Real.sqrt_sq_eq_abs, abs_of_pos ht]
      have hd := (hF (square t) hspos).comp t (gap2 t)
      convert hd.div_const 2 using 1 <;>
        simp [Function.comp_def, xIntegrand, hsqrt] <;> ring
    · intro t ht
      rw [hG t ht]
      ring
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨fun x => 2 * H (Real.sqrt x) + C, ?_, ?_⟩
    · intro x hx
      have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      have hs0 : Real.sqrt x ≠ 0 := ne_of_gt hspos
      have hd := (hH (Real.sqrt x) hspos).comp x
        (Real.hasDerivAt_sqrt (ne_of_gt hx))
      convert (hd.const_mul 2).add_const C using 1
      dsimp [xIntegrand]
      field_simp [hs0] <;> ring
    · intro t ht
      have hsqrt : Real.sqrt (square t) = t := by
        rw [square, Real.sqrt_sq_eq_abs, abs_of_pos ht]
      simpa [hsqrt] using hG t ht
theorem gap4 : ScaledCosFamily = Family TDomain tIntegrand := by
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    intro t ht
    have hd := ((hH t ht).const_mul 2).add_const C
    have hd' : HasDerivAt (fun u => 2 * H u + C) (tIntegrand t) t := by
      convert hd using 1
      change t * (1 + Real.cos (2 * t)) = 2 * (t * Real.cos t ^ 2)
      rw [Real.cos_two_mul] <;> ring
    exact hasDerivAt_congr_Ioi ht hG hd'
  · intro hG
    refine ⟨fun u => G u / 2, ?_, 0, ?_⟩
    · intro t ht
      have hd := (hG t ht).div_const 2
      convert hd using 1
      change t * Real.cos t ^ 2 = t * (1 + Real.cos (2 * t)) / 2
      rw [Real.cos_two_mul] <;> ring
    · intro t ht
      ring
theorem gap5 :
    PullbackFamily (Family XDomain xIntegrand) = Family TDomain tIntegrand := by
  exact gap3.trans gap4
theorem gap6 : PullbackFamily (Family XDomain xIntegrand) = Parts1 := by
  rw [gap5]
  ext G
  constructor
  · intro hG
    refine ⟨fun u => 2 * G u - u ^ 2, ?_, 0, ?_⟩
    · intro t ht
      have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
          (2 * Real.cos (2 * t)) t := by
        convert (Real.hasDerivAt_sin (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;>
          simp [Function.comp_def] <;> ring
      have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
        convert (hasDerivAt_id t).pow 2 using 1 <;> simp <;> ring
      have hd := ((hG t ht).const_mul 2).sub hsq
      convert hd using 1
      change t * deriv (fun u => Real.sin (2 * u)) t =
        2 * (t * (1 + Real.cos (2 * t))) - 2 * t
      rw [hsin.deriv, Real.cos_two_mul] <;> ring
    · intro t ht
      ring
  · rintro ⟨H, hH, C, hG⟩
    intro t ht
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
        (2 * Real.cos (2 * t)) t := by
      convert (Real.hasDerivAt_sin (2 * t)).comp t
        ((hasDerivAt_id t).const_mul 2) using 1 <;>
        simp [Function.comp_def] <;> ring
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;> simp <;> ring
    have hd := ((hsq.div_const 2).add ((hH t ht).div_const 2)).add_const C
    have hd' : HasDerivAt
        (fun u => u ^ 2 / 2 + H u / 2 + C) (tIntegrand t) t := by
      convert hd using 1
      change t * (1 + Real.cos (2 * t)) =
        2 * t / 2 + t * deriv (fun u => Real.sin (2 * u)) t / 2
      rw [hsin.deriv, Real.cos_two_mul] <;> ring
    exact hasDerivAt_congr_Ioi ht hG hd'
theorem gap7 : Parts1 = Parts2 := by
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨fun u => u * Real.sin (2 * u) - H u, ?_, C, ?_⟩
    · intro t ht
      have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
          (2 * Real.cos (2 * t)) t := by
        convert (Real.hasDerivAt_sin (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;>
          simp [Function.comp_def] <;> ring
      convert ((hasDerivAt_id t).mul hsin).sub (hH t ht) using 1
      dsimp only [id]
      rw [hsin.deriv]
      ring
    · intro t ht
      rw [hG t ht]
      ring
  · rintro ⟨H, hH, C, hG⟩
    refine ⟨fun u => u * Real.sin (2 * u) - H u, ?_, C, ?_⟩
    · intro t ht
      have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
          (2 * Real.cos (2 * t)) t := by
        convert (Real.hasDerivAt_sin (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;>
          simp [Function.comp_def] <;> ring
      convert ((hasDerivAt_id t).mul hsin).sub (hH t ht) using 1
      dsimp only [id]
      rw [hsin.deriv]
      ring
    · intro t ht
      rw [hG t ht]
      ring
theorem gap8 : PullbackFamily (Family XDomain xIntegrand) = Parts2 := by
  exact gap6.trans gap7
theorem gap9 : PullbackFamily (Family XDomain xIntegrand) = TPrimitive := by
  rw [gap8]
  ext G
  constructor
  · rintro ⟨H, hH, C, hG⟩
    let q : ℝ → ℝ := fun u => H u + Real.cos (2 * u) / 2
    have hq : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt q 0 t := by
      intro t ht
      have hcos : HasDerivAt (fun u : ℝ => Real.cos (2 * u))
          (-2 * Real.sin (2 * t)) t := by
        convert (Real.hasDerivAt_cos (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;>
          simp [Function.comp_def] <;> ring
      have hd := (hH t ht).add (hcos.div_const 2)
      convert hd using 1 <;> simp [q] <;> ring
    have hdiff : DifferentiableOn ℝ q (Set.Ioi 0) := by
      intro t ht
      exact (hq t ht).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), deriv q t = 0 := by
      intro t ht
      exact (hq t ht).deriv
    have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    refine ⟨C - q 1 / 2, ?_⟩
    intro t ht
    have hqt : q t = q 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hderiv ht h1
    rw [hG t ht]
    dsimp [q] at hqt ⊢
    linarith
  · rintro ⟨C, hG⟩
    refine ⟨fun u => -Real.cos (2 * u) / 2, ?_, C, ?_⟩
    · intro t ht
      have hcos : HasDerivAt (fun u : ℝ => Real.cos (2 * u))
          (-2 * Real.sin (2 * t)) t := by
        convert (Real.hasDerivAt_cos (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;>
          simp [Function.comp_def] <;> ring
      convert hcos.neg.div_const 2 using 1 <;> ring
    · intro t ht
      rw [hG t ht]
      ring
theorem gap10 : TPrimitive =
    PullbackFamily XTranslates := by
  ext G
  constructor
  · rintro ⟨C, hG⟩
    refine ⟨fun x => xPrimitive x + C, ?_, ?_⟩
    · refine ⟨C, ?_⟩
      intro x hx
      rfl
    · intro t ht
      have htpos : 0 < t := by
        simpa [TDomain] using ht
      have hsqrt : Real.sqrt (square t) = t := by
        rw [square, Real.sqrt_sq_eq_abs, abs_of_pos htpos]
      rw [hG t ht]
      unfold xPrimitive
      dsimp only
      rw [hsqrt, gap1 t]
      ring
  · rintro ⟨F, ⟨C, hF⟩, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    have htpos : 0 < t := by
      simpa [TDomain] using ht
    have hsqdom : square t ∈ XDomain := by
      change 0 < t ^ 2
      exact pow_pos htpos 2
    have hsqrt : Real.sqrt (square t) = t := by
      rw [square, Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    rw [hG t ht, hF (square t) hsqdom]
    unfold xPrimitive
    rw [hsqrt, gap1 t] <;> ring
theorem gap11 : Family XDomain xIntegrand = XTranslates := by
  have hPB : PullbackFamily (Family XDomain xIntegrand) =
      PullbackFamily XTranslates := gap9.trans gap10
  ext F
  constructor
  · intro hF
    have hGin : (fun t => F (square t)) ∈
        PullbackFamily (Family XDomain xIntegrand) :=
      ⟨F, hF, fun t ht => rfl⟩
    rw [hPB] at hGin
    rcases hGin with ⟨F', hF', hEq⟩
    rcases hF' with ⟨C, hFC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have hsquare : square (Real.sqrt x) = x := by
      simp [square, Real.sq_sqrt (le_of_lt hx)]
    have heq := hEq (Real.sqrt x) hspos
    change F (square (Real.sqrt x)) = F' (square (Real.sqrt x)) at heq
    calc
      F x = F' x := by simpa [hsquare] using heq
      _ = xPrimitive x + C := hFC x hx
  · intro hF
    have hGin : (fun t => F (square t)) ∈ PullbackFamily XTranslates :=
      ⟨F, hF, fun t ht => rfl⟩
    rw [← hPB] at hGin
    rcases hGin with ⟨F', hF', hEq⟩
    have heq : ∀ x ∈ Set.Ioi (0 : ℝ), F x = F' x := by
      intro x hx
      have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      have hsquare : square (Real.sqrt x) = x := by
        simp [square, Real.sq_sqrt (le_of_lt hx)]
      have h := hEq (Real.sqrt x) hspos
      change F (square (Real.sqrt x)) = F' (square (Real.sqrt x)) at h
      simpa [hsquare] using h
    intro x hx
    exact hasDerivAt_congr_Ioi hx heq (hF' x hx)

end
end ProofGap.Exercise2080
