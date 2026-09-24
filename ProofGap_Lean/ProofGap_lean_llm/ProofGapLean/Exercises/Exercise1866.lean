import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1866

noncomputable section

def domain : Set ℝ := Set.Ioo (-5) 2

def integrand (x : ℝ) : ℝ := (2 * x + 3) / ((x - 2) * (x + 5))

def partialFractions (x : ℝ) : ℝ := 1 / (x - 2) + 1 / (x + 5)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ := Real.log |(x - 2) * (x + 5)|

private theorem integrand_eq_partialFractions_on (x : ℝ) (hx : x ∈ domain) :
    integrand x = partialFractions x := by
  rcases hx with ⟨hx5, hx2⟩
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx2)
  have h5 : x + 5 ≠ 0 := ne_of_gt (by linarith)
  unfold integrand partialFractions
  field_simp [h2, h5]
  ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (partialFractions x) x := by
  rcases hx with ⟨hx5, hx2⟩
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx2)
  have h5 : x + 5 ≠ 0 := ne_of_gt (by linarith)
  have hprodneg : (x - 2) * (x + 5) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hx2) (by linarith)
  have hqne : -((x - 2) * (x + 5)) ≠ 0 :=
    ne_of_gt (neg_pos.mpr hprodneg)
  have hu : HasDerivAt (fun y : ℝ => (y - 2) * (y + 5)) (2 * x + 3) x := by
    convert (((hasDerivAt_id x).sub_const 2).mul ((hasDerivAt_id x).add_const 5)) using 1 <;>
      simp only [id_eq] <;> ring
  have hq : HasDerivAt (fun y : ℝ => -((y - 2) * (y + 5))) (-(2 * x + 3)) x :=
    hu.neg
  have hlog : HasDerivAt (fun y : ℝ => Real.log (-((y - 2) * (y + 5))))
      ((-((x - 2) * (x + 5)))⁻¹ * (-(2 * x + 3))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log hqne).comp x hq
  have hcoef : (-((x - 2) * (x + 5)))⁻¹ * (-(2 * x + 3)) = partialFractions x := by
    unfold partialFractions
    field_simp [h2, h5]
    ring
  rw [hcoef] at hlog
  have hopen : IsOpen domain := by
    simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (-5 : ℝ) 2))
  have hev : primitive =ᶠ[nhds x]
      (fun y : ℝ => Real.log (-((y - 2) * (y + 5)))) :=
    Filter.mem_of_superset (hopen.mem_nhds ⟨hx5, hx2⟩) (by
      intro y hy
      have hyprod : (y - 2) * (y + 5) < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr hy.2) (by linarith [hy.1])
      change Real.log |(y - 2) * (y + 5)| =
        Real.log (-((y - 2) * (y + 5)))
      rw [abs_of_neg hyprod])
  exact hlog.congr_of_eventuallyEq hev

theorem gap1 (A B x : ℝ) (hx2 : x ≠ 2) (hx5 : x ≠ -5)
    (h : integrand x = A / (x - 2) + B / (x + 5)) :
    2 * x + 3 = A * (x + 5) + B * (x - 2) := by
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have h5 : x + 5 ≠ 0 := by
    intro hx
    apply hx5
    linarith
  unfold integrand at h
  field_simp [h2, h5] at h
  nlinarith [h]

theorem gap2 (A B : ℝ)
    (h : ∀ x, 2 * x + 3 = A * (x + 5) + B * (x - 2)) :
    7 = 7 * A := by
  have h2 := h 2
  norm_num at h2 ⊢
  linarith

theorem gap3 (A : ℝ) (h : 7 = 7 * A) : A = 1 := by
  linarith

theorem gap4 (A B : ℝ)
    (h : ∀ x, 2 * x + 3 = A * (x + 5) + B * (x - 2)) :
    -7 = -7 * B := by
  have h5 := h (-5)
  norm_num at h5 ⊢
  linarith

theorem gap5 (B : ℝ) (h : -7 = -7 * B) : B = 1 := by
  linarith

theorem gap6 :
    antiderivatives integrand = antiderivatives partialFractions := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hF⟩
    refine ⟨hFd, ?_⟩
    intro x hx
    rw [hF x hx]
    exact integrand_eq_partialFractions_on x hx
  · rintro ⟨hFd, hF⟩
    refine ⟨hFd, ?_⟩
    intro x hx
    rw [hF x hx]
    exact (integrand_eq_partialFractions_on x hx).symm

theorem gap7 :
    antiderivatives partialFractions = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hFderiv⟩
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (-5 : ℝ) 2))
    have hprimDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (hasDerivAt_primitive x hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hFd.sub hprimDiff
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFdiff : DifferentiableAt ℝ F x :=
        (hFd x hx).differentiableAt (hopen.mem_nhds hx)
      have hd := (hFdiff.hasDerivAt.sub (hasDerivAt_primitive x hx)).deriv
      rw [hFderiv x hx] at hd
      simpa using hd
    have hdiffIoo : DifferentiableOn ℝ (fun x => F x - primitive x)
        (Set.Ioo (-5 : ℝ) 2) := by
      simpa [domain] using hdiff
    have hzeroIoo : ∀ x ∈ Set.Ioo (-5 : ℝ) 2,
        deriv (fun y => F y - primitive y) x = 0 := by
      simpa [domain] using hzero
    have hconst :
        ∀ x ∈ Set.Ioo (-5 : ℝ) 2, ∀ y ∈ Set.Ioo (-5 : ℝ) 2,
          F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact isOpen_Ioo.is_const_of_deriv_eq_zero
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-5 : ℝ) 2))
        hdiffIoo hzeroIoo hx hy
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hxIoo : x ∈ Set.Ioo (-5 : ℝ) 2 := by
      simpa [domain] using hx
    have h0Ioo : (0 : ℝ) ∈ Set.Ioo (-5 : ℝ) 2 := by
      norm_num
    have hc := hconst x hxIoo 0 h0Ioo
    linarith
  · rintro ⟨C, hFC⟩
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (-5 : ℝ) 2))
    have hlocal : ∀ x ∈ domain, HasDerivAt F (partialFractions x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => hFC y hy)
      exact ((hasDerivAt_primitive x hx).add_const C).congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hlocal x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hlocal x hx).deriv

theorem gap8 : antiderivatives integrand = primitiveFamily primitive := by
  exact gap6.trans gap7

end

end ProofGap.Exercise1866
