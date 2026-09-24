import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2259

noncomputable section

def domain (l : ℝ) : Set ℝ := Set.Icc (-l) l

def EvenOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ s, f (-x) = f x

def OddOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ s, f (-x) = -f x

def AntiderivativeOn (s : Set ℝ) (f F : ℝ → ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableAt ℝ F x ∧ deriv F x = f x

def centered (F : ℝ → ℝ) (x : ℝ) : ℝ := F x - F 0

private theorem constant_on_domain_of_deriv_eq_zero
    (l : ℝ) (g : ℝ → ℝ)
    (hdiff : ∀ x ∈ domain l, DifferentiableAt ℝ g x)
    (hzero : ∀ x ∈ domain l, deriv g x = 0) :
    ∀ x ∈ domain l, ∀ y ∈ domain l, g x = g y := by
  intro x hx y hy
  have forward : ∀ {a b : ℝ}, a ∈ domain l → b ∈ domain l →
      a < b → g a = g b := by
    intro a b ha hb hab
    have ha' : -l ≤ a ∧ a ≤ l := by
      simpa [domain] using ha
    have hb' : -l ≤ b ∧ b ≤ l := by
      simpa [domain] using hb
    have hcont : ContinuousOn g (Set.Icc a b) := by
      intro z hz
      have hz' : a ≤ z ∧ z ≤ b := by
        simpa only [Set.mem_Icc] using hz
      apply (hdiff z ?_).continuousAt.continuousWithinAt
      simp only [domain, Set.mem_Icc]
      exact ⟨le_trans ha'.1 hz'.1, le_trans hz'.2 hb'.2⟩
    have hdif : DifferentiableOn ℝ g (Set.Ioo a b) := by
      intro z hz
      have hz' : a < z ∧ z < b := by
        simpa only [Set.mem_Ioo] using hz
      apply (hdiff z ?_).differentiableWithinAt
      simp only [domain, Set.mem_Icc]
      exact
        ⟨le_trans ha'.1 (le_of_lt hz'.1),
          le_trans (le_of_lt hz'.2) hb'.2⟩
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope g hab hcont hdif
    have hc' : a < c ∧ c < b := by
      simpa only [Set.mem_Ioo] using hc
    have hcdom : c ∈ domain l := by
      simp only [domain, Set.mem_Icc]
      exact
        ⟨le_trans ha'.1 (le_of_lt hc'.1),
          le_trans (le_of_lt hc'.2) hb'.2⟩
    have hslope : (g b - g a) / (b - a) = 0 := by
      rw [← hcder]
      exact hzero c hcdom
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    field_simp [hba] at hslope
    have hslope' : g b - g a = 0 := by
      simpa using hslope
    exact (sub_eq_zero.mp hslope').symm
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact forward hx hy hxy
  · exact congrArg g hxy
  · exact (forward hy hx hyx).symm

theorem gap1 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F) (x : ℝ) (hx : x ∈ domain l) :
    f x = deriv F x := by
  exact (hF x hx).2.symm

theorem gap2 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (heven : EvenOn (domain l) f) (x : ℝ) (hx : x ∈ domain l) :
    f (-x) = -deriv (fun y : ℝ => F (-y)) x := by
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have hnx : -x ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  have hneg :
      HasDerivAt (fun y : ℝ => F (-y)) (-(deriv F (-x))) x := by
    simpa using
      ((hF (-x) hnx).1.hasDerivAt.comp x ((hasDerivAt_id x).neg))
  rw [hneg.deriv, (hF (-x) hnx).2]
  ring

theorem gap3 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (heven : EvenOn (domain l) f) (x : ℝ) (hx : x ∈ domain l) :
    deriv (fun y : ℝ => F y + F (-y)) x = 0 := by
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have hnx : -x ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  have hneg :
      HasDerivAt (fun y : ℝ => F (-y)) (-(deriv F (-x))) x := by
    simpa using
      ((hF (-x) hnx).1.hasDerivAt.comp x ((hasDerivAt_id x).neg))
  have hsum :
      HasDerivAt (fun y : ℝ => F y + F (-y))
        (deriv F x + -(deriv F (-x))) x :=
    (hF x hx).1.hasDerivAt.add hneg
  rw [hsum.deriv, (hF x hx).2, (hF (-x) hnx).2, heven x hx]
  ring

theorem gap4 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (heven : EvenOn (domain l) f) :
    ∃ C₁ : ℝ, ∀ x ∈ domain l, F x + F (-x) = C₁ := by
  let G : ℝ → ℝ := fun x => F x + F (-x)
  have hdiff : ∀ x ∈ domain l, DifferentiableAt ℝ G x := by
    intro x hx
    have hbounds : -l ≤ x ∧ x ≤ l := by
      simpa [domain] using hx
    have hnx : -x ∈ domain l := by
      simp only [domain, Set.mem_Icc]
      constructor <;> linarith
    have hneg :
        HasDerivAt (fun y : ℝ => F (-y)) (-(deriv F (-x))) x := by
      simpa using
        ((hF (-x) hnx).1.hasDerivAt.comp x ((hasDerivAt_id x).neg))
    exact (hF x hx).1.add hneg.differentiableAt
  have hzero : ∀ x ∈ domain l, deriv G x = 0 := by
    intro x hx
    exact gap3 l f F hF heven x hx
  refine ⟨2 * F 0, ?_⟩
  intro x hx
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have h0 : 0 ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  have heq :=
    constant_on_domain_of_deriv_eq_zero l G hdiff hzero x hx 0 h0
  simpa [G, two_mul] using heq

theorem gap5 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (heven : EvenOn (domain l) f) :
    ∃ C₁ : ℝ, C₁ = 2 * F 0 ∧
      ∀ x ∈ domain l, F x + F (-x) = C₁ := by
  obtain ⟨C, hC⟩ := gap4 l f F hF heven
  refine ⟨2 * F 0, rfl, ?_⟩
  intro x hx
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have h0 : 0 ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  calc
    F x + F (-x) = C := hC x hx
    _ = F 0 + F (-0) := (hC 0 h0).symm
    _ = 2 * F 0 := by ring

theorem gap6 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (heven : EvenOn (domain l) f) :
    OddOn (domain l) (centered F) := by
  obtain ⟨C, hC, hsymm⟩ := gap5 l f F hF heven
  intro x hx
  have hs := hsymm x hx
  rw [hC] at hs
  dsimp [centered]
  linarith

theorem gap7 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (hodd : OddOn (domain l) f) :
    ∃ C₂ : ℝ, ∀ x ∈ domain l, F x - F (-x) = C₂ := by
  let G : ℝ → ℝ := fun x => F x - F (-x)
  have hdiff : ∀ x ∈ domain l, DifferentiableAt ℝ G x := by
    intro x hx
    have hbounds : -l ≤ x ∧ x ≤ l := by
      simpa [domain] using hx
    have hnx : -x ∈ domain l := by
      simp only [domain, Set.mem_Icc]
      constructor <;> linarith
    have hneg :
        HasDerivAt (fun y : ℝ => F (-y)) (-(deriv F (-x))) x := by
      simpa using
        ((hF (-x) hnx).1.hasDerivAt.comp x ((hasDerivAt_id x).neg))
    exact (hF x hx).1.sub hneg.differentiableAt
  have hzero : ∀ x ∈ domain l, deriv G x = 0 := by
    intro x hx
    have hbounds : -l ≤ x ∧ x ≤ l := by
      simpa [domain] using hx
    have hnx : -x ∈ domain l := by
      simp only [domain, Set.mem_Icc]
      constructor <;> linarith
    have hneg :
        HasDerivAt (fun y : ℝ => F (-y)) (-(deriv F (-x))) x := by
      simpa using
        ((hF (-x) hnx).1.hasDerivAt.comp x ((hasDerivAt_id x).neg))
    have hsub :
        HasDerivAt (fun y : ℝ => F y - F (-y))
          (deriv F x - (-(deriv F (-x)))) x :=
      (hF x hx).1.hasDerivAt.sub hneg
    rw [hsub.deriv, (hF x hx).2, (hF (-x) hnx).2, hodd x hx]
    ring
  refine ⟨0, ?_⟩
  intro x hx
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have h0 : 0 ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  have heq :=
    constant_on_domain_of_deriv_eq_zero l G hdiff hzero x hx 0 h0
  simpa [G] using heq

theorem gap8 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (hodd : OddOn (domain l) f) :
    ∃ C₂ : ℝ, C₂ = 0 ∧
      ∀ x ∈ domain l, F x - F (-x) = C₂ := by
  obtain ⟨C, hC⟩ := gap7 l f F hF hodd
  refine ⟨0, rfl, ?_⟩
  intro x hx
  have hbounds : -l ≤ x ∧ x ≤ l := by
    simpa [domain] using hx
  have h0 : 0 ∈ domain l := by
    simp only [domain, Set.mem_Icc]
    constructor <;> linarith
  calc
    F x - F (-x) = C := hC x hx
    _ = F 0 - F (-0) := (hC 0 h0).symm
    _ = 0 := by ring

theorem gap9 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (hodd : OddOn (domain l) f) :
    EvenOn (domain l) F := by
  obtain ⟨C, hC0, hC⟩ := gap8 l f F hF hodd
  intro x hx
  have hs := hC x hx
  rw [hC0] at hs
  exact (sub_eq_zero.mp hs).symm

theorem gap10 (l : ℝ) (f F : ℝ → ℝ)
    (hF : AntiderivativeOn (domain l) f F)
    (hodd : OddOn (domain l) f) (C : ℝ) :
    EvenOn (domain l) (fun x => F x + C) := by
  have hFeven := gap9 l f F hF hodd
  intro x hx
  change F (-x) + C = F x + C
  rw [hFeven x hx]

theorem gap11 (l : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (EvenOn (domain l) f →
        ∃ F : ℝ → ℝ,
          AntiderivativeOn (domain l) f F ∧ OddOn (domain l) F) ∧
      (OddOn (domain l) f →
        ∀ F : ℝ → ℝ,
          AntiderivativeOn (domain l) f F → EvenOn (domain l) F) := by
  constructor
  · intro heven
    let A : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
    have hA : ∀ x : ℝ, HasDerivAt A (f x) x := by
      intro x
      simpa only [A] using
        (intervalIntegral.integral_hasDerivAt_right
          (hf.intervalIntegrable 0 x)
          hf.stronglyMeasurable.stronglyMeasurableAtFilter
          hf.continuousAt)
    have hantiA : AntiderivativeOn (domain l) f A := by
      intro x hx
      exact ⟨(hA x).differentiableAt, (hA x).deriv⟩
    have hantiCentered : AntiderivativeOn (domain l) f (centered A) := by
      intro x hx
      have hc : HasDerivAt (centered A) (f x) x := by
        change HasDerivAt (fun y : ℝ => A y - A 0) (f x) x
        exact (hA x).sub_const (A 0)
      exact ⟨hc.differentiableAt, hc.deriv⟩
    exact ⟨centered A, hantiCentered, gap6 l f A hantiA heven⟩
  · intro hodd F hanti
    exact gap9 l f F hanti hodd

end

end ProofGap.Exercise2259
