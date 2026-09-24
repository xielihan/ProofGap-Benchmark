import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2129
noncomputable section

def domain : Set ℝ := Set.Ioi 0
def t (x : ℝ) := Real.rpow x (1 / 6 : ℝ)
def integrand (x : ℝ) := 1 / (Real.sqrt x + Real.cbrt x)
def pulledBack (x : ℝ) := t x ^ 3 / (t x + 1) * deriv t x
def divided (x : ℝ) :=
  (t x ^ 2 - t x + 1 - 1 / (t x + 1)) * deriv t x
def primitiveT (x : ℝ) :=
  2 * t x ^ 3 - 3 * t x ^ 2 + 6 * t x - 6 * Real.log (1 + t x)
def primitive (x : ℝ) :=
  2 * Real.sqrt x - 3 * Real.cbrt x + 6 * Real.rpow x (1 / 6 : ℝ) -
    6 * Real.log (1 + Real.rpow x (1 / 6 : ℝ))

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def SixFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain, F x = 6 * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) : Real.sqrt x = t x ^ 3 := by
  change 0 < x at hx
  unfold t
  rw [Real.sqrt_eq_rpow]
  have hmul := Real.rpow_mul hx.le (1 / 6 : ℝ) (3 : ℝ)
  have hnat :
      Real.rpow (Real.rpow x (1 / 6 : ℝ)) (3 : ℝ) =
        (Real.rpow x (1 / 6 : ℝ)) ^ (3 : ℕ) := by
    simpa using
      (Real.rpow_natCast (Real.rpow x (1 / 6 : ℝ)) 3)
  calc
    Real.rpow x (1 / 2 : ℝ) = Real.rpow x ((1 / 6 : ℝ) * 3) := by norm_num
    _ = Real.rpow (Real.rpow x (1 / 6 : ℝ)) 3 := hmul
    _ = (Real.rpow x (1 / 6 : ℝ)) ^ (3 : ℕ) := hnat
theorem gap2 (x : ℝ) (hx : x ∈ domain) : Real.cbrt x = t x ^ 2 := by
  change 0 < x at hx
  have hc : Real.cbrt x = Real.rpow x (1 / 3 : ℝ) := by
    simp [Real.cbrt]
  rw [hc]
  unfold t
  have hmul := Real.rpow_mul hx.le (1 / 6 : ℝ) (2 : ℝ)
  have hnat :
      Real.rpow (Real.rpow x (1 / 6 : ℝ)) (2 : ℝ) =
        (Real.rpow x (1 / 6 : ℝ)) ^ (2 : ℕ) := by
    simpa using
      (Real.rpow_natCast (Real.rpow x (1 / 6 : ℝ)) 2)
  calc
    Real.rpow x (1 / 3 : ℝ) = Real.rpow x ((1 / 6 : ℝ) * 2) := by norm_num
    _ = Real.rpow (Real.rpow x (1 / 6 : ℝ)) 2 := hmul
    _ = (Real.rpow x (1 / 6 : ℝ)) ^ (2 : ℕ) := hnat
theorem gap3 (x : ℝ) (hx : x ∈ domain) : 1 = 6 * t x ^ 5 * deriv t x := by
  change 0 < x at hx
  have ht : HasDerivAt t
      ((1 / 6 : ℝ) * Real.rpow x ((1 / 6 : ℝ) - 1)) x := by
    change HasDerivAt (fun y : ℝ => Real.rpow y (1 / 6 : ℝ))
      ((1 / 6 : ℝ) * Real.rpow x ((1 / 6 : ℝ) - 1)) x
    exact Real.hasDerivAt_rpow_const (p := (1 / 6 : ℝ))
      (Or.inl hx.ne')
  have hpow : t x ^ 5 = Real.rpow x ((1 / 6 : ℝ) * 5) := by
    unfold t
    have hnat :
        Real.rpow (Real.rpow x (1 / 6 : ℝ)) (5 : ℝ) =
          (Real.rpow x (1 / 6 : ℝ)) ^ (5 : ℕ) := by
      simpa using
        (Real.rpow_natCast (Real.rpow x (1 / 6 : ℝ)) 5)
    have hmul := Real.rpow_mul hx.le (1 / 6 : ℝ) (5 : ℝ)
    exact hnat.symm.trans hmul.symm
  have hadd := Real.rpow_add hx ((1 / 6 : ℝ) * 5) ((1 / 6 : ℝ) - 1)
  rw [ht.deriv]
  symm
  calc
    6 * t x ^ 5 * ((1 / 6 : ℝ) * Real.rpow x ((1 / 6 : ℝ) - 1)) =
        Real.rpow x ((1 / 6 : ℝ) * 5) * Real.rpow x ((1 / 6 : ℝ) - 1) := by
          rw [hpow]
          ring
    _ = Real.rpow x (((1 / 6 : ℝ) * 5) + ((1 / 6 : ℝ) - 1)) := hadd.symm
    _ = 1 := by norm_num
theorem gap4 : Family integrand = SixFamily pulledBack := by
  have hscale : ∀ x ∈ domain, integrand x = 6 * pulledBack x := by
    intro x hx
    change 0 < x at hx
    have hu : 0 < t x := Real.rpow_pos_of_pos hx _
    have hu1 : t x + 1 ≠ 0 := by positivity
    have hden : t x ^ 3 + t x ^ 2 ≠ 0 := by positivity
    have hrel := gap3 x hx
    rw [integrand, pulledBack, gap1 x hx, gap2 x hx]
    field_simp [hden, hu1]
    convert hrel using 1 <;> ring
  ext F
  simp only [Family, SixFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => (1 / 6 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (1 / 6 : ℝ)
      rw [hscale x hx] at hd
      convert hd using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hxpos : 0 < x := hx
    have hmem : ∀ᶠ y in nhds x, y ∈ domain := by
      simpa [domain] using (Ioi_mem_nhds hxpos)
    have hlocal : (fun y => 6 * A y) =ᶠ[nhds x] F :=
      hmem.mono (fun y hy => (hFA y hy).symm)
    have hd : HasDerivAt (fun y => 6 * A y)
        (6 * pulledBack x) x := (hA x hx).const_mul 6
    have hdF : HasDerivAt F (6 * pulledBack x) x :=
      hlocal.hasDerivAt_iff.mp hd
    rw [hscale x hx]
    exact hdF
theorem gap5 : SixFamily pulledBack = SixFamily divided := by
  have heq : ∀ x ∈ domain, pulledBack x = divided x := by
    intro x hx
    change 0 < x at hx
    have hu : 0 < t x := Real.rpow_pos_of_pos hx _
    have hu1 : t x + 1 ≠ 0 := by positivity
    unfold pulledBack divided
    field_simp [hu1]
    ring
  ext F
  simp only [SixFamily, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    refine ⟨A, ?_, hFA⟩
    intro x hx
    simpa only [heq x hx] using hA x hx
  · rintro ⟨A, hA, hFA⟩
    refine ⟨A, ?_, hFA⟩
    intro x hx
    simpa only [heq x hx] using hA x hx
theorem gap6 : SixFamily divided = Translates primitiveT := by
  have hprim : ∀ x ∈ domain,
      HasDerivAt primitiveT (6 * divided x) x := by
    intro x hx
    change 0 < x at hx
    have htBase : HasDerivAt t
        ((1 / 6 : ℝ) * Real.rpow x ((1 / 6 : ℝ) - 1)) x := by
      change HasDerivAt (fun y : ℝ => Real.rpow y (1 / 6 : ℝ))
        ((1 / 6 : ℝ) * Real.rpow x ((1 / 6 : ℝ) - 1)) x
      exact Real.hasDerivAt_rpow_const (p := (1 / 6 : ℝ))
        (Or.inl hx.ne')
    have ht : HasDerivAt t (deriv t x) x :=
      htBase.differentiableAt.hasDerivAt
    have hne : 1 + t x ≠ 0 := by
      have : 0 < t x := Real.rpow_pos_of_pos hx _
      positivity
    have harg0 :=
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).add ht
    have harg : HasDerivAt (fun y : ℝ => 1 + t y) (deriv t x) x := by
      convert harg0 using 1 <;> simp
    have hlog : HasDerivAt (fun y => Real.log (1 + t y))
        (deriv t x / (1 + t x)) x := harg.log hne
    have hall :=
      ((((ht.pow 3).const_mul 2).sub ((ht.pow 2).const_mul 3)).add
        (ht.const_mul 6)).sub (hlog.const_mul 6)
    convert hall using 1
    unfold divided
    rw [show t x + 1 = 1 + t x by ring]
    ring
  ext F
  simp only [SixFamily, Family, Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    let H : ℝ → ℝ := fun y => 6 * A y - primitiveT y
    have hzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      dsimp [H]
      convert ((hA x hx).const_mul 6).sub (hprim x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hconn : IsPreconnected domain := by
      simpa [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hone : (1 : ℝ) ∈ domain := by norm_num [domain]
    refine ⟨F 1 - primitiveT 1, ?_⟩
    intro x hx
    have hc :=
      hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv hx hone
    dsimp [H] at hc
    rw [hFA x hx, hFA 1 hone]
    linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun y => (1 / 6 : ℝ) * (primitiveT y + C), ?_, ?_⟩
    · intro x hx
      have hd := ((hprim x hx).add_const C).const_mul (1 / 6 : ℝ)
      convert hd using 1 <;> ring
    · intro x hx
      rw [hFC x hx]
      ring
theorem gap7 : Family integrand = Translates primitiveT := by
  calc
    Family integrand = SixFamily pulledBack := gap4
    _ = SixFamily divided := gap5
    _ = Translates primitiveT := gap6
theorem gap8 : Family integrand = Translates primitive := by
  have heq : ∀ x ∈ domain, primitiveT x = primitive x := by
    intro x hx
    unfold primitiveT primitive
    rw [← gap1 x hx, ← gap2 x hx]
    rfl
  rw [gap7]
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    simpa only [heq x hx] using hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    simpa only [heq x hx] using hF x hx

end
end ProofGap.Exercise2129
