import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2099
noncomputable section

def U : Set ℝ := Set.Ioi 0
def f (x : ℝ) := x ^ 3 * Real.log x ^ 3
def primitive (x : ℝ) :=
  x ^ 4 / 4 *
    (Real.log x ^ 3 - 3 / 4 * Real.log x ^ 2 +
      3 / 8 * Real.log x - 3 / 32)
def Family (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def ScalePower := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x ^ 3 * deriv (fun y => y ^ 4) x),
  ∃ C, ∀ x ∈ U, F x = G x / 4 + C}
def Step2 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => x ^ 3 * Real.log x ^ 2), ∃ C, ∀ x ∈ U,
  F x = x ^ 4 / 4 * Real.log x ^ 3 - 3 / 4 * G x + C}
def Step3 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x ^ 2 * deriv (fun y => y ^ 4) x),
  ∃ C, ∀ x ∈ U,
  F x = x ^ 4 / 4 * Real.log x ^ 3 - 3 / 16 * G x + C}
def Step5 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => x ^ 3 * Real.log x), ∃ C, ∀ x ∈ U,
  F x = x ^ 4 / 4 * Real.log x ^ 3 -
    3 / 16 * x ^ 4 * Real.log x ^ 2 + 3 / 8 * G x + C}
def Step6 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x * deriv (fun y => y ^ 4) x),
  ∃ C, ∀ x ∈ U,
  F x = x ^ 4 / 4 * Real.log x ^ 3 -
    3 / 16 * x ^ 4 * Real.log x ^ 2 + 3 / 32 * G x + C}
def Step8 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => x ^ 3), ∃ C, ∀ x ∈ U,
  F x = x ^ 4 / 4 * Real.log x ^ 3 -
    3 / 16 * x ^ 4 * Real.log x ^ 2 +
    3 / 32 * x ^ 4 * Real.log x - 3 / 32 * G x + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private def aux2 (x : ℝ) :=
  x ^ 4 / 4 * (Real.log x ^ 2 - 1 / 2 * Real.log x + 1 / 8)

private def aux1 (x : ℝ) :=
  x ^ 4 / 4 * (Real.log x - 1 / 4)

private def aux0 (x : ℝ) := x ^ 4 / 4

private theorem deriv_pow_four (x : ℝ) :
    deriv (fun y : ℝ => y ^ 4) x = 4 * x ^ 3 := by
  simpa using ((hasDerivAt_id x).pow 4).deriv

private theorem primitive_deriv (x : ℝ) (hx : x ∈ U) :
    HasDerivAt primitive (f x) x := by
  have hxpos : 0 < x := by simpa [U] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hlog := Real.hasDerivAt_log hx0
  unfold primitive f
  convert (hpow.div_const 4).mul
    ((((hlog.pow 3).sub ((hlog.pow 2).const_mul (3 / 4 : ℝ))).add
      (hlog.const_mul (3 / 8 : ℝ))).sub_const (3 / 32 : ℝ)) using 1 <;>
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply] <;>
    field_simp [hx0] <;> ring

private theorem aux2_deriv (x : ℝ) (hx : x ∈ U) :
    HasDerivAt aux2 (x ^ 3 * Real.log x ^ 2) x := by
  have hxpos : 0 < x := by simpa [U] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hlog := Real.hasDerivAt_log hx0
  unfold aux2
  convert (hpow.div_const 4).mul
    (((hlog.pow 2).sub (hlog.const_mul (1 / 2 : ℝ))).add_const (1 / 8 : ℝ)) using 1 <;>
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply] <;>
    field_simp [hx0] <;> ring

private theorem aux1_deriv (x : ℝ) (hx : x ∈ U) :
    HasDerivAt aux1 (x ^ 3 * Real.log x) x := by
  have hxpos : 0 < x := by simpa [U] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hlog := Real.hasDerivAt_log hx0
  unfold aux1
  convert (hpow.div_const 4).mul (hlog.sub_const (1 / 4 : ℝ)) using 1 <;>
    (try simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply]) <;>
    field_simp [hx0] <;> ring

private theorem aux0_deriv (x : ℝ) (hx : x ∈ U) :
    HasDerivAt aux0 (x ^ 3) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  unfold aux0
  convert hpow.div_const 4 using 1 <;> ring

private theorem family_eq_translates (g p : ℝ → ℝ)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    Family g = Translates p := by
  have hopen : IsOpen U := by simpa [U] using isOpen_Ioi
  have hconnected : IsPreconnected U := by simpa [U] using isPreconnected_Ioi
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let C : ℝ := F 1 - p 1
    refine ⟨C, ?_⟩
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) U := by
      intro y hy
      exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ U, deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      simpa using ((hF y hy).sub (hp y hy)).deriv
    have hone : (1 : ℝ) ∈ U := by norm_num [U]
    intro x hx
    have hconst :=
      hopen.is_const_of_deriv_eq_zero hconnected hdiff hzero hx hone
    change F x - p x = F 1 - p 1 at hconst
    change F x = p x + (F 1 - p 1)
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      apply Filter.mem_of_superset (hopen.mem_nhds hx)
      intro y hy
      exact hF y hy
    rw [heq.hasDerivAt_iff]
    exact (hp x hx).add_const C

theorem gap1 : Family f = ScalePower := by
  rw [family_eq_translates f primitive primitive_deriv]
  have hcanon : ∀ x ∈ U,
      HasDerivAt (fun y => 4 * primitive y)
        (Real.log x ^ 3 * deriv (fun y => y ^ 4) x) x := by
    intro x hx
    convert ((primitive_deriv x hx).const_mul 4) using 1
    change Real.log x ^ 3 * deriv (fun y : ℝ => y ^ 4) x =
      4 * (x ^ 3 * Real.log x ^ 3)
    rw [deriv_pow_four]
    ring
  ext F
  simp only [Translates, ScalePower, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun y => 4 * primitive y, hcanon, C, ?_⟩
    intro x hx
    rw [hF x hx]
    ring
  · rintro ⟨G, hG, C, hF⟩
    rw [family_eq_translates _ _ hcanon] at hG
    rcases hG with ⟨D, hG⟩
    refine ⟨D / 4 + C, ?_⟩
    intro x hx
    rw [hF x hx, hG x hx]
    ring
theorem gap2 : Family f = Step2 := by
  rw [family_eq_translates f primitive primitive_deriv]
  ext F
  simp only [Translates, Step2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨aux2, aux2_deriv, C, ?_⟩
    intro x hx
    rw [hF x hx]
    unfold primitive aux2
    ring
  · rintro ⟨G, hG, C, hF⟩
    rw [family_eq_translates _ _ aux2_deriv] at hG
    rcases hG with ⟨D, hG⟩
    refine ⟨C - 3 / 4 * D, ?_⟩
    intro x hx
    rw [hF x hx, hG x hx]
    unfold primitive aux2
    ring
theorem gap3 : Step2 = Step3 := by
  ext F
  simp only [Step2, Step3, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, C, hF⟩
    refine ⟨fun y => 4 * G y, ?_, C, ?_⟩
    · intro x hx
      convert (hG x hx).const_mul 4 using 1
      change Real.log x ^ 2 * deriv (fun y : ℝ => y ^ 4) x =
        4 * (x ^ 3 * Real.log x ^ 2)
      rw [deriv_pow_four]
      ring
    · intro x hx
      rw [hF x hx]
      ring
  · rintro ⟨G, hG, C, hF⟩
    refine ⟨fun y => G y / 4, ?_, C, ?_⟩
    · intro x hx
      convert (hG x hx).div_const 4 using 1
      change x ^ 3 * Real.log x ^ 2 =
        (Real.log x ^ 2 * deriv (fun y : ℝ => y ^ 4) x) / 4
      rw [deriv_pow_four]
      ring
    · intro x hx
      rw [hF x hx]
      ring
theorem gap4 : Family f = Step3 := by
  exact gap2.trans gap3
theorem gap5 : Family f = Step5 := by
  rw [family_eq_translates f primitive primitive_deriv]
  ext F
  simp only [Translates, Step5, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨aux1, aux1_deriv, C, ?_⟩
    intro x hx
    rw [hF x hx]
    unfold primitive aux1
    ring
  · rintro ⟨G, hG, C, hF⟩
    rw [family_eq_translates _ _ aux1_deriv] at hG
    rcases hG with ⟨D, hG⟩
    refine ⟨C + 3 / 8 * D, ?_⟩
    intro x hx
    rw [hF x hx, hG x hx]
    unfold primitive aux1
    ring
theorem gap6 : Step5 = Step6 := by
  ext F
  simp only [Step5, Step6, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, C, hF⟩
    refine ⟨fun y => 4 * G y, ?_, C, ?_⟩
    · intro x hx
      convert (hG x hx).const_mul 4 using 1
      change Real.log x * deriv (fun y : ℝ => y ^ 4) x =
        4 * (x ^ 3 * Real.log x)
      rw [deriv_pow_four]
      ring
    · intro x hx
      rw [hF x hx]
      ring
  · rintro ⟨G, hG, C, hF⟩
    refine ⟨fun y => G y / 4, ?_, C, ?_⟩
    · intro x hx
      convert (hG x hx).div_const 4 using 1
      change x ^ 3 * Real.log x =
        (Real.log x * deriv (fun y : ℝ => y ^ 4) x) / 4
      rw [deriv_pow_four]
      ring
    · intro x hx
      rw [hF x hx]
      ring
theorem gap7 : Family f = Step6 := by
  exact gap5.trans gap6
theorem gap8 : Family f = Step8 := by
  rw [family_eq_translates f primitive primitive_deriv]
  ext F
  simp only [Translates, Step8, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨aux0, aux0_deriv, C, ?_⟩
    intro x hx
    rw [hF x hx]
    unfold primitive aux0
    ring
  · rintro ⟨G, hG, C, hF⟩
    rw [family_eq_translates _ _ aux0_deriv] at hG
    rcases hG with ⟨D, hG⟩
    refine ⟨C - 3 / 32 * D, ?_⟩
    intro x hx
    rw [hF x hx, hG x hx]
    unfold primitive aux0
    ring
theorem gap9 : Step8 = Translates primitive := by
  calc
    Step8 = Family f := gap8.symm
    _ = Translates primitive := family_eq_translates f primitive primitive_deriv
theorem gap10 : Family f = Translates primitive := by
  exact gap8.trans gap9

end
end ProofGap.Exercise2099
