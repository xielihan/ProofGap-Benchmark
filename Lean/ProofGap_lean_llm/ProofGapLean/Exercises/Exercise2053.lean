import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2053
noncomputable section

def l₁ (eig : Fin 2 → ℝ) := eig 0
def l₂ (eig : Fin 2 → ℝ) := eig 1
def denom (a b c x : ℝ) :=
  a * Real.sin x ^ 2 + 2 * b * Real.sin x * Real.cos x + c * Real.cos x ^ 2
def numerator (a₁ b₁ x : ℝ) := a₁ * Real.sin x + b₁ * Real.cos x
def u (a b eig x : ℝ) := (a - eig) * Real.sin x + b * Real.cos x
def k (a eig : ℝ) := 1 / (a - eig)
def coeffA (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) :=
  -(a₁ * (l₁ eig - l₂ eig) + b * b₁ + a₁ * (a - l₁ eig)) /
    (b * (l₁ eig - l₂ eig))
def coeffB (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) :=
  (b * b₁ + a₁ * (a - l₁ eig)) / (b * (l₁ eig - l₂ eig))
def CoeffIdentity (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) (A B : ℝ) : Prop :=
  ∀ x, numerator a₁ b₁ x =
    A * deriv (u a b (l₁ eig)) x + B * deriv (u a b (l₂ eig)) x
def integrand (a b c a₁ b₁ x : ℝ) := numerator a₁ b₁ x / denom a b c x
def mode (a b eig x : ℝ) :=
  deriv (u a b eig) x / (k a eig * u a b eig x ^ 2 + eig)
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ModeFamily (U : Set ℝ) (a b c a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U (mode a b (l₁ eig)),
    ∃ Q ∈ Family U (mode a b (l₂ eig)), ∃ C₀, ∀ x ∈ U,
      F x = coeffA a b a₁ b₁ eig * P x +
        coeffB a b a₁ b₁ eig * Q x + C₀}
def EigenData (a b c : ℝ) (eig : Fin 2 → ℝ) : Prop :=
  (∀ i, (a - eig i) * (c - eig i) - b ^ 2 = 0) ∧
    l₁ eig ≠ l₂ eig ∧ (∀ i, a - eig i ≠ 0)
def Regular (U : Set ℝ) (a b c : ℝ) (eig : Fin 2 → ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, denom a b c x ≠ 0 ∧
      k a (l₁ eig) * u a b (l₁ eig) x ^ 2 + l₁ eig ≠ 0 ∧
      k a (l₂ eig) * u a b (l₂ eig) x ^ 2 + l₂ eig ≠ 0)

private theorem deriv_u_eq (a b e x : ℝ) :
    deriv (u a b e) x = (a - e) * Real.cos x - b * Real.sin x := by
  have hdu : HasDerivAt (u a b e)
      ((a - e) * Real.cos x - b * Real.sin x) x := by
    simpa only [u, mul_neg, sub_eq_add_neg] using
      ((Real.hasDerivAt_sin x).const_mul (a - e)).add
        ((Real.hasDerivAt_cos x).const_mul b)
  exact hdu.deriv

private theorem continuousAt_mode (a b e x : ℝ)
    (hden : k a e * u a b e x ^ 2 + e ≠ 0) :
    ContinuousAt (mode a b e) x := by
  unfold mode
  simp_rw [deriv_u_eq]
  apply ContinuousAt.div
  · fun_prop
  · unfold k u
    fun_prop
  · exact hden

private theorem exists_primitive_on_open_preconnected
    (U : Set ℝ) (hopen : IsOpen U) (hpre : IsPreconnected U)
    (f : ℝ → ℝ) (hcont : ContinuousOn f U) :
    ∃ F : ℝ → ℝ, ∀ x ∈ U, HasDerivAt F (f x) x := by
  by_cases hU : U.Nonempty
  · obtain ⟨z, hz⟩ := hU
    refine ⟨fun x => ∫ t in z..x, f t, ?_⟩
    intro x hx
    have hcx : ContinuousAt f x :=
      (hcont x hx).continuousAt (hopen.mem_nhds hx)
    have hseg : Set.uIcc z x ⊆ U :=
      (isPreconnected_iff_ordConnected.mp hpre).uIcc_subset hz hx
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hcont.mono hseg).intervalIntegrable
    · apply ContinuousAt.stronglyMeasurableAtFilter hopen
      · intro y hy
        exact (hcont y hy).continuousAt (hopen.mem_nhds hy)
      · exact hx
    · exact hcx
  · refine ⟨fun _ : ℝ => 0, ?_⟩
    intro x hx
    exact (hU ⟨x, hx⟩).elim

private theorem hasDerivAt_congr_of_eqOn_open
    {U : Set ℝ} (hopen : IsOpen U) {x : ℝ} (hx : x ∈ U)
    {f g : ℝ → ℝ} {f' : ℝ} (hg : HasDerivAt g f' x)
    (hfg : ∀ y ∈ U, f y = g y) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact hfg y hy

theorem gap1 (a b c : ℝ) (eig : Fin 2 → ℝ) (heig : EigenData a b c eig) :
    ∀ i, (a - eig i) * (c - eig i) - b ^ 2 = 0 := by
  exact heig.1
theorem gap2 (a b c x : ℝ) (eig : Fin 2 → ℝ) (heig : EigenData a b c eig) :
    ∀ i, denom a b c x = k a (eig i) * u a b (eig i) x ^ 2 + eig i := by
  intro i
  have hchar := heig.1 i
  have hne := heig.2.2 i
  have hcsub : c - eig i = b ^ 2 / (a - eig i) := by
    apply (eq_div_iff hne).2
    nlinarith [hchar]
  have hc : c = eig i + b ^ 2 / (a - eig i) := by
    linarith
  unfold denom k u
  rw [hc]
  calc
    a * Real.sin x ^ 2 + 2 * b * Real.sin x * Real.cos x +
          (eig i + b ^ 2 / (a - eig i)) * Real.cos x ^ 2 =
        ((a - eig i) * Real.sin x + b * Real.cos x) ^ 2 / (a - eig i) +
          eig i * (Real.sin x ^ 2 + Real.cos x ^ 2) := by
            field_simp [hne] <;> ring
    _ = 1 / (a - eig i) *
          ((a - eig i) * Real.sin x + b * Real.cos x) ^ 2 + eig i := by
            rw [Real.sin_sq_add_cos_sq]
            ring
theorem gap3 (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) (hb : b ≠ 0)
    (heig : l₁ eig ≠ l₂ eig) :
    -b * (coeffA a b a₁ b₁ eig + coeffB a b a₁ b₁ eig) = a₁ := by
  have hdiff : l₁ eig - l₂ eig ≠ 0 := sub_ne_zero.mpr heig
  unfold coeffA coeffB
  field_simp [hb, hdiff] <;> ring
theorem gap4 (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) (hb : b ≠ 0)
    (heig : l₁ eig ≠ l₂ eig) :
    coeffA a b a₁ b₁ eig * (a - l₁ eig) +
      coeffB a b a₁ b₁ eig * (a - l₂ eig) = b₁ := by
  have hdiff : l₁ eig - l₂ eig ≠ 0 := sub_ne_zero.mpr heig
  unfold coeffA coeffB
  field_simp [hb, hdiff] <;> ring
theorem gap5 (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) :
    coeffA a b a₁ b₁ eig =
      -(a₁ * (l₁ eig - l₂ eig) + b * b₁ + a₁ * (a - l₁ eig)) /
        (b * (l₁ eig - l₂ eig)) := by
  rfl
theorem gap6 (a b a₁ b₁ : ℝ) (eig : Fin 2 → ℝ) :
    coeffB a b a₁ b₁ eig =
      (b * b₁ + a₁ * (a - l₁ eig)) / (b * (l₁ eig - l₂ eig)) := by
  rfl
theorem gap7 (U : Set ℝ) (a b c a₁ b₁ : ℝ) (eig : Fin 2 → ℝ)
    (hb : b ≠ 0) (heig : EigenData a b c eig) (hU : Regular U a b c eig) :
    Family U (integrand a b c a₁ b₁) = ModeFamily U a b c a₁ b₁ eig := by
  let A := coeffA a b a₁ b₁ eig
  let B := coeffB a b a₁ b₁ eig
  have hcoeff₁ : -b * (A + B) = a₁ := by
    simpa only [A, B] using gap3 a b a₁ b₁ eig hb heig.2.1
  have hcoeff₂ : A * (a - l₁ eig) + B * (a - l₂ eig) = b₁ := by
    simpa only [A, B] using gap4 a b a₁ b₁ eig hb heig.2.1
  have hpoint : ∀ x ∈ U,
      integrand a b c a₁ b₁ x =
        A * mode a b (l₁ eig) x + B * mode a b (l₂ eig) x := by
    intro x hx
    have hd₁ : denom a b c x =
        k a (l₁ eig) * u a b (l₁ eig) x ^ 2 + l₁ eig := by
      simpa only [l₁] using (gap2 a b c x eig heig (0 : Fin 2))
    have hd₂ : denom a b c x =
        k a (l₂ eig) * u a b (l₂ eig) x ^ 2 + l₂ eig := by
      simpa only [l₂] using (gap2 a b c x eig heig (1 : Fin 2))
    have hnum : numerator a₁ b₁ x =
        A * deriv (u a b (l₁ eig)) x +
          B * deriv (u a b (l₂ eig)) x := by
      rw [deriv_u_eq, deriv_u_eq]
      calc
        numerator a₁ b₁ x =
            a₁ * Real.sin x + b₁ * Real.cos x := rfl
        _ = (-b * (A + B)) * Real.sin x +
              (A * (a - l₁ eig) + B * (a - l₂ eig)) * Real.cos x := by
                rw [hcoeff₁, hcoeff₂]
        _ = A * ((a - l₁ eig) * Real.cos x - b * Real.sin x) +
              B * ((a - l₂ eig) * Real.cos x - b * Real.sin x) := by
                ring
    unfold integrand mode
    rw [← hd₁, ← hd₂, hnum]
    ring
  have hopen := hU.1
  have hpre := hU.2.1
  have hc₁ : ContinuousOn (mode a b (l₁ eig)) U := by
    intro x hx
    exact (continuousAt_mode a b (l₁ eig) x
      (hU.2.2 x hx).2.1).continuousWithinAt
  have hc₂ : ContinuousOn (mode a b (l₂ eig)) U := by
    intro x hx
    exact (continuousAt_mode a b (l₂ eig) x
      (hU.2.2 x hx).2.2).continuousWithinAt
  obtain ⟨P, hP⟩ := exists_primitive_on_open_preconnected U hopen hpre
    (mode a b (l₁ eig)) hc₁
  obtain ⟨Q, hQ⟩ := exists_primitive_on_open_preconnected U hopen hpre
    (mode a b (l₂ eig)) hc₂
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand a b c a₁ b₁ x) x at hF
    change ∃ P ∈ Family U (mode a b (l₁ eig)),
      ∃ Q ∈ Family U (mode a b (l₂ eig)), ∃ C₀, ∀ x ∈ U,
        F x = coeffA a b a₁ b₁ eig * P x +
          coeffB a b a₁ b₁ eig * Q x + C₀
    by_cases hneU : U.Nonempty
    · obtain ⟨z, hz⟩ := hneU
      let G := fun y => F y - (A * P y + B * Q y)
      have hG : ∀ x ∈ U, HasDerivAt G 0 x := by
        intro x hx
        dsimp [G]
        convert (hF x hx).sub
          (((hP x hx).const_mul A).add ((hQ x hx).const_mul B)) using 1
        rw [hpoint x hx]
        ring
      have hdiff : DifferentiableOn ℝ G U := by
        intro x hx
        exact (hG x hx).differentiableAt.differentiableWithinAt
      have hdzero : ∀ x ∈ U, deriv G x = 0 := by
        intro x hx
        exact (hG x hx).deriv
      refine ⟨P, hP, Q, hQ, G z, ?_⟩
      intro x hx
      have heq : G x = G z :=
        hopen.is_const_of_deriv_eq_zero hpre hdiff hdzero hx hz
      calc
        F x = A * P x + B * Q x + G x := by
          dsimp [G]
          ring
        _ = A * P x + B * Q x + G z := by rw [heq]
    · refine ⟨P, hP, Q, hQ, 0, ?_⟩
      intro x hx
      exact (hneU ⟨x, hx⟩).elim
  · rintro ⟨P, hP, Q, hQ, C₀, hrepr⟩
    change ∀ x ∈ U, HasDerivAt F (integrand a b c a₁ b₁ x) x
    intro x hx
    apply hasDerivAt_congr_of_eqOn_open hopen hx
      (g := fun y => A * P y + B * Q y + C₀)
    · rw [hpoint x hx]
      exact (((hP x hx).const_mul A).add
        ((hQ x hx).const_mul B)).add_const C₀
    · intro y hy
      exact hrepr y hy

end
end ProofGap.Exercise2053
