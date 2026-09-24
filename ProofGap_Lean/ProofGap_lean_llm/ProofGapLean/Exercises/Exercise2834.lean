import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2834

noncomputable section

open Filter
open scoped BigOperators Topology

def sineCoefficient (n : ℕ) : ℝ :=
  Real.sin (Real.pi / (2 : ℝ) ^ n)

def term (n : ℕ) (x : ℝ) : ℝ :=
  sineCoefficient n / x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  x ≠ 0 ∧ Summable (fun k : ℕ => term (k + 1) x)

private def angle (n : ℕ) : ℝ :=
  Real.pi / (2 : ℝ) ^ n

private theorem angle_pos (n : ℕ) : 0 < angle n := by
  unfold angle
  positivity

private theorem angle_ne_zero (n : ℕ) : angle n ≠ 0 :=
  (angle_pos n).ne'

private theorem angle_lt_pi (n : ℕ) (hn : 1 ≤ n) :
    angle n < Real.pi := by
  unfold angle
  apply div_lt_self Real.pi_pos
  exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)

private theorem sineCoefficient_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < sineCoefficient n := by
  unfold sineCoefficient
  exact Real.sin_pos_of_pos_of_lt_pi (angle_pos n) (angle_lt_pi n hn)

private theorem angle_succ_tendsto_zero :
    Tendsto (fun n : ℕ => angle (n + 1)) atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  unfold angle
  exact tendsto_const_nhds.div_atTop hpow

private theorem normalized_sine_tendsto :
    Tendsto
      (fun n : ℕ =>
        Real.sin (angle (n + 1)) / angle (n + 1))
      atTop (𝓝 1) := by
  have hequiv :=
    Real.isEquivalent_sin.comp_tendsto angle_succ_tendsto_zero
  have hne :
      ∀ᶠ n : ℕ in atTop,
        (id ∘ fun n : ℕ => angle (n + 1)) n ≠ 0 :=
    Filter.Eventually.of_forall (fun n => angle_ne_zero (n + 1))
  have hratio :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).1 hequiv
  simpa [Function.comp_def] using hratio

private theorem angle_ratio (n : ℕ) :
    angle (n + 1) / angle (n + 2) = 2 := by
  unfold angle
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp [Real.pi_ne_zero]
  norm_num [pow_add, pow_two]
  ring

private theorem sine_ratio_tendsto :
    Tendsto
      (fun n : ℕ =>
        sineCoefficient (n + 1) / sineCoefficient (n + 2))
      atTop (𝓝 2) := by
  have hnorm2 :
      Tendsto
        (fun n : ℕ =>
          Real.sin (angle (n + 2)) / angle (n + 2))
        atTop (𝓝 1) := by
    simpa [Nat.add_assoc] using
      normalized_sine_tendsto.comp (tendsto_add_atTop_nat 1)
  have hangle :
      Tendsto
        (fun n : ℕ => angle (n + 1) / angle (n + 2))
        atTop (𝓝 2) := by
    simpa only [angle_ratio] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2))
  have hproduct :=
    (normalized_sine_tendsto.div hnorm2 (by norm_num : (1 : ℝ) ≠ 0)).mul hangle
  convert hproduct using 1
  · funext n
    unfold sineCoefficient
    change
      Real.sin (angle (n + 1)) / Real.sin (angle (n + 2)) =
        (Real.sin (angle (n + 1)) / angle (n + 1) /
          (Real.sin (angle (n + 2)) / angle (n + 2))) *
            (angle (n + 1) / angle (n + 2))
    field_simp [angle_ne_zero, (sineCoefficient_pos (n + 2) (by omega)).ne']
  · norm_num

theorem gap1 :
    Tendsto
      (fun n : ℕ => |sineCoefficient (n + 1) / sineCoefficient (n + 2)|)
      atTop (𝓝 2) := by
  simpa using sine_ratio_tendsto.abs

theorem gap2 :
    Tendsto
      (fun n : ℕ => sineCoefficient (n + 1) / sineCoefficient (n + 2))
      atTop (𝓝 2) ↔
        Tendsto
          (fun n : ℕ =>
            (Real.pi / (2 : ℝ) ^ (n + 1)) /
              (Real.pi / (2 : ℝ) ^ (n + 2)))
          atTop (𝓝 2) := by
  constructor
  · intro _
    simpa [angle] using
      (show Tendsto (fun n : ℕ => angle (n + 1) / angle (n + 2))
        atTop (𝓝 2) by
          simpa only [angle_ratio] using
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)))
  · intro _
    exact sine_ratio_tendsto

theorem gap3 :
    Tendsto
      (fun n : ℕ =>
        (Real.pi / (2 : ℝ) ^ (n + 1)) /
          (Real.pi / (2 : ℝ) ^ (n + 2)))
      atTop (𝓝 2) := by
  simpa [angle] using
    (show Tendsto (fun n : ℕ => angle (n + 1) / angle (n + 2))
      atTop (𝓝 2) by
        simpa only [angle_ratio] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)))

theorem gap4 :
    Tendsto
      (fun n : ℕ => |sineCoefficient (n + 1) / sineCoefficient (n + 2)|)
      atTop (𝓝 2) := by
  exact gap1

private theorem term_as_power (n : ℕ) (x : ℝ) :
    term n x = sineCoefficient n * (1 / x) ^ n := by
  unfold term
  rw [div_eq_mul_inv, one_div, inv_pow]

private theorem term_ratio (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ‖term (n + 2) x‖ / ‖term (n + 1) x‖ =
      |1 / x| /
        |sineCoefficient (n + 1) / sineCoefficient (n + 2)| := by
  have hy : 1 / x ≠ 0 := one_div_ne_zero hx
  have hay : |1 / x| ≠ 0 := abs_ne_zero.mpr hy
  have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hc1 : sineCoefficient (n + 1) ≠ 0 :=
    (sineCoefficient_pos (n + 1) (by omega)).ne'
  have hc2 : sineCoefficient (n + 2) ≠ 0 :=
    (sineCoefficient_pos (n + 2) (by omega)).ne'
  rw [term_as_power, term_as_power, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [abs_mul, abs_pow]
  simp only [abs_div]
  field_simp [hax, hay, hc1, hc2, pow_ne_zero _ hay]
  norm_num only [abs_one]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp [hax]

private theorem term_ratio_tendsto (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖term (n + 2) x‖ / ‖term (n + 1) x‖)
      atTop (𝓝 (|1 / x| / 2)) := by
  have hrel :
      (fun n : ℕ =>
        ‖term (n + 2) x‖ / ‖term (n + 1) x‖) =
        fun n : ℕ =>
          |1 / x| /
            |sineCoefficient (n + 1) / sineCoefficient (n + 2)| := by
    funext n
    exact term_ratio x hx n
  rw [hrel]
  exact tendsto_const_nhds.div gap1 (by norm_num : (2 : ℝ) ≠ 0)

theorem gap5 :
    ∀ x : ℝ, x ≠ 0 → (|1 / x| < 2 ↔ 1 / 2 < |x|) := by
  intro x hx
  have hax : 0 < |x| := abs_pos.mpr hx
  rw [abs_div, abs_one]
  constructor
  · intro h
    have h' := (div_lt_iff₀ hax).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ hax).2
    nlinarith

theorem gap6 :
    ∀ x : ℝ, 1 / 2 < |x| →
      Summable (fun k : ℕ => |term (k + 1) x|) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hax : 0 < |x| := abs_pos.mpr hx0
  have hinv : |1 / x| < 2 := by
    rw [abs_div, abs_one]
    apply (div_lt_iff₀ hax).2
    nlinarith
  have hlimit : |1 / x| / 2 < 1 := by linarith
  have hs : Summable (fun k : ℕ => term (k + 1) x) := by
    apply summable_of_ratio_test_tendsto_lt_one hlimit
    · exact Filter.Eventually.of_forall (fun n =>
        div_ne_zero
          (sineCoefficient_pos (n + 1) (by omega)).ne'
          (pow_ne_zero _ hx0))
    · simpa [Nat.add_assoc] using term_ratio_tendsto x hx0
  exact hs.abs

theorem gap7 :
    ∀ x : ℝ, |x| < 1 / 2 → ¬ SeriesConvergesAt x := by
  intro x hx hseries
  rcases hseries with ⟨hx0, hs⟩
  have hax : 0 < |x| := abs_pos.mpr hx0
  have hinv : 2 < |1 / x| := by
    rw [abs_div, abs_one]
    apply (lt_div_iff₀ hax).2
    nlinarith
  have hlimit : 1 < |1 / x| / 2 := by linarith
  exact
    (not_summable_of_ratio_test_tendsto_gt_one hlimit
      (by simpa [Nat.add_assoc] using term_ratio_tendsto x hx0)) hs

theorem gap8 :
    Tendsto
      (fun n : ℕ => (2 : ℝ) ^ (n + 1) *
        Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)))
      atTop (𝓝 Real.pi) := by
  have hproduct :=
    (tendsto_const_nhds (x := Real.pi)).mul normalized_sine_tendsto
  convert hproduct using 1
  · funext n
    unfold angle
    field_simp [Real.pi_ne_zero]
  · norm_num

theorem gap9 :
    Real.pi ≠ 0 := by
  exact Real.pi_ne_zero

theorem gap10 :
    ¬ Tendsto
      (fun n : ℕ => (2 : ℝ) ^ (n + 1) *
        Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)))
      atTop (𝓝 0) := by
  intro hzero
  have hpi0 : Real.pi = 0 :=
    tendsto_nhds_unique gap8 hzero
  exact gap9 hpi0

private theorem abs_term_of_boundary
    (x : ℝ) (hx : |x| = 1 / 2) (n : ℕ) :
    |term (n + 1) x| =
      (2 : ℝ) ^ (n + 1) *
        Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
  unfold term
  rw [abs_div, abs_pow,
    abs_of_pos (sineCoefficient_pos (n + 1) (by omega)), hx]
  unfold sineCoefficient
  field_simp
  rw [show
    (2 : ℝ) ^ (n + 1) *
          Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) *
          (1 / 2 : ℝ) ^ (n + 1) =
        ((2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 1)) *
          Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) by ring]
  rw [← mul_pow]
  norm_num

theorem gap11 :
    ∀ x : ℝ, |x| = 1 / 2 → ¬ SeriesConvergesAt x := by
  intro x hx hseries
  have hzero :
      Tendsto (fun n : ℕ => |term (n + 1) x|)
        atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hseries.2.tendsto_atTop_zero.norm
  have hpi :
      Tendsto (fun n : ℕ => |term (n + 1) x|)
        atTop (𝓝 Real.pi) := by
    convert gap8 using 1
    funext n
    exact abs_term_of_boundary x hx n
  have hpi0 : Real.pi = 0 :=
    tendsto_nhds_unique hpi hzero
  exact gap9 hpi0

theorem gap12 :
    ∀ x : ℝ, x ∈ {y : ℝ | 1 / 2 < |y|} ↔ SeriesConvergesAt x := by
  intro x
  change (1 / 2 : ℝ) < |x| ↔ SeriesConvergesAt x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      norm_num at hx
    refine ⟨hx0, ?_⟩
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using gap6 x hx
  · intro hseries
    by_contra hnot
    have hle : |x| ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · exact (gap11 x heq) hseries
    · exact (gap7 x hlt) hseries

end

end ProofGap.Exercise2834
