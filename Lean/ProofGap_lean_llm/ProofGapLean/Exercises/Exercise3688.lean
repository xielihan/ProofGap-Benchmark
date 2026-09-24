import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3688

noncomputable section

def feasible (S : ℝ) (p : ℝ × ℝ) : Prop :=
  0 < p.1 ∧ 0 < p.2 ∧ Real.pi * (p.1 ^ 2 + p.1 * p.2) = S

def volume (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.pi * p.1 ^ 2 * p.2

def critical (S r h μ : ℝ) : Prop :=
  2 * r * h - μ * (2 * r + h) = 0 ∧
    r ^ 2 - μ * r = 0 ∧
    r ^ 2 + r * h = S / Real.pi

def optimalRadius (S : ℝ) : ℝ :=
  Real.sqrt (S / (3 * Real.pi))

def candidate (S : ℝ) : ℝ × ℝ :=
  (optimalRadius S, 2 * optimalRadius S)

def maximumVolume (S : ℝ) : ℝ :=
  Real.sqrt (S ^ 3 / (27 * Real.pi))

def maximizers (S : ℝ) : Set (ℝ × ℝ) :=
  {p | feasible S p ∧ ∀ q, feasible S q → volume q ≤ volume p}

private theorem candidate_radius_data (S : ℝ) (hS : 0 < S) :
    0 < optimalRadius S ∧
      optimalRadius S ^ 2 = S / (3 * Real.pi) ∧
      3 * Real.pi * optimalRadius S ^ 2 = S := by
  have hden : 0 < (3 : ℝ) * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have hx : 0 < S / (3 * Real.pi) := div_pos hS hden
  have hpos : 0 < optimalRadius S := by
    unfold optimalRadius
    exact Real.sqrt_pos.2 hx
  have hsq : optimalRadius S ^ 2 = S / (3 * Real.pi) := by
    unfold optimalRadius
    exact Real.sq_sqrt (le_of_lt hx)
  refine ⟨hpos, hsq, ?_⟩
  rw [hsq]
  field_simp [ne_of_gt Real.pi_pos]

theorem gap1 (S r h μ : ℝ) (hS : 0 < S)
    (hfeas : feasible S (r, h)) (hcrit : critical S r h μ) :
    r = optimalRadius S := by
  rcases hfeas with ⟨hr, hh, harea⟩
  rcases hcrit with ⟨hc₁, hc₂, hc₃⟩
  have hmu : μ = r := by
    nlinarith
  rw [hmu] at hc₁
  have hhr : h = 2 * r := by
    nlinarith
  rw [hhr] at harea
  have hr_sq : r ^ 2 = S / (3 * Real.pi) := by
    apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))).2
    nlinarith [harea]
  rcases candidate_radius_data S hS with ⟨hR, hR_sq, hR_area⟩
  nlinarith

theorem gap2 (S r h μ : ℝ) (hS : 0 < S)
    (hfeas : feasible S (r, h)) (hcrit : critical S r h μ) :
    h = 2 * optimalRadius S := by
  have hr_eq := gap1 S r h μ hS hfeas hcrit
  rcases hfeas with ⟨hr, hh, harea⟩
  rcases hcrit with ⟨hc₁, hc₂, hc₃⟩
  have hmu : μ = r := by
    nlinarith
  rw [hmu] at hc₁
  have hhr : h = 2 * r := by
    nlinarith
  rw [hhr, hr_eq]

theorem gap3 (S : ℝ) (hS : 0 < S) :
    {p : ℝ × ℝ | feasible S p ∧ ∃ μ, critical S p.1 p.2 μ} =
      ({candidate S} : Set (ℝ × ℝ)) := by
  ext p
  constructor
  · rintro ⟨hp, μ, hcrit⟩
    have hr := gap1 S p.1 p.2 μ hS hp hcrit
    have hh := gap2 S p.1 p.2 μ hS hp hcrit
    have hp_eq : p = candidate S := by
      apply Prod.ext
      · simpa [candidate] using hr
      · simpa [candidate] using hh
    simpa using hp_eq
  · intro hp
    have hp_eq : p = candidate S := by
      simpa using hp
    subst p
    rcases candidate_radius_data S hS with ⟨hR, hR_sq, hR_area⟩
    refine ⟨?_, ⟨optimalRadius S, ?_⟩⟩
    · change 0 < optimalRadius S ∧
        0 < 2 * optimalRadius S ∧
        Real.pi * (optimalRadius S ^ 2 +
          optimalRadius S * (2 * optimalRadius S)) = S
      refine ⟨hR, mul_pos (by norm_num) hR, ?_⟩
      calc
        Real.pi * (optimalRadius S ^ 2 +
            optimalRadius S * (2 * optimalRadius S)) =
            3 * Real.pi * optimalRadius S ^ 2 := by ring
        _ = S := hR_area
    · change critical S (optimalRadius S)
        (2 * optimalRadius S) (optimalRadius S)
      refine ⟨by ring, by ring, ?_⟩
      apply (eq_div_iff (ne_of_gt Real.pi_pos)).2
      calc
        (optimalRadius S ^ 2 +
            optimalRadius S * (2 * optimalRadius S)) * Real.pi =
            3 * Real.pi * optimalRadius S ^ 2 := by ring
        _ = S := hR_area

theorem gap4 (S : ℝ) (hS : 0 < S) :
    candidate S ∈ maximizers S := by
  have hc_mem : candidate S ∈
      {p : ℝ × ℝ | feasible S p ∧ ∃ μ, critical S p.1 p.2 μ} := by
    rw [gap3 S hS]
    simp
  rcases hc_mem with ⟨hcfeas, μ, hccrit⟩
  change feasible S (candidate S) ∧
    ∀ q, feasible S q → volume q ≤ volume (candidate S)
  refine ⟨hcfeas, ?_⟩
  rintro ⟨r, h⟩ hq
  rcases hq with ⟨hr, hh, harea⟩
  rcases candidate_radius_data S hS with ⟨hR, hR_sq, hR_area⟩
  have hshape : r ^ 2 + r * h = 3 * optimalRadius S ^ 2 := by
    nlinarith [harea, hR_area, Real.pi_pos]
  have hmul : r ^ 3 + r ^ 2 * h =
      3 * optimalRadius S ^ 2 * r := by
    calc
      r ^ 3 + r ^ 2 * h = r * (r ^ 2 + r * h) := by ring
      _ = r * (3 * optimalRadius S ^ 2) := by rw [hshape]
      _ = 3 * optimalRadius S ^ 2 * r := by ring
  have hprod : 0 ≤ (r - optimalRadius S) ^ 2 *
      (r + 2 * optimalRadius S) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hvbase : r ^ 2 * h ≤
      optimalRadius S ^ 2 * (2 * optimalRadius S) := by
    nlinarith [hmul, hprod]
  have hscaled := mul_le_mul_of_nonneg_left hvbase
    (show 0 ≤ (1 / 2 : ℝ) * Real.pi by nlinarith [Real.pi_pos])
  simpa [volume, candidate, mul_assoc] using hscaled

theorem gap5 (S : ℝ) (hS : 0 < S) :
    volume (candidate S) = maximumVolume S := by
  rcases candidate_radius_data S hS with ⟨hR, hR_sq, hR_area⟩
  have hx : 0 ≤ S ^ 3 / (27 * Real.pi) := by
    exact le_of_lt (div_pos (pow_pos hS 3)
      (mul_pos (by norm_num) Real.pi_pos))
  have hsquare : (Real.pi * optimalRadius S ^ 3) ^ 2 =
      S ^ 3 / (27 * Real.pi) := by
    calc
      (Real.pi * optimalRadius S ^ 3) ^ 2 =
          Real.pi ^ 2 * (optimalRadius S ^ 2) ^ 3 := by ring
      _ = Real.pi ^ 2 * (S / (3 * Real.pi)) ^ 3 := by rw [hR_sq]
      _ = S ^ 3 / (27 * Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
        <;> ring
  have hleft : 0 ≤ Real.pi * optimalRadius S ^ 3 :=
    le_of_lt (mul_pos Real.pi_pos (pow_pos hR 3))
  change (1 / 2 : ℝ) * Real.pi * optimalRadius S ^ 2 *
      (2 * optimalRadius S) = Real.sqrt (S ^ 3 / (27 * Real.pi))
  have hvol : (1 / 2 : ℝ) * Real.pi * optimalRadius S ^ 2 *
      (2 * optimalRadius S) = Real.pi * optimalRadius S ^ 3 := by
    ring
  rw [hvol]
  nlinarith [Real.sq_sqrt hx,
    Real.sqrt_nonneg (S ^ 3 / (27 * Real.pi))]

theorem gap6 (S : ℝ) (hS : 0 < S) :
    sSup (volume '' {p : ℝ × ℝ | feasible S p}) = maximumVolume S := by
  have hopt := gap4 S hS
  change feasible S (candidate S) ∧
    ∀ q, feasible S q → volume q ≤ volume (candidate S) at hopt
  rcases hopt with ⟨hcfeas, hmax⟩
  have hbound : ∀ v ∈ volume '' {p : ℝ × ℝ | feasible S p},
      v ≤ maximumVolume S := by
    rintro v ⟨p, hp, rfl⟩
    calc
      volume p ≤ volume (candidate S) := hmax p hp
      _ = maximumVolume S := gap5 S hS
  have hnonempty : (volume '' {p : ℝ × ℝ | feasible S p}).Nonempty := by
    exact ⟨volume (candidate S), candidate S, hcfeas, rfl⟩
  have hmem : maximumVolume S ∈
      volume '' {p : ℝ × ℝ | feasible S p} := by
    exact ⟨candidate S, hcfeas, gap5 S hS⟩
  apply le_antisymm
  · exact csSup_le hnonempty hbound
  · exact le_csSup ⟨maximumVolume S, hbound⟩ hmem

theorem gap7 (S : ℝ) (hS : 0 < S) (r h : ℕ → ℝ)
    (hfeas : ∀ n, feasible S (r n, h n)) :
    (Filter.Tendsto r Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => volume (r n, h n)) Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto h Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => volume (r n, h n)) Filter.atTop (nhds 0)) := by
  constructor
  · intro hr0
    have hid : ∀ n, volume (r n, h n) =
        (1 / 2 : ℝ) * r n * (S - Real.pi * r n ^ 2) := by
      intro n
      rcases hfeas n with ⟨hr, hh, harea⟩
      calc
        volume (r n, h n) = (1 / 2 : ℝ) * r n *
            (Real.pi * (r n ^ 2 + r n * h n) -
              Real.pi * r n ^ 2) := by
          simp [volume]
          ring
        _ = (1 / 2 : ℝ) * r n * (S - Real.pi * r n ^ 2) := by
          rw [harea]
    have hpoly : Filter.Tendsto
        (fun n => S - Real.pi * r n ^ 2) Filter.atTop (nhds S) := by
      simpa using
        (tendsto_const_nhds.sub ((hr0.pow 2).const_mul Real.pi))
    have ht : Filter.Tendsto
        (fun n => (1 / 2 : ℝ) * r n *
          (S - Real.pi * r n ^ 2)) Filter.atTop (nhds 0) := by
      simpa [mul_assoc] using (hr0.mul hpoly).const_mul (1 / 2 : ℝ)
    exact ht.congr' (Filter.Eventually.of_forall
      (fun n => (hid n).symm))
  · intro hh0
    have hc : 0 < S / Real.pi := div_pos hS Real.pi_pos
    have hroot : ∀ n, r n =
        (Real.sqrt (h n ^ 2 + 4 * (S / Real.pi)) - h n) / 2 := by
      intro n
      rcases hfeas n with ⟨hr, hh, harea⟩
      have hshape : r n ^ 2 + r n * h n = S / Real.pi := by
        apply (eq_div_iff (ne_of_gt Real.pi_pos)).2
        nlinarith [harea]
      have hdisc : 0 ≤ h n ^ 2 + 4 * (S / Real.pi) := by
        nlinarith [sq_nonneg (h n)]
      have hsquare : (2 * r n + h n) ^ 2 =
          h n ^ 2 + 4 * (S / Real.pi) := by
        nlinarith [hshape]
      have hsum : 0 < 2 * r n + h n := by
        nlinarith
      have hsqrt_eq : Real.sqrt (h n ^ 2 + 4 * (S / Real.pi)) =
          2 * r n + h n := by
        nlinarith [Real.sq_sqrt hdisc,
          Real.sqrt_nonneg (h n ^ 2 + 4 * (S / Real.pi))]
      nlinarith
    have hdisc_tendsto : Filter.Tendsto
        (fun n => h n ^ 2 + 4 * (S / Real.pi)) Filter.atTop
        (nhds (0 ^ 2 + 4 * (S / Real.pi))) := by
      simpa using (hh0.pow 2).add
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ => 4 * (S / Real.pi)) Filter.atTop
          (nhds (4 * (S / Real.pi))))
    have hsqrt_tendsto :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hdisc_tendsto
    have hr_form := (hsqrt_tendsto.sub hh0).const_mul (1 / 2 : ℝ)
    have hr_tendsto : Filter.Tendsto r Filter.atTop
        (nhds ((1 / 2 : ℝ) *
          (Real.sqrt (0 ^ 2 + 4 * (S / Real.pi)) - 0))) := by
      exact hr_form.congr' (Filter.Eventually.of_forall (fun n => by
        simp only [Function.comp_apply]
        calc
          (1 / 2 : ℝ) *
              (Real.sqrt (h n ^ 2 + 4 * (S / Real.pi)) - h n) =
              (Real.sqrt (h n ^ 2 + 4 * (S / Real.pi)) - h n) / 2 := by
                ring
          _ = r n := (hroot n).symm))
    have hv := ((hr_tendsto.pow 2).mul hh0).const_mul
      ((1 / 2 : ℝ) * Real.pi)
    simpa [volume, mul_assoc] using hv

theorem gap8 (S : ℝ) (hS : 0 < S) (r h : ℕ → ℝ)
    (hfeas : ∀ n, feasible S (r n, h n))
    (hh : Filter.Tendsto h Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => volume (r n, h n)) Filter.atTop (nhds 0) := by
  have hc : 0 < S / Real.pi := div_pos hS Real.pi_pos
  have hden_top : Filter.Tendsto (fun n => r n + h n)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact (Filter.tendsto_atTop.1 hh b).mono (fun n hn => by
      have hr := (hfeas n).1
      nlinarith)
  have hinv_base : Filter.Tendsto (fun x : ℝ => x⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hinv := hinv_base.comp hden_top
  have hre : ∀ n, r n = (S / Real.pi) * (r n + h n)⁻¹ := by
    intro n
    rcases hfeas n with ⟨hr, hhn, harea⟩
    have hshape : r n ^ 2 + r n * h n = S / Real.pi := by
      apply (eq_div_iff (ne_of_gt Real.pi_pos)).2
      nlinarith [harea]
    have hmul : r n * (r n + h n) = S / Real.pi := by
      nlinarith [hshape]
    calc
      r n = (S / Real.pi) / (r n + h n) :=
        (eq_div_iff (ne_of_gt (by nlinarith : 0 < r n + h n))).2 hmul
      _ = (S / Real.pi) * (r n + h n)⁻¹ := by rw [div_eq_mul_inv]
  have hr_raw : Filter.Tendsto
      (fun n => (S / Real.pi) * (r n + h n)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      hinv.const_mul (S / Real.pi)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    exact hr_raw.congr' (Filter.Eventually.of_forall
      (fun n => (hre n).symm))
  exact (gap7 S hS r h hfeas).1 hr0

theorem gap9 (S : ℝ) (hS : 0 < S) :
    maximizers S = ({candidate S} : Set (ℝ × ℝ)) := by
  ext p
  constructor
  · intro hp
    change feasible S p ∧
      ∀ q, feasible S q → volume q ≤ volume p at hp
    rcases hp with ⟨hpfeas, hpmax⟩
    have hc := gap4 S hS
    change feasible S (candidate S) ∧
      ∀ q, feasible S q → volume q ≤ volume (candidate S) at hc
    rcases hc with ⟨hcfeas, hcmax⟩
    have hvol_eq : volume p = volume (candidate S) :=
      le_antisymm (hcmax p hpfeas) (hpmax (candidate S) hcfeas)
    rcases p with ⟨r, h⟩
    rcases hpfeas with ⟨hr, hh, harea⟩
    rcases candidate_radius_data S hS with ⟨hR, hR_sq, hR_area⟩
    have hshape : r ^ 2 + r * h = 3 * optimalRadius S ^ 2 := by
      nlinarith [harea, hR_area, Real.pi_pos]
    have hmul : r ^ 3 + r ^ 2 * h =
        3 * optimalRadius S ^ 2 * r := by
      calc
        r ^ 3 + r ^ 2 * h = r * (r ^ 2 + r * h) := by ring
        _ = r * (3 * optimalRadius S ^ 2) := by rw [hshape]
        _ = 3 * optimalRadius S ^ 2 * r := by ring
    have hvbase : r ^ 2 * h =
        2 * optimalRadius S ^ 3 := by
      change (1 / 2 : ℝ) * Real.pi * r ^ 2 * h =
        (1 / 2 : ℝ) * Real.pi * optimalRadius S ^ 2 *
          (2 * optimalRadius S) at hvol_eq
      nlinarith [Real.pi_pos]
    have hfactor : (r - optimalRadius S) ^ 2 *
        (r + 2 * optimalRadius S) = 0 := by
      nlinarith [hmul, hvbase]
    have hsum_ne : r + 2 * optimalRadius S ≠ 0 := by
      nlinarith
    have hsquare : (r - optimalRadius S) ^ 2 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hsum_ne
    have hr_eq : r = optimalRadius S := by
      nlinarith [sq_nonneg (r - optimalRadius S)]
    have hh_eq : h = 2 * optimalRadius S := by
      rw [hr_eq] at hshape
      nlinarith
    have hp_eq : (r, h) = candidate S := by
      simp [candidate, hr_eq, hh_eq]
    simpa using hp_eq
  · intro hp
    have hp_eq : p = candidate S := by
      simpa using hp
    subst p
    exact gap4 S hS

end

end ProofGap.Exercise3688
