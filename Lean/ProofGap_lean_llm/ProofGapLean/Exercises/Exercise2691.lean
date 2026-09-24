import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2691

noncomputable section

open Filter

def squareSine (n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) ^ 2)

def sineSeq (n : ℕ) : ℝ :=
  Real.sin n

theorem gap1
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => squareSine n ^ 2) atTop (nhds 0) := by
  simpa using h.pow 2

theorem gap2
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      squareSine n ^ 2 + Real.cos ((n : ℝ) ^ 2) ^ 2 = 1 := by
  intro n
  unfold squareSine
  exact Real.sin_sq_add_cos_sq ((n : ℝ) ^ 2)

theorem gap3
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.cos ((n : ℝ) ^ 2) ^ 2)
      atTop (nhds 1) := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) - squareSine n ^ 2)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (gap1 h)
  apply ht.congr'
  filter_upwards with n
  unfold squareSine
  nlinarith [Real.sin_sq_add_cos_sq ((n : ℝ) ^ 2)]

theorem gap4
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      squareSine (n + 1) =
        Real.sin ((n : ℝ) ^ 2 + 2 * n + 1) := by
  intro n
  unfold squareSine
  congr 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem gap5
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      Real.sin ((n : ℝ) ^ 2 + 2 * n + 1) =
        squareSine n * Real.cos (2 * n + 1) +
          Real.cos ((n : ℝ) ^ 2) * Real.sin (2 * n + 1) := by
  intro n
  unfold squareSine
  rw [show (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1 =
      (n : ℝ) ^ 2 + (2 * (n : ℝ) + 1) by ring]
  exact Real.sin_add ((n : ℝ) ^ 2) (2 * (n : ℝ) + 1)

theorem gap6
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      squareSine (n + 1) =
        squareSine n * Real.cos (2 * n + 1) +
          Real.cos ((n : ℝ) ^ 2) * Real.sin (2 * n + 1) := by
  intro n
  calc
    squareSine (n + 1) =
        Real.sin ((n : ℝ) ^ 2 + 2 * n + 1) := gap4 h n
    _ = squareSine n * Real.cos (2 * n + 1) +
          Real.cos ((n : ℝ) ^ 2) * Real.sin (2 * n + 1) := gap5 h n

theorem gap7
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      Real.cos ((n : ℝ) ^ 2) ^ 2 * Real.sin (2 * n + 1) ^ 2 =
        (squareSine (n + 1) -
          squareSine n * Real.cos (2 * n + 1)) ^ 2 := by
  intro n
  have heq :
      squareSine (n + 1) - squareSine n * Real.cos (2 * n + 1) =
        Real.cos ((n : ℝ) ^ 2) * Real.sin (2 * n + 1) := by
    linarith [gap6 h n]
  rw [heq]
  ring

theorem gap8
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.sin (2 * n + 1) ^ 2)
      atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => squareSine (n + 1))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  have hmul : Tendsto
      (fun n : ℕ => squareSine n * Real.cos (2 * (n : ℝ) + 1))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hh := h
    rw [Metric.tendsto_atTop] at hh
    obtain ⟨N, hN⟩ := hh ε hε
    refine ⟨N, ?_⟩
    intro n hn
    calc
      dist (squareSine n * Real.cos (2 * (n : ℝ) + 1)) 0 =
          |squareSine n| * |Real.cos (2 * (n : ℝ) + 1)| := by
        rw [Real.dist_eq, sub_zero, abs_mul]
      _ ≤ |squareSine n| * 1 := by
        exact mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one (2 * (n : ℝ) + 1)) (abs_nonneg _)
      _ = dist (squareSine n) 0 := by
        rw [Real.dist_eq, sub_zero, mul_one]
      _ < ε := hN n hn
  have hdiff : Tendsto
      (fun n : ℕ => squareSine (n + 1) -
        squareSine n * Real.cos (2 * n + 1))
      atTop (nhds 0) := by
    simpa using hshift.sub hmul
  have hp : Tendsto
      (fun n : ℕ => Real.cos ((n : ℝ) ^ 2) ^ 2 *
        Real.sin (2 * n + 1) ^ 2)
      atTop (nhds 0) := by
    have heq :
        (fun n : ℕ =>
          (squareSine (n + 1) -
            squareSine n * Real.cos (2 * n + 1)) ^ 2) =ᶠ[atTop]
        (fun n : ℕ =>
          Real.cos ((n : ℝ) ^ 2) ^ 2 * Real.sin (2 * n + 1) ^ 2) := by
      filter_upwards with n
      exact (gap7 h n).symm
    simpa using (hdiff.pow 2).congr' heq
  have hinv : Tendsto
      (fun n : ℕ => (Real.cos ((n : ℝ) ^ 2) ^ 2)⁻¹)
      atTop (nhds 1) := by
    simpa using (gap3 h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hq : Tendsto
      (fun n : ℕ =>
        (Real.cos ((n : ℝ) ^ 2) ^ 2 * Real.sin (2 * n + 1) ^ 2) *
          (Real.cos ((n : ℝ) ^ 2) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa using hp.mul hinv
  have hne : ∀ᶠ n : ℕ in atTop,
      Real.cos ((n : ℝ) ^ 2) ^ 2 ≠ 0 := by
    have hone : ∀ᶠ x : ℝ in nhds 1, x ≠ 0 :=
      eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)
    exact (gap3 h) hone
  apply hq.congr'
  filter_upwards [hne] with n hn
  calc
    (Real.cos ((n : ℝ) ^ 2) ^ 2 * Real.sin (2 * n + 1) ^ 2) *
          (Real.cos ((n : ℝ) ^ 2) ^ 2)⁻¹ =
        Real.sin (2 * n + 1) ^ 2 *
          (Real.cos ((n : ℝ) ^ 2) ^ 2 *
            (Real.cos ((n : ℝ) ^ 2) ^ 2)⁻¹) := by ring
    _ = Real.sin (2 * n + 1) ^ 2 := by simp [hn]

theorem gap9
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.sin (2 * n + 1))
      atTop (nhds 0) := by
  have hs : Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘
        (fun n : ℕ => Real.sin (2 * (n : ℝ) + 1) ^ 2))
      atTop (nhds (Real.sqrt (0 : ℝ))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp (gap8 h)
  have habs0 : Tendsto
      (fun n : ℕ => |Real.sin (2 * (n : ℝ) + 1)|)
      atTop (nhds (Real.sqrt (0 : ℝ))) := by
    refine hs.congr' ?_
    filter_upwards with n
    change Real.sqrt (Real.sin (2 * (n : ℝ) + 1) ^ 2) =
      |Real.sin (2 * (n : ℝ) + 1)|
    exact Real.sqrt_sq_eq_abs _
  have habs : Tendsto
      (fun n : ℕ => |Real.sin (2 * (n : ℝ) + 1)|)
      atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using habs0
  rw [Metric.tendsto_atTop] at habs ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := habs ε hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using hN n hn

theorem gap10
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.sin (2 * (n + 1) - 1))
      atTop (nhds 0) := by
  apply (gap9 h).congr'
  filter_upwards with n
  congr 1
  ring

theorem gap11
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ, 1 ≤ n →
      Real.sin (2 * n + 1) + Real.sin (2 * n - 1) =
        2 * Real.sin (2 * n) * Real.cos 1 := by
  intro n hn
  have hp := Real.sin_add (2 * (n : ℝ)) 1
  have hm := Real.sin_sub (2 * (n : ℝ)) 1
  rw [hp, hm]
  ring

theorem gap12
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.sin (2 * n)) atTop (nhds 0) := by
  have hoddShift : Tendsto
      (fun n : ℕ => Real.sin (2 * ((n + 1 : ℕ) : ℝ) + 1))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (gap9 h)
  have hsum := hoddShift.add (gap10 h)
  have hprod : Tendsto
      (fun n : ℕ =>
        2 * Real.sin (2 * ((n + 1 : ℕ) : ℝ)) * Real.cos 1)
      atTop (nhds 0) := by
    have heq :
        (fun n : ℕ =>
          Real.sin (2 * ((n + 1 : ℕ) : ℝ) + 1) +
            Real.sin (2 * (n + 1) - 1)) =ᶠ[atTop]
        (fun n : ℕ =>
          2 * Real.sin (2 * ((n + 1 : ℕ) : ℝ)) * Real.cos 1) := by
      filter_upwards with n
      simpa [Nat.cast_add, Nat.cast_one] using
        gap11 h (n + 1) (by omega)
    simpa using hsum.congr' heq
  have hcospos : 0 < Real.cos 1 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  have hcos : Real.cos 1 ≠ 0 := ne_of_gt hcospos
  have hc : (2 : ℝ) * Real.cos 1 ≠ 0 :=
    mul_ne_zero (by norm_num) hcos
  have hz : Tendsto
      (fun n : ℕ =>
        (2 * Real.sin (2 * ((n + 1 : ℕ) : ℝ)) * Real.cos 1) *
          (2 * Real.cos 1)⁻¹)
      atTop (nhds 0) := by
    simpa using hprod.mul_const ((2 * Real.cos 1)⁻¹)
  have hevenShift : Tendsto
      (fun n : ℕ => Real.sin (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    apply hz.congr'
    filter_upwards with n
    calc
      (2 * Real.sin (2 * ((n + 1 : ℕ) : ℝ)) * Real.cos 1) *
          (2 * Real.cos 1)⁻¹ =
        Real.sin (2 * ((n + 1 : ℕ) : ℝ)) *
          ((2 * Real.cos 1) * (2 * Real.cos 1)⁻¹) := by ring
      _ = Real.sin (2 * ((n + 1 : ℕ) : ℝ)) := by
        rw [mul_inv_cancel₀ hc, mul_one]
  exact (tendsto_add_atTop_iff_nat 1).1 hevenShift

theorem gap13
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto sineSeq atTop (nhds 0) := by
  have hparity : ∀ n : ℕ, ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
    intro n
    induction n with
    | zero =>
        exact ⟨0, Or.inl rfl⟩
    | succ n ih =>
        rcases ih with ⟨k, hk | hk⟩
        · exact ⟨k, Or.inr (by omega)⟩
        · exact ⟨k + 1, Or.inl (by omega)⟩
  have heven := gap12 h
  have hodd := gap9 h
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := hparity n
  have hle : Ne ≤ max Ne No := Nat.le_max_left _ _
  have hlo : No ≤ max Ne No := Nat.le_max_right _ _
  rcases hk with hk | hk
  · subst n
    have hkNe : Ne ≤ k := by omega
    simpa [sineSeq, Nat.cast_mul] using hNe k hkNe
  · subst n
    have hkNo : No ≤ k := by omega
    simpa [sineSeq, Nat.cast_add, Nat.cast_mul] using hNo k hkNo

theorem gap14
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => sineSeq n ^ 2) atTop (nhds 0) := by
  simpa using (gap13 h).pow 2

theorem gap15
    (h : Tendsto squareSine atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.cos n ^ 2) atTop (nhds 1) := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) - sineSeq n ^ 2)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (gap14 h)
  apply ht.congr'
  filter_upwards with n
  unfold sineSeq
  nlinarith [Real.sin_sq_add_cos_sq (n : ℝ)]

theorem gap16
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      sineSeq (n + 1) =
        sineSeq n * Real.cos 1 + Real.cos n * Real.sin 1 := by
  intro n
  simpa [sineSeq, Nat.cast_add, Nat.cast_one] using
    (Real.sin_add (n : ℝ) 1)

theorem gap17
    (h : Tendsto squareSine atTop (nhds 0)) :
    ∀ n : ℕ,
      Real.cos n ^ 2 * Real.sin 1 ^ 2 =
        (sineSeq (n + 1) - sineSeq n * Real.cos 1) ^ 2 := by
  intro n
  have heq :
      sineSeq (n + 1) - sineSeq n * Real.cos 1 =
        Real.cos n * Real.sin 1 := by
    linarith [gap16 h n]
  rw [heq]
  ring

theorem gap18
    (h : Tendsto squareSine atTop (nhds 0)) :
    Real.sin 1 ^ 2 ≠ 0 := by
  have hsin : 0 < Real.sin 1 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · norm_num
    · linarith [Real.pi_gt_three]
  exact pow_ne_zero 2 (ne_of_gt hsin)

theorem gap19 :
    Tendsto squareSine atTop (nhds 0) → False := by
  intro h
  have hshift : Tendsto (fun n : ℕ => sineSeq (n + 1))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (gap13 h)
  have hdiff : Tendsto
      (fun n : ℕ => sineSeq (n + 1) - sineSeq n * Real.cos 1)
      atTop (nhds 0) := by
    simpa using hshift.sub ((gap13 h).mul_const (Real.cos 1))
  have hl : Tendsto
      (fun n : ℕ => Real.cos n ^ 2 * Real.sin 1 ^ 2)
      atTop (nhds (Real.sin 1 ^ 2)) := by
    simpa using (gap15 h).mul_const (Real.sin 1 ^ 2)
  have hl0 : Tendsto
      (fun n : ℕ => Real.cos n ^ 2 * Real.sin 1 ^ 2)
      atTop (nhds 0) := by
    have heq :
        (fun n : ℕ =>
          (sineSeq (n + 1) - sineSeq n * Real.cos 1) ^ 2) =ᶠ[atTop]
        (fun n : ℕ => Real.cos n ^ 2 * Real.sin 1 ^ 2) := by
      filter_upwards with n
      exact (gap17 h n).symm
    simpa using (hdiff.pow 2).congr' heq
  have hz : Real.sin 1 ^ 2 = 0 := tendsto_nhds_unique hl hl0
  exact gap18 h hz

theorem gap20 :
    ¬ Tendsto squareSine atTop (nhds 0) := by
  intro h
  exact gap19 h

theorem gap21 :
    ¬ Summable (fun n : ℕ => squareSine (n + 1)) := by
  intro hs
  apply gap20
  have hshift : Tendsto (fun n : ℕ => squareSine (n + 1))
      atTop (nhds 0) := hs.tendsto_atTop_zero
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

end

end ProofGap.Exercise2691
