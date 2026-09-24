import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise752

noncomputable section

def boundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Bornology.IsBounded (f '' s)
def increment (f : ℝ → ℝ) (x₀ T y : ℝ) : ℝ :=
  f (x₀ + (y + 1) * T) - f (x₀ + y * T)
def eps (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

/-- Source: `proof_gap/exercise_752/1.txt`; index `g` by the step `T`. -/
theorem gap1 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : ContinuousOn f (Set.Ioi x₀)) :
    ∀ T > 0, ContinuousOn (increment f x₀ T) (Set.Ici 1) := by
  intro T hT y hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have ha : x₀ < x₀ + (y + 1) * T := by nlinarith
  have hb : x₀ < x₀ + y * T := by nlinarith
  have hfa : ContinuousAt f (x₀ + (y + 1) * T) :=
    hf.continuousAt (isOpen_Ioi.mem_nhds ha)
  have hfb : ContinuousAt f (x₀ + y * T) :=
    hf.continuousAt (isOpen_Ioi.mem_nhds hb)
  have haddA : ContinuousAt (fun u : ℝ => x₀ + u) ((y + 1) * T) :=
    continuousAt_const.add continuousAt_id
  have haddB : ContinuousAt (fun u : ℝ => x₀ + u) (y * T) :=
    continuousAt_const.add continuousAt_id
  have houterA :
      ContinuousAt (f ∘ (fun u : ℝ => x₀ + u)) ((y + 1) * T) :=
    hfa.comp haddA
  have houterB :
      ContinuousAt (f ∘ (fun u : ℝ => x₀ + u)) (y * T) :=
    hfb.comp haddB
  have hargA : ContinuousAt (fun z : ℝ => (z + 1) * T) y :=
    (continuousAt_id.add continuousAt_const).mul continuousAt_const
  have hargB : ContinuousAt (fun z : ℝ => z * T) y :=
    continuousAt_id.mul continuousAt_const
  have hA :
      ContinuousAt
        ((f ∘ (fun u : ℝ => x₀ + u)) ∘ (fun z : ℝ => (z + 1) * T)) y :=
    houterA.comp (f := fun z : ℝ => (z + 1) * T) (x := y) hargA
  have hB :
      ContinuousAt
        ((f ∘ (fun u : ℝ => x₀ + u)) ∘ (fun z : ℝ => z * T)) y :=
    houterB.comp (f := fun z : ℝ => z * T) (x := y) hargB
  simpa [increment, Function.comp_def] using (hA.sub hB).continuousWithinAt

/-- Source: `proof_gap/exercise_752/2.txt`; index `g` by `T`. -/
theorem gap2 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : boundedOn f (Set.Ioi x₀)) :
    ∀ T > 0, boundedOn (increment f x₀ T) (Set.Ici 1) := by
  intro T hT
  unfold boundedOn at hf ⊢
  apply (hf.sub hf).subset
  rintro z ⟨y, hy, rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hy1 : 0 < y + 1 := by linarith
  have hya : 0 < (y + 1) * T := mul_pos hy1 hT
  have hyb : 0 < y * T := mul_pos hy0 hT
  refine ⟨f (x₀ + (y + 1) * T), ?_, f (x₀ + y * T), ?_, rfl⟩
  · exact ⟨x₀ + (y + 1) * T, lt_add_of_pos_right x₀ hya, rfl⟩
  · exact ⟨x₀ + y * T, lt_add_of_pos_right x₀ hyb, rfl⟩

/-- Source: `proof_gap/exercise_752/3.txt`; replace the unbound sequence by
`εₙ=1/(n+1)`. -/
theorem gap3 : Filter.Tendsto eps Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hmul : 1 < (N : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have heps : eps n < δ := by
    unfold eps
    apply (div_lt_iff₀ hden).2
    nlinarith
  have heps0 : 0 < eps n := by
    unfold eps
    positivity
  simpa [Real.dist_eq, abs_of_pos heps0] using heps

/-- Source: `proof_gap/exercise_752/4.txt`; the displayed growth estimate needs
a fixed sign, not merely an absolute lower bound. -/
theorem gap4 (f : ℝ → ℝ) (x₀ T : ℝ) (n p k : ℕ)
    (hT : 0 < T) (hn : ∀ j ≥ p, eps n ≤ increment f x₀ T j)
    (hpk : p ≤ k) :
    f (x₀ + (k + 1 : ℕ) * T) ≥
      (k - p + 1 : ℕ) * eps n + f (x₀ + p * T) := by
  have hstep : ∀ j : ℕ, p ≤ j →
      eps n ≤ f (x₀ + ((j + 1 : ℕ) : ℝ) * T) -
        f (x₀ + (j : ℝ) * T) := by
    intro j hj
    simpa [increment, Nat.cast_add, Nat.cast_one] using hn j hj
  induction k, hpk using Nat.le_induction with
  | base =>
      have hs := hstep p (le_refl p)
      simpa using (show
        f (x₀ + (((p + 1 : ℕ) : ℝ)) * T) ≥
          eps n + f (x₀ + (p : ℝ) * T) by linarith)
  | succ k hpk ih =>
      have hs := hstep (k + 1) (Nat.le_succ_of_le hpk)
      have hcount : k + 1 - p + 1 = (k - p + 1) + 1 := by omega
      have hcountR :
          ((k + 1 - p + 1 : ℕ) : ℝ) =
            ((k - p + 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hcount
      rw [hcountR, add_mul, one_mul]
      linarith

/-- Source: `proof_gap/exercise_752/5.txt`; state the eventual-one-sign
alternative that contradicts boundedness. -/
theorem gap5 (f : ℝ → ℝ) (x₀ T : ℝ)
    (hT : 0 < T) (hf : boundedOn f (Set.Ioi x₀)) :
    ¬(∃ n p : ℕ, (∀ k ≥ p, eps n ≤ increment f x₀ T k) ∨
      (∀ k ≥ p, increment f x₀ T k ≤ -eps n)) := by
  intro hex
  unfold boundedOn at hf
  rcases Metric.isBounded_iff.1 hf with ⟨C, hC⟩
  rcases hex with ⟨n, p, hpos | hneg⟩
  · have he : 0 < eps n := by
      unfold eps
      positivity
    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        ((C + f (x₀ + T) - f (x₀ + (p : ℝ) * T)) / eps n)
    have hmul :
        C + f (x₀ + T) - f (x₀ + (p : ℝ) * T) <
          (N : ℝ) * eps n := by
      exact (div_lt_iff₀ he).mp hN
    have hg := gap4 f x₀ T n p (p + N) hT hpos (by omega)
    have hcount : p + N - p + 1 = N + 1 := by omega
    have hcountR :
        ((p + N - p + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
      rw [hcount]
      norm_num
    rw [hcountR, add_mul, one_mul] at hg
    have hbig :
        C + f (x₀ + T) <
          f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) := by
      linarith
    have hend :
        f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) ∈
          f '' Set.Ioi x₀ := by
      have hprod : 0 < ((p + N + 1 : ℕ) : ℝ) * T :=
        mul_pos (by positivity) hT
      exact ⟨x₀ + ((p + N + 1 : ℕ) : ℝ) * T,
        lt_add_of_pos_right x₀ hprod, rfl⟩
    have hanchor : f (x₀ + T) ∈ f '' Set.Ioi x₀ := by
      exact ⟨x₀ + T, lt_add_of_pos_right x₀ hT, rfl⟩
    have hd :
        dist (f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T))
          (f (x₀ + T)) ≤ C := hC hend hanchor
    have hC0 : 0 ≤ C := le_trans dist_nonneg hd
    have hdiff :
        C < f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) - f (x₀ + T) := by
      linarith
    have hdiff0 :
        0 < f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) - f (x₀ + T) :=
      lt_of_le_of_lt hC0 hdiff
    rw [Real.dist_eq, abs_of_pos hdiff0] at hd
    linarith
  · have he : 0 < eps n := by
      unfold eps
      positivity
    have hneg' : ∀ j ≥ p,
        eps n ≤ increment (fun z => -f z) x₀ T j := by
      intro j hj
      have h := hneg j hj
      simp [increment] at h ⊢
      linarith
    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        ((C - f (x₀ + T) + f (x₀ + (p : ℝ) * T)) / eps n)
    have hmul :
        C - f (x₀ + T) + f (x₀ + (p : ℝ) * T) <
          (N : ℝ) * eps n := by
      exact (div_lt_iff₀ he).mp hN
    have hg := gap4 (fun z => -f z) x₀ T n p (p + N) hT hneg' (by omega)
    have hcount : p + N - p + 1 = N + 1 := by omega
    have hcountR :
        ((p + N - p + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
      rw [hcount]
      norm_num
    rw [hcountR, add_mul, one_mul] at hg
    have hbig :
        f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) <
          f (x₀ + T) - C := by
      linarith
    have hend :
        f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) ∈
          f '' Set.Ioi x₀ := by
      have hprod : 0 < ((p + N + 1 : ℕ) : ℝ) * T :=
        mul_pos (by positivity) hT
      exact ⟨x₀ + ((p + N + 1 : ℕ) : ℝ) * T,
        lt_add_of_pos_right x₀ hprod, rfl⟩
    have hanchor : f (x₀ + T) ∈ f '' Set.Ioi x₀ := by
      exact ⟨x₀ + T, lt_add_of_pos_right x₀ hT, rfl⟩
    have hd :
        dist (f (x₀ + T))
          (f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T)) ≤ C :=
      hC hanchor hend
    have hC0 : 0 ≤ C := le_trans dist_nonneg hd
    have hdiff :
        C < f (x₀ + T) -
          f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) := by
      linarith
    have hdiff0 :
        0 < f (x₀ + T) -
          f (x₀ + ((p + N + 1 : ℕ) : ℝ) * T) :=
      lt_of_le_of_lt hC0 hdiff
    rw [Real.dist_eq, abs_of_pos hdiff0] at hd
    linarith

/-- Source: `proof_gap/exercise_752/6.txt`; make the selected integer depend on
`n` and on `T`. -/
theorem gap6 (f : ℝ → ℝ) (x₀ T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn f (Set.Ioi x₀))
    (hb : boundedOn f (Set.Ioi x₀)) :
    ∀ n p : ℕ, 1 ≤ p → ∃ y : ℝ,
      (p : ℝ) ≤ y ∧ |increment f x₀ T y| < eps n := by
  have hgcont : ContinuousOn (increment f x₀ T) (Set.Ici 1) :=
    gap1 f x₀ hc T hT
  intro n p hp
  by_contra hnone
  have he : 0 < eps n := by
    unfold eps
    positivity
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlarge : ∀ y : ℝ, (p : ℝ) ≤ y →
      eps n ≤ |increment f x₀ T y| := by
    intro y hy
    exact le_of_not_gt (fun hlt => hnone ⟨y, hy, hlt⟩)
  have hdown : ∀ {k : ℕ}, p ≤ k →
      eps n ≤ increment f x₀ T p →
      increment f x₀ T k ≤ -eps n → False := by
    intro k hpk hpp hkk
    have hpkR : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpk
    have hcI : ContinuousOn (increment f x₀ T)
        (Set.Icc (p : ℝ) (k : ℝ)) :=
      hgcont.mono (by
        intro z hz
        exact le_trans hpR hz.1)
    have hzmem : (0 : ℝ) ∈
        Set.Icc (increment f x₀ T k) (increment f x₀ T p) := by
      constructor <;> nlinarith
    rcases intermediate_value_Icc' hpkR hcI hzmem with ⟨z, hz, hz0⟩
    have hzlarge := hlarge z hz.1
    rw [hz0, abs_zero] at hzlarge
    linarith
  have hup : ∀ {k : ℕ}, p ≤ k →
      increment f x₀ T p ≤ -eps n →
      eps n ≤ increment f x₀ T k → False := by
    intro k hpk hpp hkk
    have hpkR : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpk
    have hcI : ContinuousOn (increment f x₀ T)
        (Set.Icc (p : ℝ) (k : ℝ)) :=
      hgcont.mono (by
        intro z hz
        exact le_trans hpR hz.1)
    have hzmem : (0 : ℝ) ∈
        Set.Icc (increment f x₀ T p) (increment f x₀ T k) := by
      constructor <;> nlinarith
    rcases intermediate_value_Icc hpkR hcI hzmem with ⟨z, hz, hz0⟩
    have hzlarge := hlarge z hz.1
    rw [hz0, abs_zero] at hzlarge
    linarith
  have hpabs := hlarge (p : ℝ) (le_refl _)
  by_cases hpnonneg : 0 ≤ increment f x₀ T p
  · have hpp : eps n ≤ increment f x₀ T p := by
      simpa [abs_of_nonneg hpnonneg] using hpabs
    have htail : ∀ k ≥ p, eps n ≤ increment f x₀ T k := by
      intro k hk
      by_contra hknot
      have hkabs := hlarge (k : ℝ) (by exact_mod_cast hk)
      have hkneg : increment f x₀ T k ≤ -eps n := by
        by_cases hk0 : 0 ≤ increment f x₀ T k
        · rw [abs_of_nonneg hk0] at hkabs
          exact False.elim (hknot hkabs)
        · rw [abs_of_nonpos (le_of_not_ge hk0)] at hkabs
          linarith
      exact hdown hk hpp hkneg
    exact (gap5 f x₀ T hT hb) ⟨n, p, Or.inl htail⟩
  · have hpnonpos : increment f x₀ T p ≤ 0 := le_of_not_ge hpnonneg
    have hpp : increment f x₀ T p ≤ -eps n := by
      rw [abs_of_nonpos hpnonpos] at hpabs
      linarith
    have htail : ∀ k ≥ p, increment f x₀ T k ≤ -eps n := by
      intro k hk
      by_contra hknot
      have hkabs := hlarge (k : ℝ) (by exact_mod_cast hk)
      have hkpos : eps n ≤ increment f x₀ T k := by
        by_cases hk0 : 0 ≤ increment f x₀ T k
        · simpa [abs_of_nonneg hk0] using hkabs
        · rw [abs_of_nonpos (le_of_not_ge hk0)] at hkabs
          exfalso
          exact hknot (by linarith)
      exact hup hk hpp hkpos
    exact (gap5 f x₀ T hT hb) ⟨n, p, Or.inr htail⟩

/-- Source: `proof_gap/exercise_752/7.txt`; bind the integer selector and
require it to tend to infinity. -/
theorem gap7 (x₀ T : ℝ) (k : ℕ → ℕ)
    (hT : 0 < T) (hk : Filter.Tendsto k Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => x₀ + (k n : ℝ) * T)
      Filter.atTop (Filter.atTop : Filter ℝ) := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  obtain ⟨K : ℕ, hK⟩ := exists_nat_gt ((b - x₀) / T)
  filter_upwards [Filter.tendsto_atTop.1 hk K] with n hn
  have hn' : (K : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hn
  have hmul : b - x₀ < (K : ℝ) * T := by
    have := (div_lt_iff₀ hT).mp hK
    nlinarith
  nlinarith

/-- Source: `proof_gap/exercise_752/8.txt`; bind the selected sequence. -/
theorem gap8 (f : ℝ → ℝ) (T : ℝ) (x : ℕ → ℝ)
    (hx : Filter.Tendsto x Filter.atTop (Filter.atTop : Filter ℝ))
    (hd : ∀ n, |f (x n + T) - f (x n)| < eps n) :
    Filter.Tendsto (fun n => f (x n + T) - f (x n))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  rcases (Metric.tendsto_atTop.1 gap3 δ hδ) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have he := hN n hn
  have heps0 : 0 < eps n := by
    unfold eps
    positivity
  have heps : eps n < δ := by
    simpa [Real.dist_eq, abs_of_pos heps0] using he
  simpa [Real.dist_eq] using lt_trans (hd n) heps

/-- Source: `proof_gap/exercise_752/9`; repair the existential scope and add
the omitted positivity assumption on `T`. -/
theorem gap9 (f : ℝ → ℝ) (x₀ : ℝ)
    (hc : ContinuousOn f (Set.Ioi x₀))
    (hb : boundedOn f (Set.Ioi x₀)) :
    ∀ T > 0, ∃ x : ℕ → ℝ,
      Filter.Tendsto x Filter.atTop (Filter.atTop : Filter ℝ) ∧
      Filter.Tendsto (fun n => f (x n + T) - f (x n))
        Filter.atTop (nhds 0) := by
  intro T hT
  have hgcont :
      ContinuousOn (increment f x₀ T) (Set.Ici 1) :=
    gap1 f x₀ hc T hT
  have hsmall : ∀ n p : ℕ, 1 ≤ p →
      ∃ y : ℝ, (p : ℝ) ≤ y ∧ |increment f x₀ T y| < eps n := by
    intro n p hp
    by_contra hnone
    have he : 0 < eps n := by
      unfold eps
      positivity
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hlarge : ∀ y : ℝ, (p : ℝ) ≤ y →
        eps n ≤ |increment f x₀ T y| := by
      intro y hy
      exact le_of_not_gt (fun hlt => hnone ⟨y, hy, hlt⟩)
    have hdown : ∀ {k : ℕ}, p ≤ k →
        eps n ≤ increment f x₀ T p →
        increment f x₀ T k ≤ -eps n → False := by
      intro k hpk hpp hkk
      have hpkR : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpk
      have hcI : ContinuousOn (increment f x₀ T)
          (Set.Icc (p : ℝ) (k : ℝ)) :=
        hgcont.mono (by
          intro z hz
          exact le_trans hpR hz.1)
      have hzmem : (0 : ℝ) ∈
          Set.Icc (increment f x₀ T k) (increment f x₀ T p) := by
        constructor <;> nlinarith
      rcases intermediate_value_Icc' hpkR hcI hzmem with
        ⟨z, hz, hz0⟩
      have hzlarge := hlarge z hz.1
      rw [hz0, abs_zero] at hzlarge
      linarith
    have hup : ∀ {k : ℕ}, p ≤ k →
        increment f x₀ T p ≤ -eps n →
        eps n ≤ increment f x₀ T k → False := by
      intro k hpk hpp hkk
      have hpkR : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpk
      have hcI : ContinuousOn (increment f x₀ T)
          (Set.Icc (p : ℝ) (k : ℝ)) :=
        hgcont.mono (by
          intro z hz
          exact le_trans hpR hz.1)
      have hzmem : (0 : ℝ) ∈
          Set.Icc (increment f x₀ T p) (increment f x₀ T k) := by
        constructor <;> nlinarith
      rcases intermediate_value_Icc hpkR hcI hzmem with
        ⟨z, hz, hz0⟩
      have hzlarge := hlarge z hz.1
      rw [hz0, abs_zero] at hzlarge
      linarith
    have hpabs := hlarge (p : ℝ) (le_refl _)
    by_cases hpnonneg : 0 ≤ increment f x₀ T p
    · have hpp : eps n ≤ increment f x₀ T p := by
        simpa [abs_of_nonneg hpnonneg] using hpabs
      have htail : ∀ k ≥ p, eps n ≤ increment f x₀ T k := by
        intro k hk
        by_contra hknot
        have hkabs := hlarge (k : ℝ) (by exact_mod_cast hk)
        have hkneg : increment f x₀ T k ≤ -eps n := by
          by_cases hk0 : 0 ≤ increment f x₀ T k
          · rw [abs_of_nonneg hk0] at hkabs
            exact False.elim (hknot hkabs)
          · rw [abs_of_nonpos (le_of_not_ge hk0)] at hkabs
            linarith
        exact hdown hk hpp hkneg
      exact (gap5 f x₀ T hT hb) ⟨n, p, Or.inl htail⟩
    · have hpnonpos : increment f x₀ T p ≤ 0 := le_of_not_ge hpnonneg
      have hpp : increment f x₀ T p ≤ -eps n := by
        rw [abs_of_nonpos hpnonpos] at hpabs
        linarith
      have htail : ∀ k ≥ p, increment f x₀ T k ≤ -eps n := by
        intro k hk
        by_contra hknot
        have hkabs := hlarge (k : ℝ) (by exact_mod_cast hk)
        have hkpos : eps n ≤ increment f x₀ T k := by
          by_cases hk0 : 0 ≤ increment f x₀ T k
          · simpa [abs_of_nonneg hk0] using hkabs
          · rw [abs_of_nonpos (le_of_not_ge hk0)] at hkabs
            exfalso
            exact hknot (by linarith)
        exact hup hk hpp hkpos
      exact (gap5 f x₀ T hT hb) ⟨n, p, Or.inr htail⟩
  have hchoice : ∀ n : ℕ, ∃ y : ℝ,
      ((n + 1 : ℕ) : ℝ) ≤ y ∧ |increment f x₀ T y| < eps n := by
    intro n
    exact hsmall n (n + 1) (by omega)
  choose y hy hdy using hchoice
  let x : ℕ → ℝ := fun n => x₀ + y n * T
  have hx : Filter.Tendsto x Filter.atTop (Filter.atTop : Filter ℝ) := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - x₀) / T)
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    have hyN : (N : ℝ) ≤ y n := hnR.trans (hnn.trans (hy n))
    have hmul : b - x₀ < (N : ℝ) * T :=
      (div_lt_iff₀ hT).mp hN
    have hprod : (N : ℝ) * T ≤ y n * T :=
      mul_le_mul_of_nonneg_right hyN hT.le
    dsimp [x]
    linarith
  refine ⟨x, hx, gap8 f T x hx ?_⟩
  intro n
  simpa [x, increment, add_mul, add_assoc] using hdy n

end

end ProofGap.Exercise752
