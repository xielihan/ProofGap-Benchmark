import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise4166

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

abbrev Point := ℝ × ℝ

def mass (f : Point → ℝ) (A : Set Point) : ℝ≥0∞ :=
  ∫⁻ z in A, ENNReal.ofReal (f z)

theorem gap1 (S' : ℕ → Set Point) (hmono : Monotone S') :
    S' 1 ⊆ S' 2 := by
  exact hmono (Nat.le_succ 1)

theorem gap2 (S' : ℕ → Set Point) (hmono : Monotone S') :
    ∀ n, 2 ≤ n → S' 2 ⊆ S' n := by
  intro n hn
  exact hmono hn

theorem gap3 (S' : ℕ → Set Point) (S : Set Point)
    (hUnion : ⋃ n, S' n = S) :
    ∀ n, S' n ⊆ S := by
  intro n
  rw [← hUnion]
  exact Set.subset_iUnion S' n

theorem gap4 (S' : ℕ → Set Point) (S : Set Point)
    (hUnion : ⋃ n, S' n = S) :
    ⋃ n, S' n = S := by
  exact hUnion

theorem gap5 (f : Point → ℝ) (S' : ℕ → Set Point)
    (hf : ∀ z, 0 ≤ f z) (hmono : Monotone S') :
    ∀ i j, i ≤ j → mass f (S' i) ≤ mass f (S' j) := by
  intro i j hij
  unfold mass
  exact lintegral_mono_set (hmono hij)

theorem gap6 (f : Point → ℝ) (S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ n, N ≤ n →
        mass f (S' n) < I + ENNReal.ofReal ε ∧
          I < mass f (S' n) + ENNReal.ofReal ε := by
  intro ε hε
  let δ : ℝ≥0∞ := ENNReal.ofReal ε
  have hδ : 0 < δ := by
    exact ENNReal.ofReal_pos.mpr hε
  have hlt : I < I + δ := ENNReal.lt_add_right hI hδ.ne'
  have hu : ∀ᶠ n in atTop, mass f (S' n) < I + δ :=
    (tendsto_order.1 hlim).2 (I + δ) hlt
  have haddlim :
      Tendsto (fun n => mass f (S' n) + δ) atTop (nhds (I + δ)) :=
    hlim.add tendsto_const_nhds
  have hl : ∀ᶠ n in atTop, I < mass f (S' n) + δ :=
    (tendsto_order.1 haddlim).1 I hlt
  rcases eventually_atTop.1 (hu.and hl) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [δ] using hN n hn

theorem gap7 (S S' : ℕ → Set Point)
    (hcofinal : ∀ N, ∃ n₀, ∀ n, n₀ ≤ n → S' N ⊆ S n) :
    ∀ N, ∃ n₀, ∀ n, n₀ ≤ n → S' N ⊆ S n := by
  exact hcofinal

theorem gap8 (f : Point → ℝ) (S S' : ℕ → Set Point)
    (hf : ∀ z, 0 ≤ f z)
    (hcofinal : ∀ N, ∃ n₀, ∀ n, n₀ ≤ n → S' N ⊆ S n) :
    ∀ N, ∃ n₀, ∀ n, n₀ ≤ n →
      mass f (S' N) ≤ mass f (S n) := by
  intro N
  rcases hcofinal N with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  unfold mass
  exact lintegral_mono_set (hn₀ n hn)

theorem gap9 (f : Point → ℝ) (S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N, I < mass f (S' N) + ENNReal.ofReal ε := by
  intro ε hε
  rcases gap6 f S' I hlim hI ε hε with ⟨N, hN⟩
  exact ⟨N, (hN N le_rfl).2⟩

theorem gap10 (f : Point → ℝ) (S S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I ≠ ⊤)
    (hcofinal : ∀ N, ∃ n₀, ∀ n, n₀ ≤ n → S' N ⊆ S n) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n₀, ∀ n, n₀ ≤ n →
        I < mass f (S n) + ENNReal.ofReal ε := by
  intro ε hε
  rcases gap9 f S' I hlim hI ε hε with ⟨N, hN⟩
  rcases hcofinal N with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have hm : mass f (S' N) ≤ mass f (S n) := by
    unfold mass
    exact lintegral_mono_set (hn₀ n hn)
  have hm' :
      mass f (S' N) + ENNReal.ofReal ε ≤
        mass f (S n) + ENNReal.ofReal ε := by
    simpa [add_comm] using
      (add_le_add_right hm (ENNReal.ofReal ε))
  exact lt_of_lt_of_le hN hm'

theorem gap11 (S S' : ℕ → Set Point)
    (hcofinal : ∀ n, ∃ k, S n ⊆ S' k) :
    ∀ n, ∃ k, S n ⊆ S' k := by
  exact hcofinal

theorem gap12 (f : Point → ℝ) (S S' : ℕ → Set Point)
    (hf : ∀ z, 0 ≤ f z)
    (hcofinal : ∀ n, ∃ k, S n ⊆ S' k) :
    ∃ k : ℕ → ℕ, ∀ n,
      mass f (S n) ≤ mass f (S' (k n)) := by
  classical
  let k : ℕ → ℕ := fun n => Classical.choose (hcofinal n)
  refine ⟨k, ?_⟩
  intro n
  unfold mass
  apply lintegral_mono_set
  simpa [k] using Classical.choose_spec (hcofinal n)

theorem gap13 (f : Point → ℝ) (S S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hI : I ≠ ⊤)
    (hcompare :
      ∃ k : ℕ → ℕ, ∀ n, mass f (S n) ≤ mass f (S' (k n)))
    (hrefUpper : ∀ j, mass f (S' j) ≤ I) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ → ℕ, ∀ n,
        mass f (S' (k n)) < I + ENNReal.ofReal ε := by
  intro ε hε
  rcases hcompare with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  have hlt : I < I + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hI (ENNReal.ofReal_pos.mpr hε).ne'
  exact lt_of_le_of_lt (hrefUpper (k n)) hlt

theorem gap14 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hI : I ≠ ⊤)
    (hupper : ∀ n, mass f (S n) ≤ I) :
    ∀ ε : ℝ, 0 < ε → ∀ n,
      mass f (S n) < I + ENNReal.ofReal ε := by
  intro ε hε n
  have hlt : I < I + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hI (ENNReal.ofReal_pos.mpr hε).ne'
  exact lt_of_le_of_lt (hupper n) hlt

theorem gap15 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∃ n₀, ∀ n, n₀ ≤ n →
          I < mass f (S n) + ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n₀, ∀ n, n₀ ≤ n →
        I < mass f (S n) + ENNReal.ofReal ε := by
  exact hlower

theorem gap16 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hI : I ≠ ⊤)
    (hupper : ∀ n, mass f (S n) ≤ I) :
    ∀ ε : ℝ, 0 < ε → ∀ n,
      mass f (S n) < I + ENNReal.ofReal ε := by
  exact gap14 f S I hI hupper

theorem gap17 (I : ℝ≥0∞) (ε : ℝ)
    (hI : I ≠ ⊤) (hε : 0 < ε) :
    I - ENNReal.ofReal ε < I + ENNReal.ofReal ε := by
  have hlt : I < I + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hI (ENNReal.ofReal_pos.mpr hε).ne'
  have hle : I - ENNReal.ofReal ε ≤ I := tsub_le_self
  exact lt_of_le_of_lt hle hlt

theorem gap18 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hI : I ≠ ⊤)
    (hlower :
      ∀ ε : ℝ, 0 < ε →
        ∃ n₀, ∀ n, n₀ ≤ n →
          I < mass f (S n) + ENNReal.ofReal ε)
    (hupper :
      ∀ ε : ℝ, 0 < ε →
        ∃ n₀, ∀ n, n₀ ≤ n →
          mass f (S n) < I + ENNReal.ofReal ε) :
    Tendsto (fun n => mass f (S n)) atTop (nhds I) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hI_top : I < ⊤ := (lt_top_iff_ne_top).2 hI
    have ha_top : a ≠ ⊤ := ne_of_lt (lt_trans ha hI_top)
    have hai : a.toReal < I.toReal :=
      (ENNReal.toReal_lt_toReal ha_top hI).2 ha
    let ε : ℝ := (I.toReal - a.toReal) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hsum_top : a + ENNReal.ofReal ε ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ha_top, ENNReal.ofReal_ne_top⟩
    have hsum : a + ENNReal.ofReal ε < I := by
      apply (ENNReal.toReal_lt_toReal hsum_top hI).1
      rw [ENNReal.toReal_add ha_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε.le]
      dsimp [ε]
      linarith
    rcases hlower ε hε with ⟨n₀, hn₀⟩
    refine eventually_atTop.2 ⟨n₀, ?_⟩
    intro n hn
    have hnear := hn₀ n hn
    by_contra hnot
    have hxle : mass f (S n) ≤ a := le_of_not_gt hnot
    have hadd :
        mass f (S n) + ENNReal.ofReal ε ≤
          a + ENNReal.ofReal ε := by
      simpa [add_comm] using
        (add_le_add_right hxle (ENNReal.ofReal ε))
    have hle : mass f (S n) + ENNReal.ofReal ε ≤ I :=
      le_trans hadd (le_of_lt hsum)
    exact (not_lt_of_ge hle) hnear
  · intro b hb
    by_cases hb_top : b = ⊤
    · subst b
      rcases hupper 1 zero_lt_one with ⟨n₀, hn₀⟩
      have hsum_top : I + ENNReal.ofReal 1 ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hI, ENNReal.ofReal_ne_top⟩
      have hsum_lt : I + ENNReal.ofReal 1 < ⊤ :=
        (lt_top_iff_ne_top).2 hsum_top
      refine eventually_atTop.2 ⟨n₀, ?_⟩
      intro n hn
      exact lt_trans (hn₀ n hn) hsum_lt
    · have hIb : I.toReal < b.toReal :=
        (ENNReal.toReal_lt_toReal hI hb_top).2 hb
      let ε : ℝ := (b.toReal - I.toReal) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hsum_top : I + ENNReal.ofReal ε ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hI, ENNReal.ofReal_ne_top⟩
      have hsum : I + ENNReal.ofReal ε < b := by
        apply (ENNReal.toReal_lt_toReal hsum_top hb_top).1
        rw [ENNReal.toReal_add hI ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hε.le]
        dsimp [ε]
        linarith
      rcases hupper ε hε with ⟨n₀, hn₀⟩
      refine eventually_atTop.2 ⟨n₀, ?_⟩
      intro n hn
      exact lt_trans (hn₀ n hn) hsum

theorem gap19 (f : Point → ℝ) (S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I = ⊤) :
    ∀ M : ℝ, 0 < M →
      ∃ N, ENNReal.ofReal M < mass f (S' N) := by
  intro M hM
  have hlimtop : Tendsto (fun n => mass f (S' n)) atTop (nhds ⊤) := by
    simpa [hI] using hlim
  have hthreshold : ENNReal.ofReal M < ⊤ :=
    (lt_top_iff_ne_top).2 ENNReal.ofReal_ne_top
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal M < mass f (S' n) :=
    (tendsto_order.1 hlimtop).1 (ENNReal.ofReal M) hthreshold
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, hN N le_rfl⟩

theorem gap20 (S S' : ℕ → Set Point)
    (hcofinal : ∀ N, ∃ n₁, ∀ n, n₁ ≤ n → S' N ⊆ S n) :
    ∀ N, ∃ n₁, ∀ n, n₁ ≤ n → S' N ⊆ S n := by
  exact hcofinal

theorem gap21 (f : Point → ℝ) (S S' : ℕ → Set Point)
    (hf : ∀ z, 0 ≤ f z)
    (hcofinal : ∀ N, ∃ n₁, ∀ n, n₁ ≤ n → S' N ⊆ S n) :
    ∀ N, ∃ n₁, ∀ n, n₁ ≤ n →
      mass f (S' N) ≤ mass f (S n) := by
  exact gap8 f S S' hf hcofinal

theorem gap22 (f : Point → ℝ) (S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I = ⊤) :
    ∀ M : ℝ, 0 < M →
      ∃ N, ENNReal.ofReal M < mass f (S' N) := by
  exact gap19 f S' I hlim hI

theorem gap23 (f : Point → ℝ) (S S' : ℕ → Set Point) (I : ℝ≥0∞)
    (hlim : Tendsto (fun n => mass f (S' n)) atTop (nhds I))
    (hI : I = ⊤)
    (hcofinal : ∀ N, ∃ n₁, ∀ n, n₁ ≤ n → S' N ⊆ S n) :
    ∀ M : ℝ, 0 < M →
      ∃ n₁, ∀ n, n₁ ≤ n →
        ENNReal.ofReal M < mass f (S n) := by
  intro M hM
  rcases gap22 f S' I hlim hI M hM with ⟨N, hN⟩
  rcases hcofinal N with ⟨n₁, hn₁⟩
  refine ⟨n₁, ?_⟩
  intro n hn
  have hm : mass f (S' N) ≤ mass f (S n) := by
    unfold mass
    exact lintegral_mono_set (hn₁ n hn)
  exact lt_of_lt_of_le hN hm

theorem gap24 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hI : I = ⊤)
    (hdiverges :
      ∀ M : ℝ, 0 < M →
        ∃ n₁, ∀ n, n₁ ≤ n →
          ENNReal.ofReal M < mass f (S n)) :
    Tendsto (fun n => mass f (S n)) atTop (nhds ⊤) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have ha_top : a ≠ ⊤ := ne_of_lt ha
    let M : ℝ := a.toReal + 1
    have hM : 0 < M := by
      dsimp [M]
      exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
    have haM : a < ENNReal.ofReal M := by
      apply (ENNReal.toReal_lt_toReal ha_top ENNReal.ofReal_ne_top).1
      rw [ENNReal.toReal_ofReal hM.le]
      dsimp [M]
      linarith
    rcases hdiverges M hM with ⟨n₁, hn₁⟩
    refine eventually_atTop.2 ⟨n₁, ?_⟩
    intro n hn
    exact lt_trans haM (hn₁ n hn)
  · intro b hb
    exact (not_lt_of_ge le_top hb).elim

theorem gap25 (f : Point → ℝ) (S : ℕ → Set Point) (I : ℝ≥0∞)
    (hfinite :
      I ≠ ⊤ → Tendsto (fun n => mass f (S n)) atTop (nhds I))
    (hinfinite :
      I = ⊤ → Tendsto (fun n => mass f (S n)) atTop (nhds ⊤)) :
    Tendsto (fun n => mass f (S n)) atTop (nhds I) := by
  by_cases hI : I = ⊤
  · simpa [hI] using hinfinite hI
  · exact hfinite hI

theorem gap26 (f : Point → ℝ) (Sseq : ℕ → Set Point) (S : Set Point)
    (hlimit :
      Tendsto (fun n => mass f (Sseq n)) atTop (nhds (mass f S))) :
    Tendsto (fun n => mass f (Sseq n)) atTop (nhds (mass f S)) := by
  exact hlimit

end

end ProofGap.Exercise4166
