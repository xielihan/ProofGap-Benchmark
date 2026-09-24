import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2570

noncomputable section

def scaled (u : ℕ → ℝ) (n : ℕ) : ℝ := (n : ℝ) * u n
def harmonic (n : ℕ) : ℝ := 1 / (n : ℝ)

def TailSummable (u : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  Summable (fun k : ℕ => u (k + n₀))

theorem gap1
    (u : ℕ → ℝ) (A : ℝ)
    (hlim : Tendsto (scaled u) atTop (nhds A))
    (hA : A ≠ 0) :
    ∀ n, scaled u n = u n / harmonic n := by
  intro n
  simp only [scaled, harmonic]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

theorem gap2
    (u : ℕ → ℝ) (A : ℝ)
    (hlim : Tendsto (scaled u) atTop (nhds A))
    (hA : A ≠ 0)
    (hquotient : ∀ n, scaled u n = u n / harmonic n) :
    A > 0 → ∀ ε : ℝ, 0 < ε → ε < A →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
        u n / harmonic n > A - ε ∧ A - ε > 0 := by
  intro hApos ε hε hεA
  have heventually : ∀ᶠ n in atTop, A - ε < scaled u n :=
    (tendsto_order.1 hlim).1 (A - ε) (sub_lt_self A hε)
  rcases (Filter.eventually_atTop.1 heventually) with ⟨N, hN⟩
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have hscaled : A - ε < scaled u n :=
    hN n (le_trans (le_max_right 1 N) hn)
  rw [hquotient n] at hscaled
  exact ⟨hscaled, sub_pos.mpr hεA⟩

theorem gap3
    (u : ℕ → ℝ) (A : ℝ)
    (hpositiveRatio : A > 0 → ∀ ε : ℝ, 0 < ε → ε < A →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
        u n / harmonic n > A - ε ∧ A - ε > 0) :
    A > 0 → ∀ ε : ℝ, 0 < ε → ε < A →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
        u n > (A - ε) * harmonic n ∧
          (A - ε) * harmonic n > 0 := by
  intro hA ε hε hεA
  rcases hpositiveRatio hA ε hε hεA with ⟨n₀, hn₀, hbound⟩
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn
  rcases hbound n hn with ⟨hratio, hcoeff⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hn₀.trans hn)
  have hharmonic : 0 < harmonic n := by
    simp [harmonic, Nat.cast_pos.mpr hnpos]
  exact ⟨(lt_div_iff₀ hharmonic).mp hratio, mul_pos hcoeff hharmonic⟩

theorem gap4
    (u : ℕ → ℝ) (A : ℝ) :
    A > 0 → Summable u → ∀ n₀ : ℕ, TailSummable u n₀ := by
  intro hA hu n₀
  exact (summable_nat_add_iff n₀).2 hu

theorem gap5
    (u : ℕ → ℝ) (A : ℝ)
    (hlower : A > 0 → ∀ ε : ℝ, 0 < ε → ε < A →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
        u n > (A - ε) * harmonic n ∧
          (A - ε) * harmonic n > 0)
    (huTail : A > 0 → Summable u →
      ∀ n₀ : ℕ, TailSummable u n₀) :
    A > 0 → Summable u →
      ∃ n₀ : ℕ, TailSummable harmonic n₀ := by
  intro hA hu
  have hhalfpos : 0 < A / 2 := half_pos hA
  have hhalflt : A / 2 < A := half_lt_self hA
  rcases hlower hA (A / 2) hhalfpos hhalflt with
    ⟨n₀, hn₀, hbound⟩
  have hutail : TailSummable u n₀ := huTail hA hu n₀
  have hscaled :
      Summable (fun k : ℕ => (A - A / 2) * harmonic (k + n₀)) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact (hbound (k + n₀) (n₀.le_add_left k)).2.le
    · intro k
      exact (hbound (k + n₀) (n₀.le_add_left k)).1.le
    · exact hutail
  refine ⟨n₀, ?_⟩
  have hcoeff : A - A / 2 ≠ 0 := ne_of_gt (sub_pos.mpr hhalflt)
  simpa [TailSummable, hcoeff] using
    hscaled.mul_left (A - A / 2)⁻¹

theorem gap6
    (u : ℕ → ℝ) (A : ℝ)
    (hharmonic : A > 0 → Summable u →
      ∃ n₀ : ℕ, TailSummable harmonic n₀)
    (hharmonicDiv : ¬ Summable harmonic) :
    A > 0 → Summable u → False := by
  intro hA hu
  rcases hharmonic hA hu with ⟨n₀, htail⟩
  apply hharmonicDiv
  exact (summable_nat_add_iff n₀).1 htail

theorem gap7
    (u : ℕ → ℝ) (A : ℝ)
    (hlim : Tendsto (scaled u) atTop (nhds A)) :
    A < 0 → ¬ Summable u := by
  intro hA hu
  let v : ℕ → ℝ := fun n => -u n
  have hvlim : Tendsto (scaled v) atTop (nhds (-A)) := by
    have hvfun : scaled v = fun n => -(scaled u n) := by
      funext n
      simp [v, scaled]
    rw [hvfun]
    exact hlim.neg
  have hvA : -A ≠ 0 := ne_of_gt (neg_pos.mpr hA)
  have hquotient := gap1 v (-A) hvlim hvA
  have hpositiveRatio := gap2 v (-A) hvlim hvA hquotient
  have hlower := gap3 v (-A) hpositiveRatio
  have hvTail := gap4 v (-A)
  have hharmonic := gap5 v (-A) hlower hvTail
  have hharmonicDiv : ¬ Summable harmonic := by
    unfold harmonic
    simpa only [one_div] using Real.not_summable_one_div_natCast
  have hvsum : Summable v := by
    simpa [v] using hu.neg
  exact gap6 v (-A) hharmonic hharmonicDiv (neg_pos.mpr hA) hvsum

theorem gap8
    (u : ℕ → ℝ) (A : ℝ)
    (hlim : Tendsto (scaled u) atTop (nhds A))
    (hA : A ≠ 0)
    (hpositive : A > 0 → Summable u → False)
    (hnegative : A < 0 → ¬ Summable u) :
    ¬ Summable u := by
  intro hu
  rcases lt_trichotomy A 0 with hneg | heq | hpos
  · exact hnegative hneg hu
  · exact hA heq
  · exact hpositive hpos hu

theorem gap9
    (u : ℕ → ℝ) (A : ℝ)
    (hlim : Tendsto (scaled u) atTop (nhds A))
    (hA : A ≠ 0)
    (hdiv : ¬ Summable u) :
    ¬ Summable u := by
  exact hdiv

end

end ProofGap.Exercise2570
