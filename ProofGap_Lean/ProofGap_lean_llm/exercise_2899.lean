import Mathlib

noncomputable section

namespace ProofGapBatch5

abbrev SeqR := ℕ → ℝ

def factR (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

def powerSeriesTerm (a : SeqR) (x0 : ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a n * (x - x0) ^ n

def powerSeriesSum (a : SeqR) (x0 : ℝ) (x s : ℝ) : Prop :=
  HasSum (fun n : ℕ => powerSeriesTerm a x0 x n) s

def HasInfiniteRadius (a : SeqR) : Prop :=
  ∀ r : ℝ, Summable (fun n : ℕ => |a n| * |r| ^ n)

def UniformlyHasSumOn (F : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ b : ℕ → ℝ,
    Summable b ∧
      (∀ n : ℕ, 0 ≤ b n) ∧
      (∀ n : ℕ, ∀ x ∈ s, |F n x| ≤ b n) ∧
      (∀ x ∈ s, HasSum (fun n : ℕ => F n x) (f x))

def iterDeriv (m : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  Nat.iterate deriv m f

def derivativeSeriesSum (a : SeqR) (x0 : ℝ) (m : ℕ) (x s : ℝ) : Prop :=
  HasSum
    (fun n : ℕ => if m ≤ n then factR n / factR (n - m) * a n * (x - x0) ^ (n - m) else 0)
    s

def taylorSeriesSum (f : ℝ → ℝ) (c x s : ℝ) : Prop :=
  HasSum (fun n : ℕ => iterDeriv n f c / factR n * (x - c) ^ n) s

namespace exercise_2899

variable (f : ℝ → ℝ) (a : SeqR) (x0 M L P center : ℝ) (Rem : ℕ → ℝ → ℝ)

theorem proof_gap_exercise_2899_1
    (hM : 0 < M)
    (hcoef : ∀ n : ℕ, 0 < n → |factR n * a n| < M) :
    ∀ n : ℕ, 0 < n → |a n| < M / factR n := by
  sorry

theorem proof_gap_exercise_2899_2
    (hcoef : ∀ n : ℕ, 0 < n → |a n| < M / factR n) :
    ∀ N : ℝ, 0 < N → x0 ∈ Set.Icc (-N) N →
      ∀ x : ℝ, ∀ N' : ℝ, ∀ n : ℕ,
        x ∈ Set.Icc (-N') N' → 0 < n →
          |a n * (x - x0) ^ n| < M / factR n * (2 * N') ^ n := by
  sorry

theorem proof_gap_exercise_2899_3 :
    ∀ N : ℝ, 0 < N → x0 ∈ Set.Icc (-N) N →
      Summable (fun n : ℕ => M / factR n * (2 * N) ^ n) := by
  sorry

theorem proof_gap_exercise_2899_4
    (hmajor : ∀ N : ℝ, 0 < N → x0 ∈ Set.Icc (-N) N →
      Summable (fun n : ℕ => M / factR n * (2 * N) ^ n))
    (hsum : ∀ x : ℝ, powerSeriesSum a x0 x (f x)) :
    ∀ N : ℝ, 0 < N → x0 ∈ Set.Icc (-N) N →
      UniformlyHasSumOn (fun n x => a n * (x - x0) ^ n) (Set.Icc (-N) N) f := by
  sorry

theorem proof_gap_exercise_2899_5
    (hunif : ∀ N : ℝ, 0 < N → x0 ∈ Set.Icc (-N) N →
      UniformlyHasSumOn (fun n x => a n * (x - x0) ^ n) (Set.Icc (-N) N) f) :
    HasInfiniteRadius a := by
  sorry

theorem proof_gap_exercise_2899_6
    (hradius : HasInfiniteRadius a) :
    ∀ c : ℝ, ∀ m : ℕ, 0 < m → DifferentiableAt ℝ (iterDeriv m f) c := by
  sorry

theorem proof_gap_exercise_2899_7
    (hdiff : ∀ c : ℝ, ∀ m : ℕ, 0 < m → DifferentiableAt ℝ (iterDeriv m f) c) :
    ∀ m : ℕ, 0 < m →
      ∀ x : ℝ, derivativeSeriesSum a x0 m x (iterDeriv m f x) := by
  sorry

theorem proof_gap_exercise_2899_8 :
    ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R → |x - x0| ≤ |x - center| + |center - x0| := by
  sorry

theorem proof_gap_exercise_2899_9
    (hL : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R → L = R + |center - x0|) :
    ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R → |x - center| + |center - x0| < L := by
  sorry

theorem proof_gap_exercise_2899_10
    (htri : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      |x - x0| ≤ |x - center| + |center - x0|)
    (hlt : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      |x - center| + |center - x0| < L) :
    ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R → |x - x0| < L := by
  sorry

theorem proof_gap_exercise_2899_11
    (hP : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      HasSum (fun s : ℕ => L ^ s / factR s) P) :
    ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R → ∃ C : ℝ, P < C := by
  sorry

theorem proof_gap_exercise_2899_12
    (hderiv : ∀ m : ℕ, 0 < m → ∀ x : ℝ, derivativeSeriesSum a x0 m x (iterDeriv m f x))
    (hP : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      HasSum (fun s : ℕ => L ^ s / factR s) P) :
    ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        ∀ m : ℕ, 0 < m → |iterDeriv m f x| ≤ M * P := by
  sorry

theorem proof_gap_exercise_2899_13
    (hRem : ∀ n : ℕ, ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      Rem n x = f x - Finset.sum (Finset.range (n + 1))
        (fun k : ℕ => iterDeriv k f center / factR k * (x - center) ^ k)) :
    ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
          Rem n x =
            iterDeriv (n + 1) f (center + θ * (x - center)) / factR (n + 1) *
              (x - center) ^ (n + 1) := by
  sorry

theorem proof_gap_exercise_2899_14
    (hlagrange : ∀ n : ℕ, ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        Rem n x =
          iterDeriv (n + 1) f (center + θ * (x - center)) / factR (n + 1) *
            (x - center) ^ (n + 1))
    (hderivBound : ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      ∀ m : ℕ, 0 < m → |iterDeriv m f x| ≤ M * P) :
    ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        |Rem n x| ≤ (M * P) / factR (n + 1) * R ^ (n + 1) := by
  sorry

theorem proof_gap_exercise_2899_15 :
    ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        Tendsto (fun n : ℕ => R ^ (n + 1) / factR (n + 1)) Filter.atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2899_16
    (hRemBound : ∀ n : ℕ, ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      |Rem n x| ≤ (M * P) / factR (n + 1) * R ^ (n + 1)) :
    ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        Tendsto (fun n : ℕ => Rem n x) Filter.atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2899_17
    (hRemZero : ∀ n : ℕ, ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      Tendsto (fun n : ℕ => Rem n x) Filter.atTop (𝓝 0)) :
    ∀ k : ℕ, ∀ R : ℝ, 0 < R →
      ∀ x : ℝ, |x - center| < R →
        taylorSeriesSum f center x (f x) := by
  sorry

theorem proof_gap_exercise_2899_18
    (hlocal : ∀ k : ℕ, ∀ R : ℝ, 0 < R → ∀ x : ℝ, |x - center| < R →
      taylorSeriesSum f center x (f x)) :
    ∀ n : ℕ, ∀ c x : ℝ, taylorSeriesSum f c x (f x) := by
  sorry

theorem proof_gap_exercise_2899_19
    (hdiff : ∀ c : ℝ, ∀ m : ℕ, 0 < m → DifferentiableAt ℝ (iterDeriv m f) c)
    (htaylor : ∀ n : ℕ, ∀ c x : ℝ, taylorSeriesSum f c x (f x)) :
    (∀ c : ℝ, ∀ m : ℕ, 0 < m → DifferentiableAt ℝ (iterDeriv m f) c) ∧
      (∀ c x : ℝ, taylorSeriesSum f c x (f x)) := by
  sorry

end exercise_2899

end ProofGapBatch5
