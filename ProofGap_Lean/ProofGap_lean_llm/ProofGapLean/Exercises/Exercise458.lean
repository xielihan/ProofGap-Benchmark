import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise458

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) - Real.sqrt x
def rationalized (x : ℝ) : ℝ :=
  Real.sqrt (x + Real.sqrt x) /
    (Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) + Real.sqrt x)
def normalized (x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.sqrt (1 / x)) /
    (1 + Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))))
def HasLimitAtPosInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |g x - L| < ε

/-- Exercise 458, gap 1. -/
private theorem hasLimitAtPosInfinity_congr
    {f g : ℝ → ℝ} {L : ℝ}
    (hfg : ∃ A > 0, ∀ x, A < x → f x = g x) :
    HasLimitAtPosInfinity f L ↔ HasLimitAtPosInfinity g L := by
  rcases hfg with ⟨A, hA, hfg⟩
  constructor
  · intro hf ε hε
    rcases hf ε hε with ⟨N, hN, hfN⟩
    refine ⟨max A N, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
    intro x hx
    have hAx : A < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hNx : N < x := lt_of_le_of_lt (le_max_right _ _) hx
    rw [← hfg x hAx]
    exact hfN x hNx
  · intro hg ε hε
    rcases hg ε hε with ⟨N, hN, hgN⟩
    refine ⟨max A N, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
    intro x hx
    have hAx : A < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hNx : N < x := lt_of_le_of_lt (le_max_right _ _) hx
    rw [hfg x hAx]
    exact hgN x hNx

private theorem hasLimitAtPosInfinity_of_tendsto
    {g : ℝ → ℝ} {L : ℝ}
    (h : Filter.Tendsto g Filter.atTop (nhds L)) :
    HasLimitAtPosInfinity g L := by
  intro ε hε
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, dist (g x) L < ε :=
    (Metric.tendsto_nhds.1 h) ε hε
  rcases Filter.eventually_atTop.1 hevent with ⟨A, hA⟩
  refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hAx : A ≤ x :=
    le_trans (le_max_right (1 : ℝ) A) (le_of_lt hx)
  simpa only [Real.dist_eq] using hA x hAx

private theorem tendsto_one_div_atTop_local :
    Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  refine Filter.eventually_atTop.2 ⟨1 / ε + 1, ?_⟩
  intro x hx
  have hboundPos : 0 < 1 / ε + 1 := by positivity
  have hxPos : 0 < x := lt_of_lt_of_le hboundPos hx
  rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hxPos)]
  apply (div_lt_iff₀ hxPos).2
  have hmul : ε * (1 / ε + 1) ≤ ε * x :=
    mul_le_mul_of_nonneg_left hx hε.le
  have heq : ε * (1 / ε + 1) = 1 + ε := by
    calc
      ε * (1 / ε + 1) = ε / ε + ε := by ring
      _ = 1 + ε := by rw [div_self (ne_of_gt hε)]
  rw [heq] at hmul
  nlinarith

private theorem tendsto_sqrt_of_tendsto
    {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Filter.Tendsto f l (nhds a)) :
    Filter.Tendsto (fun x => Real.sqrt (f x)) l (nhds (Real.sqrt a)) := by
  have hsqrt :
      Filter.Tendsto Real.sqrt (nhds a) (nhds (Real.sqrt a)) :=
    Real.continuous_sqrt.continuousAt
  simpa only [Function.comp_apply] using hsqrt.comp h

theorem gap1 :
    HasLimitAtPosInfinity original (1 / 2) ↔
      HasLimitAtPosInfinity rationalized (1 / 2) := by
  apply hasLimitAtPosInfinity_congr
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx1
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hx0 : 0 ≤ x := hx.le
  have houter0 :
      0 ≤ x + Real.sqrt (x + Real.sqrt x) :=
    add_nonneg hx0 (Real.sqrt_nonneg _)
  have houterPos :
      0 < Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) :=
    Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hx (Real.sqrt_nonneg _))
  have hden :
      Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) + Real.sqrt x ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg houterPos (Real.sqrt_nonneg _))
  rw [original, rationalized]
  apply (eq_div_iff hden).2
  calc
    (Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) - Real.sqrt x) *
        (Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) + Real.sqrt x) =
        Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) ^ 2 -
          Real.sqrt x ^ 2 := by ring
    _ = (x + Real.sqrt (x + Real.sqrt x)) - x := by
      rw [Real.sq_sqrt houter0, Real.sq_sqrt hx0]
    _ = Real.sqrt (x + Real.sqrt x) := by ring

/-- Exercise 458, gap 2. -/
theorem gap2 :
    HasLimitAtPosInfinity rationalized (1 / 2) ↔
      HasLimitAtPosInfinity normalized (1 / 2) := by
  apply hasLimitAtPosInfinity_congr
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx1
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hxne : x ≠ 0 := ne_of_gt hx
  let s : ℝ := Real.sqrt x
  let a : ℝ := Real.sqrt (1 / x)
  let u : ℝ := Real.sqrt (1 + a)
  let b : ℝ := Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))
  let v : ℝ := Real.sqrt (1 + b)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hsne : s ≠ 0 := by
    dsimp [s]
    exact ne_of_gt (Real.sqrt_pos.2 hx)
  have hsSq : s * s = x := by
    dsimp [s]
    exact Real.mul_self_sqrt hx.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have haSq : a ^ 2 = 1 / x := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hinvx : a = 1 / s := by
    dsimp [a, s]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hnumInside : x + s = x * (1 + a) := by
    rw [hinvx, ← hsSq]
    field_simp [hsne]
    <;> ring
  have hnum : Real.sqrt (x + Real.sqrt x) = s * u := by
    change Real.sqrt (x + s) = s * u
    rw [hnumInside, Real.sqrt_mul hx.le]
  have hpow : (1 / x ^ 3 : ℝ) = (1 / x) ^ 3 := by
    field_simp [hxne]
    <;> ring
  have hrootSq :
      Real.sqrt (1 / x ^ 3) ^ 2 = (a ^ 3) ^ 2 := by
    calc
      Real.sqrt (1 / x ^ 3) ^ 2 = 1 / x ^ 3 :=
        Real.sq_sqrt (by positivity)
      _ = (a ^ 3) ^ 2 := by
        rw [hpow, ← haSq]
        ring
  have hrootPow : Real.sqrt (1 / x ^ 3) = a ^ 3 := by
    nlinarith [Real.sqrt_nonneg (1 / x ^ 3), pow_nonneg ha0 3]
  have hbInside :
      1 / x + Real.sqrt (1 / x ^ 3) = (1 / x) * (1 + a) := by
    rw [hrootPow, ← haSq]
    ring
  have hb : b = a * u := by
    change Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)) =
      a * Real.sqrt (1 + a)
    rw [hbInside, Real.sqrt_mul (by positivity : 0 ≤ (1 / x : ℝ))]
  have houterInside : x + s * u = x * (1 + b) := by
    rw [hb, hinvx, ← hsSq]
    field_simp [hsne]
    <;> ring
  have houter : Real.sqrt (x + s * u) = s * v := by
    change Real.sqrt (x + s * u) = s * Real.sqrt (1 + b)
    rw [houterInside, Real.sqrt_mul hx.le]
  rw [rationalized, normalized]
  change Real.sqrt (x + s) /
      (Real.sqrt (x + Real.sqrt (x + s)) + s) = u / (1 + v)
  rw [hnum, houter]
  have hfactor : s * v + s = s * (1 + v) := by ring
  rw [hfactor]
  have hvne : 1 + v ≠ 0 := by
    have hv0 : 0 ≤ v := by
      dsimp [v]
      exact Real.sqrt_nonneg _
    linarith
  field_simp [hsne, hvne]
  <;> ring

/-- Exercise 458, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity normalized (1 / 2) := by
  have hInv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_local
  have hOne :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hInv3 :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ 3) Filter.atTop (nhds 0) := by
    simpa [one_div, inv_pow] using hInv.pow 3
  have hSqrtInv :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 / x))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_sqrt_of_tendsto hInv
  have hSqrtInv3 :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 / x ^ 3))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_sqrt_of_tendsto hInv3
  have hNumeratorInside :
      Filter.Tendsto (fun x : ℝ => 1 + Real.sqrt (1 / x))
        Filter.atTop (nhds 1) := by
    simpa using hOne.add hSqrtInv
  have hNumerator :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + Real.sqrt (1 / x)))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_sqrt_of_tendsto hNumeratorInside
  have hInner :
      Filter.Tendsto
        (fun x : ℝ => 1 / x + Real.sqrt (1 / x ^ 3))
        Filter.atTop (nhds 0) := by
    simpa using hInv.add hSqrtInv3
  have hInnerSqrt :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_sqrt_of_tendsto hInner
  have hDenominatorInside :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)))
        Filter.atTop (nhds 1) := by
    simpa using hOne.add hInnerSqrt
  have hOuterSqrt :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_sqrt_of_tendsto hDenominatorInside
  have hDenominatorRaw :
      Filter.Tendsto
        (fun x : ℝ =>
          1 + Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))))
        Filter.atTop (nhds ((1 : ℝ) + 1)) := by
    simpa using hOne.add hOuterSqrt
  have hOnePlusOne : (1 : ℝ) + 1 = 2 := by norm_num
  rw [hOnePlusOne] at hDenominatorRaw
  have hDenominator :
      Filter.Tendsto
        (fun x : ℝ =>
          1 + Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))))
        Filter.atTop (nhds 2) :=
    hDenominatorRaw
  have hNormalized :
      Filter.Tendsto normalized Filter.atTop (nhds (1 / 2)) := by
    unfold normalized
    simpa only [Pi.div_apply] using
      hNumerator.div hDenominator (by norm_num : (2 : ℝ) ≠ 0)
  exact hasLimitAtPosInfinity_of_tendsto hNormalized

end

end ProofGap.Exercise458
