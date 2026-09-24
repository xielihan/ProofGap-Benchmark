import ProofGapLean.Prelude.Full
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Floor

open Filter Topology

/-!
# Exercise 71

Semantic formalization of Exercise 71, gaps 1,...,25.
-/

namespace ProofGap.Exercise71

noncomputable section

def k (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Int.floor (p n) : ℝ)

def expSeq (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / u n) (u n)

def kCore (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / k p n) (k p n)

def kUpper (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / k p n) (k p n + 1)

def kLower (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (k p n + 1)) (k p n)

def kLowerProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (k p n + 1)) (k p n + 1) *
    (1 + 1 / (k p n + 1))⁻¹

def negativeTransform (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 - 1 / p n) (-p n)

def ratioTransform (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (p n / (p n - 1)) (p n)

def shiftedTransform (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (p n - 1)) (p n - 1) *
    (1 + 1 / (p n - 1))

/-- Exercise 71, gap 1. -/
theorem gap1 (p : ℕ → ℝ) :
    ∀ n : ℕ, k p n ≤ p n := by
  intro n
  exact_mod_cast Int.floor_le (p n)

/-- Exercise 71, gap 2. -/
theorem gap2 (p : ℕ → ℝ) :
    ∀ n : ℕ, p n < k p n + 1 := by
  intro n
  unfold k
  exact_mod_cast Int.lt_floor_add_one (p n)

/-- Exercise 71, gap 3. -/
theorem gap3 (p : ℕ → ℝ) :
    ∀ n : ℕ, k p n < k p n + 1 := by
  intro n
  linarith

/-- Exercise 71, gap 4. -/
theorem gap4
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    Tendsto (k p) atTop (atTop : Filter ℝ) := by
  unfold k
  exact tendsto_intCast_atTop_atTop.comp
    ((tendsto_floor_atTop (α := ℝ)).comp hp)

/-- Exercise 71, gap 5; the cited Exercise 69 limit is explicit. -/
theorem gap5
    (p : ℕ → ℝ) (e : ℝ)
    (hbase : Tendsto
      (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (𝓝 e))
    (hk : Tendsto (k p) atTop (atTop : Filter ℝ)) :
    Tendsto (kCore p) atTop (𝓝 e) := by
  let m : ℕ → ℕ := fun n => ⌊p n⌋₊
  have hm : Tendsto m atTop atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp
      (by
        exact tendsto_atTop_mono' _ (Filter.Eventually.of_forall fun n =>
          gap1 p n) hk)
  have hcomp :
      Tendsto
        (fun n : ℕ => (1 + 1 / (m n : ℝ)) ^ m n)
        atTop (𝓝 e) := by
    simpa [Function.comp_def] using hbase.comp hm
  apply hcomp.congr'
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  have hpn : 0 ≤ p n := (gap1 p n).trans' hkn.le
  have hfloor : 0 ≤ ⌊p n⌋ := Int.floor_nonneg.mpr hpn
  have hkm : k p n = (m n : ℝ) := by
    unfold k m
    rw [← Int.floor_toNat]
    norm_cast
    exact (Int.toNat_of_nonneg hfloor).symm
  unfold kCore
  rw [hkm]
  exact (Real.rpow_natCast (1 + 1 / (m n : ℝ)) (m n)).symm

/-- Exercise 71, gap 6; positivity holds eventually. -/
theorem gap6
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, 1 / k p n ≥ 1 / p n := by
  have hk := gap4 p hp
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  exact one_div_le_one_div_of_le hkn (gap1 p n)

/-- Exercise 71, gap 7; positivity holds eventually. -/
theorem gap7
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, 1 / p n > 1 / (k p n + 1) := by
  filter_upwards [hp.eventually_gt_atTop 0] with n hpn
  exact one_div_lt_one_div_of_lt hpn (gap2 p n)

/-- Exercise 71, gap 8; positivity holds eventually. -/
theorem gap8
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, 1 / k p n > 1 / (k p n + 1) := by
  have hk := gap4 p hp
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  exact one_div_lt_one_div_of_lt hkn (gap3 p n)

/-- Exercise 71, gap 9; the comparison is eventual. -/
theorem gap9
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, kUpper p n > expSeq p n := by
  have hk := gap4 p hp
  filter_upwards [hk.eventually_gt_atTop 0, hp.eventually_gt_atTop 0,
    gap6 p hp] with n hkn hpn hrecip
  let A : ℝ := 1 + 1 / p n
  let B : ℝ := 1 + 1 / k p n
  have hA : 1 < A := by
    dsimp [A]
    have : 0 < 1 / p n := one_div_pos.mpr hpn
    linarith
  have hAB : A ≤ B := by
    dsimp [A, B]
    linarith
  have hexp :
      A ^ p n < A ^ (k p n + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt hA (gap2 p n)
  have hbase :
      A ^ (k p n + 1) ≤ B ^ (k p n + 1) :=
    Real.rpow_le_rpow (zero_le_one.trans hA.le) hAB (by linarith)
  simpa [expSeq, kUpper, A, B, Real.rpow_eq_pow] using
    hexp.trans_le hbase

/-- Exercise 71, gap 10; the comparison is eventual. -/
theorem gap10
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, expSeq p n > kLower p n := by
  have hk := gap4 p hp
  filter_upwards [hk.eventually_gt_atTop 0, hp.eventually_gt_atTop 0,
    gap7 p hp] with n hkn hpn hrecip
  let A : ℝ := 1 + 1 / p n
  let B : ℝ := 1 + 1 / (k p n + 1)
  have hB : 1 < B := by
    dsimp [B]
    have : 0 < 1 / (k p n + 1) := one_div_pos.mpr (by linarith)
    linarith
  have hBA : B < A := by
    dsimp [A, B]
    linarith
  have hexp :
      B ^ k p n ≤ B ^ p n :=
    Real.rpow_le_rpow_of_exponent_le hB.le (gap1 p n)
  have hbase :
      B ^ p n < A ^ p n :=
    Real.rpow_lt_rpow (zero_le_one.trans hB.le) hBA hpn
  simpa [expSeq, kLower, A, B, Real.rpow_eq_pow] using
    hexp.trans_lt hbase

/-- Exercise 71, gap 11; the comparison is eventual. -/
theorem gap11
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, kUpper p n > kLower p n := by
  filter_upwards [gap9 p hp, gap10 p hp] with n hu hl
  exact hl.trans hu

/-- Exercise 71, gap 12. -/
theorem gap12
    (p : ℕ → ℝ) (e : ℝ)
    (h : Tendsto (kUpper p) atTop (𝓝 e)) :
    Tendsto (kUpper p) atTop (𝓝 e) := by
  exact h

/-- Exercise 71, gap 13; equality of raw limits becomes a pointwise identity. -/
theorem gap13
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, kLower p n = kLowerProduct p n := by
  have hk := gap4 p hp
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  let B : ℝ := 1 + 1 / (k p n + 1)
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < 1 / (k p n + 1) := one_div_pos.mpr (by linarith)
    linarith
  have hident :
      B ^ k p n = B ^ (k p n + 1) * B⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hB]
    congr 1
    ring
  simpa [kLower, kLowerProduct, B, Real.rpow_eq_pow] using hident

/-- Exercise 71, gap 14. -/
theorem gap14
    (p : ℕ → ℝ) (e : ℝ)
    (h : Tendsto (kLowerProduct p) atTop (𝓝 e)) :
    Tendsto (kLowerProduct p) atTop (𝓝 e) := by
  exact h

/-- Exercise 71, gap 15. -/
theorem gap15
    (p : ℕ → ℝ) (e : ℝ)
    (hid : ∀ᶠ n in atTop, kLower p n = kLowerProduct p n)
    (h : Tendsto (kLowerProduct p) atTop (𝓝 e)) :
    Tendsto (kLower p) atTop (𝓝 e) := by
  exact h.congr' (hid.mono fun _ hn => hn.symm)

/-- Exercise 71, gap 16; the squeeze assumptions are explicit. -/
theorem gap16
    (p : ℕ → ℝ) (e : ℝ)
    (hlower : Tendsto (kLower p) atTop (𝓝 e))
    (hupper : Tendsto (kUpper p) atTop (𝓝 e))
    (hl : ∀ᶠ n in atTop, kLower p n ≤ expSeq p n)
    (hu : ∀ᶠ n in atTop, expSeq p n ≤ kUpper p n) :
    Tendsto (expSeq p) atTop (𝓝 e) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper hl hu

/-- Exercise 71, gap 17; `q = -p` gives a pointwise identity. -/
theorem gap17
    (p q : ℕ → ℝ)
    (hqp : ∀ n : ℕ, q n = -p n) :
    ∀ n : ℕ, expSeq q n = negativeTransform p n := by
  intro n
  unfold expSeq negativeTransform
  rw [hqp]
  congr 2
  field_simp

/-- Exercise 71, gap 18; the algebraic transform is eventual. -/
theorem gap18
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, negativeTransform p n = ratioTransform p n := by
  filter_upwards [hp.eventually_gt_atTop 1] with n hpn
  let A : ℝ := 1 - 1 / p n
  let B : ℝ := p n / (p n - 1)
  have hA : 0 < A := by
    dsimp [A]
    have : 1 / p n < 1 := by
      rw [div_lt_one (by linarith : 0 < p n)]
      linarith
    linarith
  have hbase : A⁻¹ = B := by
    dsimp [A, B]
    field_simp
  have hid := Real.rpow_neg_eq_inv_rpow A (p n)
  rw [hbase] at hid
  simpa [negativeTransform, ratioTransform, A, B, Real.rpow_eq_pow] using hid

/-- Exercise 71, gap 19; the algebraic transform is eventual. -/
theorem gap19
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (atTop : Filter ℝ)) :
    ∀ᶠ n in atTop, ratioTransform p n = shiftedTransform p n := by
  filter_upwards [hp.eventually_gt_atTop 1] with n hpn
  let A : ℝ := p n / (p n - 1)
  let B : ℝ := 1 + 1 / (p n - 1)
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < 1 / (p n - 1) := one_div_pos.mpr (by linarith)
    linarith
  have hbase : A = B := by
    have hpm1 : p n - 1 ≠ 0 := by linarith
    dsimp [A, B]
    field_simp [hpm1]
    ring
  have hid : B ^ p n = B ^ (p n - 1) * B := by
    calc
      B ^ p n = B ^ ((p n - 1) + 1) := by congr 1 <;> ring
      _ = B ^ (p n - 1) * B := Real.rpow_add_one hB.ne' _
  simpa [ratioTransform, shiftedTransform, A, B, hbase,
    Real.rpow_eq_pow] using hid

/-- Exercise 71, gap 20. -/
theorem gap20
    (p : ℕ → ℝ) (e : ℝ)
    (h : Tendsto (shiftedTransform p) atTop (𝓝 e)) :
    Tendsto (shiftedTransform p) atTop (𝓝 e) := by
  exact h

/-- Exercise 71, gap 21. -/
theorem gap21
    (p q : ℕ → ℝ) (e : ℝ)
    (hqp : ∀ n : ℕ, q n = -p n)
    (hneg : Tendsto (negativeTransform p) atTop (𝓝 e)) :
    Tendsto (expSeq q) atTop (𝓝 e) := by
  exact hneg.congr' (Filter.Eventually.of_forall fun n => (gap17 p q hqp n).symm)

/-- Exercise 71, gap 22; equal limits are represented by a common value. -/
theorem gap22
    (p q : ℕ → ℝ) (e : ℝ)
    (hp : Tendsto (expSeq p) atTop (𝓝 e))
    (hq : Tendsto (expSeq q) atTop (𝓝 e)) :
    ∃ L : ℝ,
      Tendsto (expSeq p) atTop (𝓝 L) ∧
      Tendsto (expSeq q) atTop (𝓝 L) := by
  exact ⟨e, hp, hq⟩

/-- Exercise 71, gap 23. -/
theorem gap23
    (q : ℕ → ℝ) (e : ℝ)
    (hq : Tendsto (expSeq q) atTop (𝓝 e)) :
    Tendsto (expSeq q) atTop (𝓝 e) := by
  exact hq

/-- Exercise 71, gap 24. -/
theorem gap24
    (p : ℕ → ℝ) (e : ℝ)
    (hp : Tendsto (expSeq p) atTop (𝓝 e)) :
    Tendsto (expSeq p) atTop (𝓝 e) := by
  exact hp

/-- Exercise 71, gap 25. -/
theorem gap25
    (p q : ℕ → ℝ) (e : ℝ)
    (hp : Tendsto (expSeq p) atTop (𝓝 e))
    (hq : Tendsto (expSeq q) atTop (𝓝 e)) :
    (∃ L : ℝ,
      Tendsto (expSeq p) atTop (𝓝 L) ∧
      Tendsto (expSeq q) atTop (𝓝 L)) ∧
      Tendsto (expSeq q) atTop (𝓝 e) := by
  exact ⟨⟨e, hp, hq⟩, hq⟩

end

end ProofGap.Exercise71
