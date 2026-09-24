import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Fin
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3673

noncomputable section

open scoped BigOperators

def dotProduct {n : ℕ} (a x : Fin n → ℝ) : ℝ :=
  ∑ i, a i * x i

def powerSum {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.rpow (x i) p

def holderBound {n : ℕ}
    (k k' : ℝ) (a x : Fin n → ℝ) : ℝ :=
  Real.rpow (powerSum k a) (1 / k) *
    Real.rpow (powerSum k' x) (1 / k')

def alphaSum {n : ℕ} (k : ℝ) (a : Fin n → ℝ) : ℝ :=
  powerSum k a

def extremalCandidate {n : ℕ}
    (k A : ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => A / alphaSum k a * Real.rpow (a i) (k - 1)

def stationary {n : ℕ}
    (k k' A : ℝ) (a x : Fin n → ℝ) (lambda : ℝ) : Prop :=
  (∀ i,
    Real.rpow (alphaSum k a) (1 / k) *
      Real.rpow (powerSum k' x) (1 / k' - 1) *
      Real.rpow (x i) (k' - 1) - lambda * a i = 0) ∧
  dotProduct a x = A ∧
  ∀ i, 0 ≤ x i

def truncateLast {m : ℕ} (x : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => x i.castSucc

private theorem powerSum_nonneg {n : ℕ} (p : ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ powerSum p x := by
  unfold powerSum
  exact Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (hx i) p)

private theorem powerSum_pos_of_pos_component {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∃ i, 0 < x i) : 0 < powerSum p x := by
  unfold powerSum
  apply Finset.sum_pos'
  · intro i hi
    exact Real.rpow_nonneg (hx i) p
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos hi p⟩

private theorem alphaSum_pos_of_pos_component {n : ℕ} (k : ℝ)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∃ i, 0 < a i) : 0 < alphaSum k a := by
  unfold alphaSum
  exact powerSum_pos_of_pos_component k a ha h

private theorem mul_rpow_sub_one (k : ℝ) (hk : 1 < k) (t : ℝ)
    (ht : 0 ≤ t) : t * Real.rpow t (k - 1) = Real.rpow t k := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [Real.zero_rpow (by linarith : k - 1 ≠ 0),
      Real.zero_rpow (by linarith : k ≠ 0)]
  · calc
      t * Real.rpow t (k - 1) =
          Real.rpow t 1 * Real.rpow t (k - 1) := by simp
      _ = Real.rpow t (1 + (k - 1)) :=
        (Real.rpow_add ht 1 (k - 1)).symm
      _ = Real.rpow t k := by ring_nf

private theorem dotProduct_extremal {n : ℕ} (k A : ℝ) (a : Fin n → ℝ)
    (hk : 1 < k) (ha : ∀ i, 0 ≤ a i) (halpha : alphaSum k a ≠ 0) :
    dotProduct a (extremalCandidate k A a) = A := by
  unfold dotProduct extremalCandidate
  have hsum :
      (∑ i, a i * (A / alphaSum k a * Real.rpow (a i) (k - 1))) =
        (A / alphaSum k a) * alphaSum k a := by
    calc
      (∑ i, a i * (A / alphaSum k a * Real.rpow (a i) (k - 1))) =
          ∑ i, (A / alphaSum k a) *
            (a i * Real.rpow (a i) (k - 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, (A / alphaSum k a) * Real.rpow (a i) k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_rpow_sub_one k hk (a i) (ha i)]
      _ = (A / alphaSum k a) * ∑ i, Real.rpow (a i) k := by
        rw [Finset.mul_sum]
      _ = (A / alphaSum k a) * alphaSum k a := by rfl
  rw [hsum]
  exact div_mul_cancel₀ A halpha

theorem gap1 (k k' : ℝ) (a x : Fin 1 → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    holderBound k k' a x = dotProduct a x := by
  have hk0 : k ≠ 0 := by linarith
  have hk'0 : k' ≠ 0 := by linarith
  have hk_inv : k * (1 / k) = 1 := by field_simp
  have hk'_inv : k' * (1 / k') = 1 := by field_simp
  have haRoot :
      Real.rpow (Real.rpow (a 0) k) (1 / k) = a 0 := by
    calc
      Real.rpow (Real.rpow (a 0) k) (1 / k) =
          Real.rpow (a 0) (k * (1 / k)) :=
        (Real.rpow_mul (ha 0) k (1 / k)).symm
      _ = Real.rpow (a 0) 1 := by rw [hk_inv]
      _ = a 0 := by simp
  have hxRoot :
      Real.rpow (Real.rpow (x 0) k') (1 / k') = x 0 := by
    calc
      Real.rpow (Real.rpow (x 0) k') (1 / k') =
          Real.rpow (x 0) (k' * (1 / k')) :=
        (Real.rpow_mul (hx 0) k' (1 / k')).symm
      _ = Real.rpow (x 0) 1 := by rw [hk'_inv]
      _ = x 0 := by simp
  simp only [holderBound, powerSum, dotProduct, Fin.sum_univ_one]
  rw [haRoot, hxRoot]

theorem gap2 (a x : Fin 1 → ℝ) :
    ∀ A, dotProduct a x = A → a 0 * x 0 = A := by
  intro A hA
  simpa [dotProduct] using hA

theorem gap3 (k k' A : ℝ) (a x : Fin 1 → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hA : dotProduct a x = A) :
    holderBound k k' a x = A := by
  rw [gap1 k k' a x hk hk' hconj ha hx]
  exact hA

theorem gap4 {m : ℕ} (k k' : ℝ) (a x : Fin m → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    dotProduct a x ≤ holderBound k k' a x := by
  have hpq : k.HolderConjugate k' := by
    exact ⟨by simpa [one_div] using hconj, by linarith, by linarith⟩
  simpa [dotProduct, holderBound, powerSum, abs_of_nonneg, ha, hx, one_div] using
    (Real.inner_le_Lp_mul_Lq
      (s := (Finset.univ : Finset (Fin m)))
      (p := k) (q := k') (f := a) (g := x) hpq)

theorem gap5 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (lambda : ℝ) (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 < a i) (hstat : stationary k k' A a x lambda) :
    ∃ mu : ℝ, ∀ i, x i = mu * Real.rpow (a i) (k - 1) := by
  have hk0 : k ≠ 0 := by linarith
  have hk'0 : k' ≠ 0 := by linarith
  have hrel : (k' - 1) * (k - 1) = 1 := by
    have hc := hconj
    field_simp [hk0, hk'0] at hc
    nlinarith
  have hdot : dotProduct a x = A := hstat.2.1
  have hx : ∀ i, 0 ≤ x i := hstat.2.2
  have hAnonneg : 0 ≤ A := by
    rw [← hdot]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (le_of_lt (ha i)) (hx i))
  rcases hAnonneg.eq_or_lt with hAzero | hApos
  · refine ⟨0, ?_⟩
    intro i
    have hsum : (∑ j, a j * x j) = 0 := by
      simpa [dotProduct, hAzero] using hdot
    have hterm : a i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
          mul_nonneg (le_of_lt (ha j)) (hx j))).mp
        hsum i (Finset.mem_univ i)
    have hxi : x i = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (ha i))
    simp [hxi]
  · have hn : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp [dotProduct] at hdot
      linarith
    have hex : ∃ i, 0 < x i := by
      by_contra hnone
      have hall : ∀ i, x i = 0 := by
        intro i
        apply le_antisymm
        · exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
        · exact hx i
      simp [dotProduct, hall] at hdot
      linarith
    have halpha : 0 < alphaSum k a :=
      alphaSum_pos_of_pos_component k a
        (fun i => le_of_lt (ha i)) ⟨⟨0, hn⟩, ha ⟨0, hn⟩⟩
    have hpower : 0 < powerSum k' x :=
      powerSum_pos_of_pos_component k' x hx hex
    let C : ℝ :=
      Real.rpow (alphaSum k a) (1 / k) *
        Real.rpow (powerSum k' x) (1 / k' - 1)
    have hC : 0 < C := by
      dsimp [C]
      exact mul_pos
        (Real.rpow_pos_of_pos halpha _)
        (Real.rpow_pos_of_pos hpower _)
    let d : ℝ := lambda / C
    have hpoweq : ∀ i, Real.rpow (x i) (k' - 1) = d * a i := by
      intro i
      have hi := hstat.1 i
      change C * Real.rpow (x i) (k' - 1) - lambda * a i = 0 at hi
      have hmul : C * Real.rpow (x i) (k' - 1) = lambda * a i :=
        sub_eq_zero.mp hi
      dsimp [d]
      calc
        Real.rpow (x i) (k' - 1) = (lambda * a i) / C := by
          apply (eq_div_iff hC.ne').2
          simpa [mul_comm] using hmul
        _ = (lambda / C) * a i := by ring
    have hd : 0 ≤ d := by
      let i : Fin n := ⟨0, hn⟩
      have hi := hpoweq i
      have hp : 0 ≤ Real.rpow (x i) (k' - 1) :=
        Real.rpow_nonneg (hx i) (k' - 1)
      by_contra hdn
      have hdlt : d < 0 := lt_of_not_ge hdn
      have hneg : d * a i < 0 := mul_neg_of_neg_of_pos hdlt (ha i)
      rw [← hi] at hneg
      exact (not_lt_of_ge hp) hneg
    refine ⟨Real.rpow d (k - 1), ?_⟩
    intro i
    calc
      x i = Real.rpow (x i) 1 := by simp
      _ = Real.rpow (x i) ((k' - 1) * (k - 1)) := by rw [hrel]
      _ = Real.rpow (Real.rpow (x i) (k' - 1)) (k - 1) :=
        Real.rpow_mul (hx i) (k' - 1) (k - 1)
      _ = Real.rpow (d * a i) (k - 1) := by rw [hpoweq i]
      _ = Real.rpow d (k - 1) * Real.rpow (a i) (k - 1) :=
        Real.mul_rpow hd (le_of_lt (ha i))

theorem gap6 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (lambda : ℝ) (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 < a i) (hApos : 0 < A)
    (hstat : stationary k k' A a x lambda) :
    ∃ mu : ℝ, mu = A / alphaSum k a ∧
      ∀ i, x i = mu * Real.rpow (a i) (k - 1) := by
  obtain ⟨mu, hmu⟩ :=
    gap5 k k' A a x lambda hk hk' hconj ha hstat
  have hdot : dotProduct a x = A := hstat.2.1
  have hmul : mu * alphaSum k a = A := by
    rw [← hdot]
    unfold dotProduct alphaSum powerSum
    calc
      mu * ∑ i, Real.rpow (a i) k =
          ∑ i, mu * Real.rpow (a i) k := by rw [Finset.mul_sum]
      _ = ∑ i, a i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hmu i]
        calc
          mu * Real.rpow (a i) k =
              mu * (a i * Real.rpow (a i) (k - 1)) := by
            rw [mul_rpow_sub_one k hk (a i) (le_of_lt (ha i))]
          _ = a i * (mu * Real.rpow (a i) (k - 1)) := by ring
  have halpha : alphaSum k a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmul
    linarith
  refine ⟨mu, ?_, hmu⟩
  apply (eq_div_iff halpha).2
  exact hmul

theorem gap7 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (lambda : ℝ) (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 < a i) (hApos : 0 < A)
    (hstat : stationary k k' A a x lambda) :
    ∀ i, x i = extremalCandidate k A a i := by
  obtain ⟨mu, hmu, hx⟩ :=
    gap6 k k' A a x lambda hk hk' hconj ha hApos hstat
  intro i
  rw [hx i, hmu]
  rfl

theorem gap8 {n : ℕ} (hn : 0 < n) (k k' A : ℝ)
    (a : Fin n → ℝ) (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 < a i) (hApos : 0 < A) :
    {x | ∃ lambda, stationary k k' A a x lambda} =
      ({extremalCandidate k A a} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · rintro ⟨lambda, hstat⟩
    have hx := gap7 k k' A a x lambda hk hk' hconj ha hApos hstat
    have heq : x = extremalCandidate k A a := funext hx
    simpa using heq
  · intro hxmem
    have hxEq : x = extremalCandidate k A a := by simpa using hxmem
    subst x
    have halpha : 0 < alphaSum k a :=
      alphaSum_pos_of_pos_component k a
        (fun i => le_of_lt (ha i)) ⟨⟨0, hn⟩, ha ⟨0, hn⟩⟩
    have hk0 : k ≠ 0 := by linarith
    have hk'0 : k' ≠ 0 := by linarith
    have hrel : (k - 1) * (k' - 1) = 1 := by
      have hc := hconj
      field_simp [hk0, hk'0] at hc
      nlinarith
    let c : ℝ := A / alphaSum k a
    have hcpos : 0 < c := div_pos hApos halpha
    let B : ℝ :=
      Real.rpow (alphaSum k a) (1 / k) *
        Real.rpow (powerSum k' (extremalCandidate k A a)) (1 / k' - 1)
    let lambda : ℝ := B * Real.rpow c (k' - 1)
    refine ⟨lambda, ?_,
      dotProduct_extremal k A a hk (fun i => le_of_lt (ha i)) halpha.ne', ?_⟩
    · intro i
      have hmul :
          Real.rpow (c * Real.rpow (a i) (k - 1)) (k' - 1) =
            Real.rpow c (k' - 1) *
              Real.rpow (Real.rpow (a i) (k - 1)) (k' - 1) :=
        Real.mul_rpow (le_of_lt hcpos)
          (Real.rpow_nonneg (le_of_lt (ha i)) (k - 1))
      have hnested :
          Real.rpow (Real.rpow (a i) (k - 1)) (k' - 1) = a i := by
        calc
          Real.rpow (Real.rpow (a i) (k - 1)) (k' - 1) =
              Real.rpow (a i) ((k - 1) * (k' - 1)) :=
            (Real.rpow_mul (le_of_lt (ha i)) (k - 1) (k' - 1)).symm
          _ = Real.rpow (a i) 1 := by rw [hrel]
          _ = a i := by simp
      have hp :
          Real.rpow (extremalCandidate k A a i) (k' - 1) =
            Real.rpow c (k' - 1) * a i := by
        unfold extremalCandidate
        change Real.rpow (c * Real.rpow (a i) (k - 1)) (k' - 1) = _
        rw [hmul, hnested]
      change B * Real.rpow (extremalCandidate k A a i) (k' - 1) -
          lambda * a i = 0
      rw [hp]
      dsimp [lambda]
      ring
    · intro i
      unfold extremalCandidate
      exact mul_nonneg (le_of_lt hcpos)
        (Real.rpow_nonneg (le_of_lt (ha i)) (k - 1))

theorem gap9 {n : ℕ} (hn : 0 < n) (k k' A : ℝ)
    (a : Fin n → ℝ) (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hApos : 0 < A)
    (halpha : 0 < alphaSum k a) :
    holderBound k k' a (extremalCandidate k A a) = A := by
  have hk0 : k ≠ 0 := by linarith
  have hk'0 : k' ≠ 0 := by linarith
  have hrel : (k - 1) * k' = k := by
    have hc := hconj
    field_simp [hk0, hk'0] at hc
    nlinarith
  let alpha : ℝ := alphaSum k a
  let c : ℝ := A / alpha
  have halpha' : 0 < alpha := by simpa [alpha] using halpha
  have hcpos : 0 < c := div_pos hApos halpha'
  have hpower :
      powerSum k' (extremalCandidate k A a) =
        Real.rpow c k' * alpha := by
    unfold powerSum extremalCandidate
    change (∑ i, Real.rpow (c * Real.rpow (a i) (k - 1)) k') = _
    calc
      (∑ i, Real.rpow (c * Real.rpow (a i) (k - 1)) k') =
          ∑ i, Real.rpow c k' * Real.rpow (a i) k := by
        apply Finset.sum_congr rfl
        intro i hi
        have hmul :
            Real.rpow (c * Real.rpow (a i) (k - 1)) k' =
              Real.rpow c k' *
                Real.rpow (Real.rpow (a i) (k - 1)) k' :=
          Real.mul_rpow (le_of_lt hcpos)
            (Real.rpow_nonneg (ha i) (k - 1))
        have hnested :
            Real.rpow (Real.rpow (a i) (k - 1)) k' =
              Real.rpow (a i) k := by
          calc
            Real.rpow (Real.rpow (a i) (k - 1)) k' =
                Real.rpow (a i) ((k - 1) * k') :=
              (Real.rpow_mul (ha i) (k - 1) k').symm
            _ = Real.rpow (a i) k := by rw [hrel]
        rw [hmul, hnested]
      _ = Real.rpow c k' * ∑ i, Real.rpow (a i) k := by
        rw [Finset.mul_sum]
      _ = Real.rpow c k' * alpha := by rfl
  have hk'_inv : k' * (1 / k') = 1 := by field_simp
  have hcRoot :
      Real.rpow (Real.rpow c k') (1 / k') = c := by
    calc
      Real.rpow (Real.rpow c k') (1 / k') =
          Real.rpow c (k' * (1 / k')) :=
        (Real.rpow_mul (le_of_lt hcpos) k' (1 / k')).symm
      _ = Real.rpow c 1 := by rw [hk'_inv]
      _ = c := by simp
  have hprod :
      Real.rpow (Real.rpow c k' * alpha) (1 / k') =
        Real.rpow (Real.rpow c k') (1 / k') *
          Real.rpow alpha (1 / k') :=
    Real.mul_rpow (Real.rpow_nonneg (le_of_lt hcpos) k')
      (le_of_lt halpha')
  unfold holderBound
  change Real.rpow alpha (1 / k) *
      Real.rpow (powerSum k' (extremalCandidate k A a)) (1 / k') = A
  rw [hpower, hprod, hcRoot]
  calc
    Real.rpow alpha (1 / k) * (c * Real.rpow alpha (1 / k')) =
        c * (Real.rpow alpha (1 / k) * Real.rpow alpha (1 / k')) := by ring
    _ = c * Real.rpow alpha (1 / k + 1 / k') := by
      exact congrArg (fun z : ℝ => c * z)
        (Real.rpow_add halpha' (1 / k) (1 / k')).symm
    _ = c * alpha := by rw [hconj]; simp
    _ = A := by
      dsimp [c]
      exact div_mul_cancel₀ A halpha'.ne'

theorem gap10 {m : ℕ} (k k' : ℝ)
    (a x : Fin (m + 1) → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hlast : x (Fin.last m) = 0) :
    holderBound k k' a x ≥
      holderBound k k' (truncateLast a) (truncateLast x) := by
  have hkexp : 0 ≤ 1 / k := by positivity
  have hksum :
      powerSum k (truncateLast a) ≤ powerSum k a := by
    unfold powerSum truncateLast
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right
      (Real.rpow_nonneg (ha (Fin.last m)) k)
  have hkpow :
      Real.rpow (powerSum k (truncateLast a)) (1 / k) ≤
        Real.rpow (powerSum k a) (1 / k) :=
    Real.rpow_le_rpow
      (powerSum_nonneg k (truncateLast a) (fun i => ha i.castSucc))
      hksum hkexp
  have hxsum : powerSum k' x = powerSum k' (truncateLast x) := by
    unfold powerSum truncateLast
    rw [Fin.sum_univ_castSucc, hlast]
    simp [Real.zero_rpow (by linarith : k' ≠ 0)]
  unfold holderBound
  rw [hxsum]
  exact mul_le_mul_of_nonneg_right hkpow
    (Real.rpow_nonneg
      (powerSum_nonneg k' (truncateLast x) (fun i => hx i.castSucc))
      (1 / k'))

theorem gap11 {m : ℕ} (k k' : ℝ)
    (a x : Fin (m + 1) → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    holderBound k k' (truncateLast a) (truncateLast x) ≥
      dotProduct (truncateLast a) (truncateLast x) := by
  exact gap4 k k' (truncateLast a) (truncateLast x) hk hk' hconj
    (fun i => ha i.castSucc) (fun i => hx i.castSucc)

theorem gap12 {m : ℕ} (A : ℝ) (a x : Fin (m + 1) → ℝ)
    (hA : dotProduct a x = A) (hlast : x (Fin.last m) = 0) :
    dotProduct (truncateLast a) (truncateLast x) = A := by
  unfold dotProduct truncateLast
  unfold dotProduct at hA
  rw [Fin.sum_univ_castSucc] at hA
  simpa [hlast] using hA

theorem gap13 {m : ℕ} (k k' A : ℝ)
    (a x : Fin (m + 1) → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hA : dotProduct a x = A) (hlast : x (Fin.last m) = 0) :
    holderBound k k' a x ≥ A := by
  calc
    A = dotProduct (truncateLast a) (truncateLast x) :=
      (gap12 A a x hA hlast).symm
    _ ≤ holderBound k k' (truncateLast a) (truncateLast x) :=
      gap11 k k' a x hk hk' hconj ha hx
    _ ≤ holderBound k k' a x :=
      gap10 k k' a x hk hk' ha hx hlast

theorem gap14 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hA : dotProduct a x = A) :
    holderBound k k' a x ≥ A := by
  rw [← hA]
  exact gap4 k k' a x hk hk' hconj ha hx

theorem gap15 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hA : dotProduct a x = A) :
    holderBound k k' a x ≥ A := by
  exact gap14 k k' A a x hk hk' hconj ha hx hA

theorem gap16 {n : ℕ} (k k' : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    ∀ A > 0, dotProduct a x = A →
      holderBound k k' a x ≥ A := by
  intro A hApos hA
  exact gap15 k k' A a x hk hk' hconj ha hx hA

theorem gap17 {n : ℕ} (k k' : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hzero : dotProduct a x = 0) :
    dotProduct a x ≤ holderBound k k' a x := by
  rw [hzero]
  unfold holderBound
  exact mul_nonneg
    (Real.rpow_nonneg (powerSum_nonneg k a ha) (1 / k))
    (Real.rpow_nonneg (powerSum_nonneg k' x hx) (1 / k'))

theorem gap18 {n : ℕ} (A : ℝ) (a x : Fin n → ℝ)
    (hA : A = dotProduct a x) (hpos : dotProduct a x > 0) :
    A > 0 := by
  rw [hA]
  exact hpos

theorem gap19 {n : ℕ} (k k' A : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hA : A = dotProduct a x) (hpos : dotProduct a x > 0) :
    holderBound k k' a x ≥ A := by
  exact gap15 k k' A a x hk hk' hconj ha hx hA.symm

theorem gap20 {n : ℕ} (a x : Fin n → ℝ)
    (hpos : dotProduct a x > 0) :
    ∃ A > 0, A = dotProduct a x := by
  exact ⟨dotProduct a x, hpos, rfl⟩

theorem gap21 {n : ℕ} (k k' : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (hpos : dotProduct a x > 0) :
    holderBound k k' a x ≥ dotProduct a x := by
  exact gap19 k k' (dotProduct a x) a x hk hk' hconj ha hx rfl hpos

theorem gap22 {n : ℕ} (k k' : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    dotProduct a x ≤ holderBound k k' a x := by
  exact gap4 k k' a x hk hk' hconj ha hx

theorem gap23 {n : ℕ} (k k' : ℝ) (a x : Fin n → ℝ)
    (hk : k > 1) (hk' : k' > 1)
    (hconj : 1 / k + 1 / k' = 1)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    dotProduct a x ≤ holderBound k k' a x := by
  exact gap22 k k' a x hk hk' hconj ha hx

end

end ProofGap.Exercise3673
