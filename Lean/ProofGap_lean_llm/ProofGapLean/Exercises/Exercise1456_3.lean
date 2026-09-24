import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1456_3

noncomputable section

def f (m n a x : ℝ) : ℝ :=
  Real.rpow x m * Real.rpow (a - x) n

def bound (m n a : ℝ) : ℝ :=
  (Real.rpow m m * Real.rpow n n / Real.rpow (m + n) (m + n)) *
    Real.rpow a (m + n)

private theorem weighted_max_aux (m n a x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hx₀ : 0 ≤ x) (hxa : x ≤ a) :
    f m n a x ≤ f m n a (m * a / (m + n)) := by
  have ha : 0 ≤ a := le_trans hx₀ hxa
  by_cases ha0 : a = 0
  · subst a
    have hx : x = 0 := le_antisymm hxa hx₀
    subst x
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let s : ℝ := m + n
  let α : ℝ := m / s
  let β : ℝ := n / s
  let u : ℝ := s * x / m
  let v : ℝ := s * (a - x) / n
  have hs : 0 < s := by
    dsimp [s]
    exact add_pos hm hn
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hm.le hs.le
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg hn.le hs.le
  have hab : α + β = 1 := by
    dsimp [α, β, s]
    field_simp [(add_pos hm hn).ne'] <;> ring
  have hu : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (mul_nonneg hs.le hx₀) hm.le
  have hv : 0 ≤ v := by
    dsimp [v]
    exact div_nonneg (mul_nonneg hs.le (sub_nonneg.mpr hxa)) hn.le
  have harith : α * u + β * v = a := by
    dsimp [α, β, u, v, s]
    field_simp [hm.ne', hn.ne', (add_pos hm hn).ne'] <;> ring
  have hgm0 :
      Real.rpow u α * Real.rpow v β ≤ α * u + β * v :=
    Real.geom_mean_le_arith_mean2_weighted hα hβ hu hv hab
  have hgm : Real.rpow u α * Real.rpow v β ≤ a := by
    calc
      Real.rpow u α * Real.rpow v β ≤ α * u + β * v := hgm0
      _ = a := harith
  have hpbase : 0 ≤ Real.rpow u α * Real.rpow v β :=
    mul_nonneg (Real.rpow_nonneg hu α) (Real.rpow_nonneg hv β)
  have hpow :
      Real.rpow (Real.rpow u α * Real.rpow v β) s ≤ Real.rpow a s :=
    Real.rpow_le_rpow hpbase hgm hs.le
  have hαs : α * s = m := by
    dsimp [α]
    field_simp [hs.ne']
  have hβs : β * s = n := by
    dsimp [β]
    field_simp [hs.ne']
  have hu_mul : (u ^ α) ^ s = u ^ (α * s) :=
    (Real.rpow_mul hu (y := α) (z := s)).symm
  have hv_mul : (v ^ β) ^ s = v ^ (β * s) :=
    (Real.rpow_mul hv (y := β) (z := s)).symm
  have hleft :
      Real.rpow (Real.rpow u α * Real.rpow v β) s =
        Real.rpow u m * Real.rpow v n := by
    calc
      Real.rpow (Real.rpow u α * Real.rpow v β) s =
          Real.rpow (Real.rpow u α) s *
            Real.rpow (Real.rpow v β) s :=
        Real.mul_rpow (Real.rpow_nonneg hu α)
          (Real.rpow_nonneg hv β) (z := s)
      _ = Real.rpow u (α * s) * Real.rpow v (β * s) := by
            change (u ^ α) ^ s * (v ^ β) ^ s =
              u ^ (α * s) * v ^ (β * s)
            rw [hu_mul, hv_mul]
      _ = Real.rpow u m * Real.rpow v n := by
            rw [hαs, hβs]
  have huv : Real.rpow u m * Real.rpow v n ≤ Real.rpow a s := by
    calc
      Real.rpow u m * Real.rpow v n =
          Real.rpow (Real.rpow u α * Real.rpow v β) s := hleft.symm
      _ ≤ Real.rpow a s := hpow
  have hxrepr : x = α * u := by
    dsimp [α, u, s]
    field_simp [hm.ne', (add_pos hm hn).ne'] <;> ring
  have hyrepr : a - x = β * v := by
    dsimp [β, v, s]
    field_simp [hn.ne', (add_pos hm hn).ne'] <;> ring
  have hxpow :
      Real.rpow x m = Real.rpow α m * Real.rpow u m := by
    rw [hxrepr]
    exact Real.mul_rpow hα hu (z := m)
  have hypow :
      Real.rpow (a - x) n = Real.rpow β n * Real.rpow v n := by
    rw [hyrepr]
    exact Real.mul_rpow hβ hv (z := n)
  have hfx :
      f m n a x =
        (Real.rpow α m * Real.rpow β n) *
          (Real.rpow u m * Real.rpow v n) := by
    unfold f
    rw [hxpow, hypow]
    ring
  have hcenterx : m * a / (m + n) = α * a := by
    dsimp [α, s]
    ring
  have hcentery : a - m * a / (m + n) = β * a := by
    dsimp [β, s]
    field_simp [(add_pos hm hn).ne'] <;> ring
  have hcpow :
      Real.rpow (m * a / (m + n)) m =
        Real.rpow α m * Real.rpow a m := by
    rw [hcenterx]
    exact Real.mul_rpow hα ha (z := m)
  have hcypow :
      Real.rpow (a - m * a / (m + n)) n =
        Real.rpow β n * Real.rpow a n := by
    rw [hcentery]
    exact Real.mul_rpow hβ ha (z := n)
  have ha_add : a ^ m * a ^ n = a ^ (m + n) :=
    (Real.rpow_add ha_pos (y := m) (z := n)).symm
  have hfcenter :
      f m n a (m * a / (m + n)) =
        (Real.rpow α m * Real.rpow β n) * Real.rpow a s := by
    unfold f
    rw [hcpow, hcypow]
    calc
      (Real.rpow α m * Real.rpow a m) *
          (Real.rpow β n * Real.rpow a n) =
          (Real.rpow α m * Real.rpow β n) *
            (Real.rpow a m * Real.rpow a n) := by ring
      _ = (Real.rpow α m * Real.rpow β n) *
            Real.rpow a (m + n) := by
              change (α ^ m * β ^ n) * (a ^ m * a ^ n) =
                (α ^ m * β ^ n) * a ^ (m + n)
              rw [ha_add]
      _ = (Real.rpow α m * Real.rpow β n) * Real.rpow a s := by
            rfl
  have hfactor : 0 ≤ Real.rpow α m * Real.rpow β n :=
    mul_nonneg (Real.rpow_nonneg hα m) (Real.rpow_nonneg hβ n)
  calc
    f m n a x =
        (Real.rpow α m * Real.rpow β n) *
          (Real.rpow u m * Real.rpow v n) := hfx
    _ ≤ (Real.rpow α m * Real.rpow β n) * Real.rpow a s :=
      mul_le_mul_of_nonneg_left huv hfactor
    _ = f m n a (m * a / (m + n)) := hfcenter.symm

theorem gap1 (m n a : ℝ) (hm : 0 < m) (hn : 0 < n) (ha : 0 ≤ a) :
    IsMaxOn (f m n a) (Set.Icc 0 a) (m * a / (m + n)) := by
  intro x hx
  exact weighted_max_aux m n a x hm hn hx.1 hx.2

theorem gap2 (m n a x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hx₀ : 0 ≤ x) (hxa : x ≤ a) :
    f m n a x ≤ f m n a (m * a / (m + n)) := by
  exact weighted_max_aux m n a x hm hn hx₀ hxa

theorem gap3 (m n a : ℝ) (hm : 0 < m) (hn : 0 < n) (ha : 0 ≤ a) :
    f m n a (m * a / (m + n)) = bound m n a := by
  have hs : 0 < m + n := add_pos hm hn
  by_cases ha0 : a = 0
  · subst a
    simp [f, bound, hm.ne', hn.ne', hs.ne']
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let s : ℝ := m + n
  let α : ℝ := m / s
  let β : ℝ := n / s
  have hs' : 0 < s := by
    dsimp [s]
    exact hs
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hm.le hs'.le
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg hn.le hs'.le
  have hcenterx : m * a / (m + n) = α * a := by
    dsimp [α, s]
    ring
  have hcentery : a - m * a / (m + n) = β * a := by
    dsimp [β, s]
    field_simp [hs.ne'] <;> ring
  have hcpow :
      Real.rpow (m * a / (m + n)) m =
        Real.rpow α m * Real.rpow a m := by
    rw [hcenterx]
    exact Real.mul_rpow hα ha (z := m)
  have hcypow :
      Real.rpow (a - m * a / (m + n)) n =
        Real.rpow β n * Real.rpow a n := by
    rw [hcentery]
    exact Real.mul_rpow hβ ha (z := n)
  have ha_add : a ^ m * a ^ n = a ^ (m + n) :=
    (Real.rpow_add ha_pos (y := m) (z := n)).symm
  have hfcenter :
      f m n a (m * a / (m + n)) =
        (Real.rpow α m * Real.rpow β n) * Real.rpow a s := by
    unfold f
    rw [hcpow, hcypow]
    calc
      (Real.rpow α m * Real.rpow a m) *
          (Real.rpow β n * Real.rpow a n) =
          (Real.rpow α m * Real.rpow β n) *
            (Real.rpow a m * Real.rpow a n) := by ring
      _ = (Real.rpow α m * Real.rpow β n) *
            Real.rpow a (m + n) := by
              change (α ^ m * β ^ n) * (a ^ m * a ^ n) =
                (α ^ m * β ^ n) * a ^ (m + n)
              rw [ha_add]
      _ = (Real.rpow α m * Real.rpow β n) * Real.rpow a s := by
            rfl
  have hsm : Real.rpow s m ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs' m)
  have hsn : Real.rpow s n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs' n)
  have hfactor :
      Real.rpow α m * Real.rpow β n =
        Real.rpow m m * Real.rpow n n / Real.rpow s s := by
    dsimp [α, β]
    rw [Real.div_rpow hm.le hs'.le (z := m),
      Real.div_rpow hn.le hs'.le (z := n)]
    rw [Real.rpow_add hs' (y := m) (z := n)]
    field_simp [hsm, hsn] <;> ring
  calc
    f m n a (m * a / (m + n)) =
        (Real.rpow α m * Real.rpow β n) * Real.rpow a s := hfcenter
    _ = (Real.rpow m m * Real.rpow n n / Real.rpow s s) *
          Real.rpow a s := by rw [hfactor]
    _ = bound m n a := by rfl

theorem gap4 (m n a x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hx₀ : 0 ≤ x) (hxa : x ≤ a) :
    f m n a x ≤ bound m n a := by
  calc
    f m n a x ≤ f m n a (m * a / (m + n)) :=
      gap2 m n a x hm hn hx₀ hxa
    _ = bound m n a :=
      gap3 m n a hm hn (le_trans hx₀ hxa)

theorem gap5 (m n a x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hx₀ : 0 ≤ x) (hxa : x ≤ a) :
    f m n a x ≤ bound m n a := by
  exact gap4 m n a x hm hn hx₀ hxa

end
end ProofGap.Exercise1456_3
