import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

noncomputable section

namespace ProofGap.Exercise116

def x (n : ℕ) : ℝ :=
  if Even n then
    1 - 1 / (2 : ℝ) ^ (n / 2)
  else
    1 / (2 : ℝ) ^ ((n + 1) / 2)

private theorem half_pow_tendsto :
    Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem div_two_tendsto :
    Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2 * b)] with n hn
  omega

private theorem error_tendsto :
    Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ (n / 2)) atTop (𝓝 0) := by
  simpa [one_div_pow] using half_pow_tendsto.comp div_two_tendsto

private theorem x_even (k : ℕ) :
    x (2 * k) = 1 - (1 / 2 : ℝ) ^ k := by
  simp [x]

private theorem x_odd (k : ℕ) :
    x (2 * k + 1) = (1 / 2 : ℝ) ^ (k + 1) := by
  rw [x, if_neg (show ¬Even (2 * k + 1) from
    Nat.not_even_iff_odd.mpr ⟨k, by ring⟩)]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  simp

private theorem product_bounds (n : ℕ) :
    0 ≤ x n * (1 - x n) ∧
      x n * (1 - x n) ≤ 1 / (2 : ℝ) ^ (n / 2) := by
  rw [x]
  split_ifs with hn
  · let e : ℝ := 1 / (2 : ℝ) ^ (n / 2)
    have he0 : 0 ≤ e := by positivity
    have he1 : e ≤ 1 := by
      dsimp [e]
      simpa only [one_div_pow] using
        (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := n / 2)
          (by norm_num) (by norm_num))
    change 0 ≤ (1 - e) * (1 - (1 - e)) ∧
      (1 - e) * (1 - (1 - e)) ≤ e
    constructor <;> nlinarith
  · let y : ℝ := 1 / (2 : ℝ) ^ ((n + 1) / 2)
    let e : ℝ := 1 / (2 : ℝ) ^ (n / 2)
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by
      dsimp [y]
      simpa only [one_div_pow] using
        (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := (n + 1) / 2)
          (by norm_num) (by norm_num))
    have hye : y ≤ e := by
      dsimp [y, e]
      have hpow :
          (1 / 2 : ℝ) ^ ((n + 1) / 2) ≤
            (1 / 2 : ℝ) ^ (n / 2) := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        exact Nat.div_le_div_right (Nat.le_succ n)
      simpa only [one_div_pow] using hpow
    change 0 ≤ y * (1 - y) ∧ y * (1 - y) ≤ e
    constructor <;> nlinarith [sq_nonneg y]

private theorem product_tendsto :
    Tendsto (fun n : ℕ => x n * (1 - x n)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => (product_bounds n).1
  · exact Filter.Eventually.of_forall fun n => (product_bounds n).2
  · exact error_tendsto

private theorem zero_mem_cluster : 0 ∈ ProofGap.ClusterSet x := by
  let p : ℕ → ℕ := fun k => 2 * k + 1
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  have h := half_pow_tendsto.comp
    (show Tendsto (fun k : ℕ => k + 1) atTop atTop from
      (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop)
  apply h.congr'
  filter_upwards with k
  simpa [p, Function.comp_apply] using (x_odd k).symm

private theorem one_mem_cluster : 1 ∈ ProofGap.ClusterSet x := by
  let p : ℕ → ℕ := fun k => 2 * k
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  have h :
      Tendsto (fun k : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ k)
        atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub half_pow_tendsto
  norm_num at h
  apply h.congr'
  filter_upwards with k
  simpa [p, Function.comp_apply] using (x_even k).symm

/-- Exercise 116, gap 1; the pair definition is totalized by parity. -/
theorem gap1 :
    ProofGap.ClusterSet x = ({0, 1} : Set ℝ) := by
  ext a
  constructor
  · intro ha
    rcases ha with ⟨p, hp, hlim⟩
    have hpoly_a :
        Tendsto
          (fun k : ℕ => (x ∘ p) k * (1 - (x ∘ p) k))
          atTop (𝓝 (a * (1 - a))) :=
      hlim.mul (tendsto_const_nhds.sub hlim)
    have hpoly_zero :
        Tendsto
          (fun k : ℕ => (x ∘ p) k * (1 - (x ∘ p) k))
          atTop (𝓝 0) := by
      simpa [Function.comp_apply] using
        product_tendsto.comp hp.tendsto_atTop
    have hzero : a * (1 - a) = 0 :=
      tendsto_nhds_unique hpoly_a hpoly_zero
    rcases mul_eq_zero.mp hzero with ha0 | ha1
    · simp [ha0]
    · have : a = 1 := by linarith
      simp [this]
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact zero_mem_cluster
    · exact one_mem_cluster

end ProofGap.Exercise116
