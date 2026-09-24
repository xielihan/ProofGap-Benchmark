import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2760

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x / n) ^ n

def logRemainder (n : ℕ) (x : ℝ) : ℝ :=
  n * Real.log (1 + x / n) - (x - x ^ 2 / (2 * n))

def approximation (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x * (1 - x ^ 2 / (2 * n))

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem div_nat_lt
    (K ε : ℝ) (_hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → K / (n : ℝ) < ε := by
  have hlim : Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_div_pow K 1 one_ne_zero
  obtain ⟨N, hN⟩ :=
    ((tendsto_order.1 hlim).2 ε hε).exists_forall_of_atTop
  exact ⟨N, fun n hn => hN n (Nat.le_of_lt hn)⟩

private theorem log_one_add_taylor (t : ℝ) (ht : 0 < 1 + t) :
    ∃ θ : ℝ, θ ∈ Set.Ioo 0 1 ∧
      Real.log (1 + t) =
        t - t ^ 2 / 2 + (1 / 3 : ℝ) * t ^ 3 / (1 + θ * t) ^ 3 := by
  let f : ℝ → ℝ := fun u => Real.log (1 + t * u)
  let g₁ : ℝ → ℝ := fun u => t / (1 + t * u)
  let g₂ : ℝ → ℝ := fun u => -t ^ 2 / (1 + t * u) ^ 2
  let g₃ : ℝ → ℝ := fun u => 2 * t ^ 3 / (1 + t * u) ^ 3
  have hpos (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 + t * u := by
    rcases le_total 0 t with ht0 | ht0
    · have htu : 0 ≤ t * u := mul_nonneg ht0 hu.1
      linarith
    · have hmul := mul_le_mul_of_nonpos_left hu.2 ht0
      nlinarith
  have hlin (u : ℝ) : HasDerivAt (fun v : ℝ => 1 + t * v) t u := by
    convert (hasDerivAt_const u 1).add ((hasDerivAt_id u).const_mul t) using 1 <;> simp
  have hf₁ (u : ℝ) (hu : 1 + t * u ≠ 0) : HasDerivAt f (g₁ u) u := by
    simpa [f, g₁] using (hlin u).log hu
  have hg₁ (u : ℝ) (hu : 1 + t * u ≠ 0) : HasDerivAt g₁ (g₂ u) u := by
    have h := (hasDerivAt_const u t).div (hlin u) hu
    convert h using 1 <;> simp only [g₁, g₂] <;> field_simp <;> ring
  have hg₂ (u : ℝ) (hu : 1 + t * u ≠ 0) : HasDerivAt g₂ (g₃ u) u := by
    have h := (hasDerivAt_const u (-t ^ 2)).div ((hlin u).pow 2) (pow_ne_zero 2 hu)
    simp only [Pi.pow_apply] at h
    convert h using 1 <;> simp only [g₂, g₃]
    field_simp [hu]
    ring
  have hne_nhds (u : ℝ) (hu : 1 + t * u ≠ 0) :
      ∀ᶠ v in 𝓝 u, 1 + t * v ≠ 0 :=
    (by fun_prop : ContinuousAt (fun v : ℝ => 1 + t * v) u).eventually_ne hu
  have hi₁ (u : ℝ) (hu : 1 + t * u ≠ 0) : iteratedDeriv 1 f u = g₁ u := by
    rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]
    exact (hf₁ u hu).deriv
  have hi₂ (u : ℝ) (hu : 1 + t * u ≠ 0) : iteratedDeriv 2 f u = g₂ u := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ]
    have heq : iteratedDeriv 1 f =ᶠ[𝓝 u] g₁ :=
      (hne_nhds u hu).mono fun v hv => hi₁ v hv
    rw [heq.deriv_eq]
    exact (hg₁ u hu).deriv
  have hi₃ (u : ℝ) (hu : 1 + t * u ≠ 0) : iteratedDeriv 3 f u = g₃ u := by
    rw [show 3 = 2 + 1 by omega, iteratedDeriv_succ]
    have heq : iteratedDeriv 2 f =ᶠ[𝓝 u] g₂ :=
      (hne_nhds u hu).mono fun v hv => hi₂ v hv
    rw [heq.deriv_eq]
    exact (hg₂ u hu).deriv
  have hf : ContDiffOn ℝ 3 f (Set.Icc (0 : ℝ) 1) := by
    apply ContDiffOn.log (by fun_prop)
    exact fun u hu => (hpos u hu).ne'
  obtain ⟨θ, hθ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x := (1 : ℝ)) (x₀ := 0)
      (n := 2) zero_lt_one hf
  have hf0 : ContDiffAt ℝ 3 f 0 := by
    apply ContDiffAt.log (by fun_prop)
    simp
  have hu0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hw₁ : iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0 = t := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf0.of_le (by norm_num)) hu0,
      hi₁ 0 (by simp)]
    simp [g₁]
  have hw₂ : iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 = -t ^ 2 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf0.of_le (by norm_num)) hu0,
      hi₂ 0 (by simp)]
    simp [g₂]
  have hw₀ : iteratedDerivWithin 0 f (Set.Icc (0 : ℝ) 1) 0 = 0 := by
    simp [f]
  have hpoly : taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1 = t - t ^ 2 / 2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hw₀, hw₁, hw₂]
    ring
  have hθne : 1 + t * θ ≠ 0 := (hpos θ ⟨hθ.1.le, hθ.2.le⟩).ne'
  rw [hpoly, hi₃ θ hθne] at hrem
  simp only [f, g₃] at hrem
  norm_num at hrem
  refine ⟨θ, hθ, ?_⟩
  calc
    Real.log (1 + t) =
        (t - t ^ 2 / 2) + 2 * t ^ 3 / (1 + t * θ) ^ 3 / 6 := by
      linarith
    _ = t - t ^ 2 / 2 + (1 / 3 : ℝ) * t ^ 3 / (1 + θ * t) ^ 3 := by
      ring

theorem gap1 :
    ∀ (a b x : ℝ), a < x → x < b →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.exp x)) := by
  intro a b x _ _
  simpa [term] using Real.tendsto_one_add_div_pow_exp x

theorem gap2 :
    ∀ (a b x : ℝ), a < x → x < b →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.exp x)) := by
  exact gap1

theorem gap3 :
    ∀ (a b x : ℝ), a < x → x < b → Real.exp x = Real.exp x := by
  simp

theorem gap4 :
    ∀ (a b x : ℝ), a < x → x < b →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.exp x)) := by
  exact gap1

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < 1 + x / n →
      Real.log (term n x) = n * Real.log (1 + x / n) := by
  intro n x _ _
  exact Real.log_pow (1 + x / n) n

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < 1 + x / n →
      ∃ θ : ℝ, θ ∈ Set.Ioo 0 1 ∧
        n * Real.log (1 + x / n) =
          n * (x / n - x ^ 2 / (2 * (n : ℝ) ^ 2) +
            (1 / 3 : ℝ) * (x ^ 3 / (n : ℝ) ^ 3) /
              (1 + θ * x / n) ^ 3) := by
  intro n x hn hx
  rcases log_one_add_taylor (x / n) hx with ⟨θ, hθ, hlog⟩
  refine ⟨θ, hθ, ?_⟩
  rw [hlog]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]

theorem gap7 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < 1 + x / n →
      ∃ θ : ℝ, θ ∈ Set.Ioo 0 1 ∧
        Real.log (term n x) =
          n * (x / n - x ^ 2 / (2 * (n : ℝ) ^ 2) +
            (1 / 3 : ℝ) * (x ^ 3 / (n : ℝ) ^ 3) /
              (1 + θ * x / n) ^ 3) := by
  intro n x hn hx
  rcases gap6 n x hn hx with ⟨θ, hθ, hTaylor⟩
  exact ⟨θ, hθ, (gap5 n x hn hx).trans hTaylor⟩

theorem gap8 : ∃ θ : ℝ, 0 < θ := by
  exact ⟨1, zero_lt_one⟩

theorem gap9 : ∃ θ : ℝ, θ < 1 := by
  exact ⟨0, zero_lt_one⟩

theorem gap10 :
    ∀ (c θ x : ℝ) (n : ℕ), 0 ≤ c → |x| ≤ c → |θ| ≤ 1 → 0 < n →
      |θ * x / n| ≤ c / n := by
  intro c θ x n hc hx hθ hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_mul, abs_of_nonneg hn'.le]
  apply (div_le_div_iff_of_pos_right hn').2
  calc
    |θ| * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hθ (abs_nonneg x)
    _ ≤ 1 * c := mul_le_mul_of_nonneg_left hx zero_le_one
    _ = c := one_mul c

theorem gap11 :
    ∀ (c x : ℝ), 0 ≤ c → |x| ≤ c → |x ^ 3| ≤ c ^ 3 := by
  intro c x _ hx
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx 3

theorem gap12 :
    ∀ c : ℝ, 0 ≤ c →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x : ℝ, |x| ≤ c → |logRemainder n x| ≤ K / (n : ℝ) ^ 2 := by
  intro c hc
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max (2 * c) 0)
  refine ⟨8 * c ^ 3, by positivity, N, fun n hn x hx => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n :=
    lt_of_le_of_lt (le_max_right (2 * c) 0) (hN.trans_le hNn)
  have hn : 0 < n := by exact_mod_cast hn0
  have h2c : 2 * c < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left (2 * c) 0) (hN.trans_le hNn)
  have hxlower : -c ≤ x := (abs_le.mp hx).1
  have hbase : 0 < 1 + x / (n : ℝ) := by
    have hdiv : -1 < x / (n : ℝ) := by
      rw [lt_div_iff₀ hn0]
      linarith
    linarith
  rcases gap6 n x hn hbase with ⟨θ, hθ, hlog⟩
  have hθabs : |θ| ≤ 1 := by
    rw [abs_of_pos hθ.1]
    exact hθ.2.le
  have hybound : |θ * x / (n : ℝ)| < 1 / 2 := by
    refine (gap10 c θ x n hc hx hθabs hn).trans_lt ?_
    rw [div_lt_iff₀ hn0]
    linarith
  have hden : 1 / 2 < 1 + θ * x / (n : ℝ) := by
    have hy := neg_abs_le (θ * x / (n : ℝ))
    linarith
  have hden0 : 0 < 1 + θ * x / (n : ℝ) := by linarith
  have hden3 : (1 / 8 : ℝ) ≤ (1 + θ * x / (n : ℝ)) ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hden.le 3
    norm_num at hp ⊢
    exact hp
  have hrem : logRemainder n x =
      (1 / 3 : ℝ) * x ^ 3 / (n : ℝ) ^ 2 /
        (1 + θ * x / (n : ℝ)) ^ 3 := by
    rw [logRemainder, hlog]
    field_simp [hn0.ne']
    ring
  rw [hrem]
  simp only [abs_div, abs_mul, abs_pow, abs_of_pos hn0, abs_of_pos hden0]
  norm_num
  calc
    (1 / 3 : ℝ) * |x| ^ 3 / (n : ℝ) ^ 2 /
          (1 + θ * x / (n : ℝ)) ^ 3
        ≤ (1 / 3 : ℝ) * c ^ 3 / (n : ℝ) ^ 2 / (1 / 8 : ℝ) := by
          norm_num
          gcongr
    _ ≤ 8 * c ^ 3 / (n : ℝ) ^ 2 := by
      have hc3 : 0 ≤ c ^ 3 := pow_nonneg hc 3
      have hn2 : 0 < (n : ℝ) ^ 2 := pow_pos hn0 2
      field_simp
      nlinarith

theorem gap13 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < 1 + x / n →
      term n x = Real.exp (n * Real.log (1 + x / n)) := by
  intro n x _ hx
  calc
    term n x = Real.exp (Real.log (1 + x / n)) ^ n := by
      rw [term, Real.exp_log hx]
    _ = Real.exp (n * Real.log (1 + x / n)) :=
      (Real.exp_nat_mul _ _).symm

theorem gap14 :
    ∀ c : ℝ, 0 ≤ c →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x : ℝ, |x| ≤ c →
          |term n x - approximation n x| ≤ K / (n : ℝ) ^ 2 := by
  intro c hc
  rcases gap12 c hc with ⟨L, hL, N₀, hLbound⟩
  let A : ℝ := c ^ 2 / 2 + L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (max (max c A) 0)
  let K : ℝ := Real.exp c * (A ^ 2 + L)
  refine ⟨K, by dsimp [K]; positivity, max N₀ M, fun n hn x hx => ?_⟩
  have hN₀n : N₀ ≤ n := (le_max_left N₀ M).trans hn
  have hMn : (M : ℝ) ≤ n := by
    exact_mod_cast (le_max_right N₀ M).trans hn
  have htop : max (max c A) 0 < (n : ℝ) := hM.trans_le hMn
  have hc_lt_n : c < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_left c A).trans (le_max_left (max c A) 0)) htop
  have hA_lt_n : A < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_right c A).trans (le_max_left (max c A) 0)) htop
  have hn0 : (0 : ℝ) < n := (le_max_right (max c A) 0).trans_lt htop
  have hn : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxlower : -c ≤ x := (abs_le.mp hx).1
  have hxupper : x ≤ c := (abs_le.mp hx).2
  have hbase : 0 < 1 + x / (n : ℝ) := by
    have hdiv : -1 < x / (n : ℝ) := by
      rw [lt_div_iff₀ hn0]
      linarith
    linarith
  let q : ℝ := x ^ 2 / (2 * (n : ℝ))
  let r : ℝ := logRemainder n x
  let z : ℝ := -q + r
  have hr : |r| ≤ L / (n : ℝ) ^ 2 := by
    exact hLbound n hN₀n x hx
  have hx2 : x ^ 2 ≤ c ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hc] using hx
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqn : q ≤ (c ^ 2 / 2) / (n : ℝ) := by
    dsimp [q]
    calc
      x ^ 2 / (2 * (n : ℝ)) ≤ c ^ 2 / (2 * (n : ℝ)) := by gcongr
      _ = (c ^ 2 / 2) / (n : ℝ) := by ring
  have hn_le_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrn : |r| ≤ L / (n : ℝ) := by
    refine hr.trans ?_
    calc
      L / (n : ℝ) ^ 2 = L * (1 / (n : ℝ) ^ 2) := by ring
      _ ≤ L * (1 / (n : ℝ)) := by
        gcongr
      _ = L / (n : ℝ) := by ring
  have hzabs : |z| ≤ A / (n : ℝ) := by
    calc
      |z| = |-q + r| := rfl
      _ ≤ |-q| + |r| := abs_add_le _ _
      _ = q + |r| := by rw [abs_neg, abs_of_nonneg hq]
      _ ≤ (c ^ 2 / 2) / (n : ℝ) + L / (n : ℝ) := add_le_add hqn hrn
      _ = A / (n : ℝ) := by dsimp [A]; ring
  have hAn : A / (n : ℝ) < 1 := (div_lt_one hn0).2 hA_lt_n
  have hz1 : |z| ≤ 1 := hzabs.trans (le_of_lt hAn)
  have hz2 : z ^ 2 ≤ (A / (n : ℝ)) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (div_nonneg hA hn0.le)] using hzabs
  have hexp := Real.abs_exp_sub_one_sub_id_le hz1
  have hinner : |Real.exp z - (1 - q)| ≤ (A ^ 2 + L) / (n : ℝ) ^ 2 := by
    calc
      |Real.exp z - (1 - q)| = |(Real.exp z - 1 - z) + r| := by
        congr 1
        dsimp [z]
        ring
      _ ≤ |Real.exp z - 1 - z| + |r| := abs_add_le _ _
      _ ≤ z ^ 2 + |r| := add_le_add hexp le_rfl
      _ ≤ (A / (n : ℝ)) ^ 2 + L / (n : ℝ) ^ 2 := add_le_add hz2 hr
      _ = (A ^ 2 + L) / (n : ℝ) ^ 2 := by ring
  have hlogid : (n : ℝ) * Real.log (1 + x / (n : ℝ)) = x + z := by
    dsimp [z, q, r, logRemainder]
    ring
  have hterm : term n x = Real.exp x * Real.exp z := by
    calc
      term n x = Real.exp ((n : ℝ) * Real.log (1 + x / (n : ℝ))) :=
        gap13 n x hn hbase
      _ = Real.exp (x + z) := by rw [hlogid]
      _ = Real.exp x * Real.exp z := Real.exp_add x z
  rw [hterm, approximation]
  change |Real.exp x * Real.exp z - Real.exp x * (1 - q)| ≤ K / (n : ℝ) ^ 2
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos x)]
  calc
    Real.exp x * |Real.exp z - (1 - q)|
        ≤ Real.exp x * ((A ^ 2 + L) / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (Real.exp_pos x).le
    _ ≤ Real.exp c * ((A ^ 2 + L) / (n : ℝ) ^ 2) := by
      gcongr
    _ = K / (n : ℝ) ^ 2 := by dsimp [K]; ring

theorem gap15 :
    ∀ (n : ℕ) (x : ℝ), approximation n x =
      Real.exp x * (1 - x ^ 2 / (2 * n)) := by
  intro n x
  rfl

theorem gap16 :
    ∀ c : ℝ, 0 ≤ c →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x : ℝ, |x| ≤ c →
          |term n x - Real.exp x| ≤ K / (n : ℝ) := by
  intro c hc
  rcases gap14 c hc with ⟨L, hL, N₀, hbound⟩
  let B : ℝ := Real.exp c * (c ^ 2 / 2)
  let K : ℝ := L + B
  refine ⟨K, by dsimp [K, B]; positivity, max N₀ 1, fun n hn x hx => ?_⟩
  have hN₀n : N₀ ≤ n := (le_max_left N₀ 1).trans hn
  have hn_nat : 1 ≤ n := (le_max_right N₀ 1).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn_nat)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_nat
  have hxupper : x ≤ c := (abs_le.mp hx).2
  have hx2 : x ^ 2 ≤ c ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hc] using hx
  have hfirst : |term n x - approximation n x| ≤ L / (n : ℝ) := by
    refine (hbound n hN₀n x hx).trans ?_
    calc
      L / (n : ℝ) ^ 2 = L * (1 / (n : ℝ) ^ 2) := by ring
      _ ≤ L * (1 / (n : ℝ)) := by
        gcongr
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
      _ = L / (n : ℝ) := by ring
  have hq : 0 ≤ x ^ 2 / (2 * (n : ℝ)) := by positivity
  have hsecond : |approximation n x - Real.exp x| ≤ B / (n : ℝ) := by
    rw [approximation]
    calc
      |Real.exp x * (1 - x ^ 2 / (2 * (n : ℝ))) - Real.exp x| =
          Real.exp x * (x ^ 2 / (2 * (n : ℝ))) := by
            rw [show Real.exp x * (1 - x ^ 2 / (2 * (n : ℝ))) - Real.exp x =
              Real.exp x * (-(x ^ 2 / (2 * (n : ℝ)))) by ring,
              abs_mul, abs_of_pos (Real.exp_pos x), abs_neg, abs_of_nonneg hq]
      _ ≤ Real.exp c * (c ^ 2 / (2 * (n : ℝ))) := by
        gcongr
      _ = B / (n : ℝ) := by dsimp [B]; ring
  calc
    |term n x - Real.exp x| =
        |(term n x - approximation n x) + (approximation n x - Real.exp x)| := by
          congr 1
          ring
    _ ≤ |term n x - approximation n x| +
        |approximation n x - Real.exp x| := abs_add_le _ _
    _ ≤ L / (n : ℝ) + B / (n : ℝ) := add_le_add hfirst hsecond
    _ = K / (n : ℝ) := by dsimp [K]; ring

theorem gap17 :
    ∀ c : ℝ, 0 ≤ c →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x : ℝ, |x| ≤ c →
          |term n x - Real.exp x| ≤ K / (n : ℝ) := by
  exact gap16

theorem gap18 :
    ∀ c : ℝ, 0 ≤ c →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ x : ℝ, |x| ≤ c →
          |term n x - Real.exp x| ≤ K / (n : ℝ) := by
  exact gap16

theorem gap19 :
    ∀ c ε : ℝ, 0 ≤ c → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x : ℝ, |x| ≤ c → |term n x - Real.exp x| < ε := by
  intro c ε hc hε
  rcases gap16 c hc with ⟨K, hK, N₀, hbound⟩
  rcases div_nat_lt K ε hK hε with ⟨N₁, hsmall⟩
  refine ⟨max N₀ N₁, fun n hn x hx => ?_⟩
  exact (hbound n ((le_max_left _ _).trans (Nat.le_of_lt hn)) x hx).trans_lt
    (hsmall n ((le_max_right _ _).trans_lt hn))

theorem gap20 :
    ∀ (K ε : ℝ), 0 ≤ K → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → K / (n : ℝ) < ε := by
  exact div_nat_lt

theorem gap21 :
    ∀ (a b ε : ℝ), a < b → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Ioo a b, |term n x - Real.exp x| < ε := by
  intro a b ε _ hε
  let c := max |a| |b|
  have hc : 0 ≤ c := (abs_nonneg a).trans (le_max_left _ _)
  rcases gap19 c ε hc hε with ⟨N, hN⟩
  refine ⟨N, fun n hn x hx => hN n hn x ?_⟩
  rw [abs_le]
  constructor
  · have ha : -|a| ≤ a := neg_abs_le a
    have hca : |a| ≤ c := le_max_left _ _
    linarith [hx.1]
  · have hb : b ≤ |b| := le_abs_self b
    have hcb : |b| ≤ c := le_max_right _ _
    linarith [hx.2]

theorem gap22 :
    ∀ (a b ε : ℝ), a < b → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Ioo a b, |term n x - Real.exp x| < ε := by
  exact gap21

theorem gap23 :
    ∀ a b : ℝ, a < b →
      UniformlyConvergesOn term Real.exp (Set.Ioo a b) := by
  intro a b hab
  intro ε hε
  exact gap22 a b ε hab hε

theorem gap24 :
    ∀ (n : ℕ) (x : ℝ),
      |term n x - Real.exp x| = |(1 + x / n) ^ n - Real.exp x| := by
  intro n x
  rfl

theorem gap25 :
    ∀ n : ℕ,
      |term n n - Real.exp n| =
        2 ^ n * ((Real.exp 1 / 2) ^ n - 1) := by
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num [term]
  have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hterm : term n n = (2 : ℝ) ^ n := by
    norm_num [term, hncast]
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul 1 n
  have hpow : (2 : ℝ) ^ n ≤ Real.exp 1 ^ n :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le n
  rw [hterm, hexp, abs_of_nonpos (sub_nonpos.mpr hpow), neg_sub]
  rw [div_pow]
  field_simp

theorem gap26 :
    Tendsto (fun n : ℕ => |term n n - Real.exp n|) atTop atTop := by
  have hr : 1 < Real.exp 1 / 2 := by
    rw [one_lt_div (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_one_gt_two
  have hpow : Tendsto (fun n : ℕ => (Real.exp 1 / 2) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have hsub : Tendsto (fun n : ℕ => (Real.exp 1 / 2) ^ n - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hpow
  refine tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_) hsub
  change (Real.exp 1 / 2) ^ n - 1 ≤ |term n n - Real.exp n|
  rw [gap25 n]
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hrn : (1 : ℝ) ≤ (Real.exp 1 / 2) ^ n := one_le_pow₀ hr.le
  calc
    (Real.exp 1 / 2) ^ n - 1 = 1 * ((Real.exp 1 / 2) ^ n - 1) := by ring
    _ ≤ 2 ^ n * ((Real.exp 1 / 2) ^ n - 1) :=
      mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hrn)

theorem gap27 :
    ¬ UniformlyConvergesOn term Real.exp Set.univ := by
  intro h
  rcases h 1 zero_lt_one with ⟨N, hN⟩
  rcases ((gap26.eventually_gt_atTop 1).and (eventually_gt_atTop N)).exists with
    ⟨n, hlarge, hn⟩
  have hsmall := hN n hn (n : ℝ) (Set.mem_univ _)
  linarith

theorem gap28 :
    ∀ a b : ℝ, a < b →
      UniformlyConvergesOn term Real.exp (Set.Ioo a b) ∧
        ¬ UniformlyConvergesOn term Real.exp Set.univ := by
  intro a b hab
  exact ⟨gap23 a b hab, gap27⟩

end

end ProofGap.Exercise2760
