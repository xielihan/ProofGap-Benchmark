import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic

namespace ProofGap.Exercise608_2

noncomputable section

def ratio (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) / f x
def rootExpr (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.rpow (f x) (1 / x)
def shiftedProduct (f : ℝ → ℝ) (X₀ : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).prod (fun k => ratio f (X₀ + k - 1))
def LocallyBounded (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M

/-- Exercise 608_2, gap 1. -/
theorem gap1 (f : ℝ → ℝ) (A₁ c : ℝ) (hc : 0 < c)
    (hf : ∀ x, c ≤ f x)
    (hratio : Filter.Tendsto (ratio f) Filter.atTop (nhds A₁)) :
    0 ≤ A₁ := by
  by_contra hA
  have hAneg : A₁ < 0 := lt_of_not_ge hA
  have hev : ∀ᶠ x in Filter.atTop, ratio f x < 0 :=
    (tendsto_order.1 hratio).2 0 hAneg
  rcases hev.exists with ⟨x, hx⟩
  have hrpos : 0 < ratio f x := by
    simp only [ratio]
    exact div_pos (lt_of_lt_of_le hc (hf (x + 1)))
      (lt_of_lt_of_le hc (hf x))
  exact (not_lt_of_ge hrpos.le) hx

/-- Exercise 608_2, gap 2; remove shadowed tail variables. -/
theorem gap2 (f : ℝ → ℝ) (A₁ : ℝ)
    (hpos : ∀ x, 0 < f x)
    (hratio : Filter.Tendsto (ratio f) Filter.atTop (nhds A₁))
    (hA : A₁ = 0) :
    ∃ X₀, ∀ x ≥ X₀, 0 < ratio f x ∧ ratio f x < 1 / 2 := by
  have hratio0 : Filter.Tendsto (ratio f) Filter.atTop (nhds 0) := by
    simpa [hA] using hratio
  have hev : ∀ᶠ x in Filter.atTop, ratio f x < (1 / 2 : ℝ) :=
    (tendsto_order.1 hratio0).2 (1 / 2 : ℝ) (by norm_num)
  rcases Filter.eventually_atTop.1 hev with ⟨X₀, hX₀⟩
  refine ⟨X₀, fun x hx => ⟨?_, hX₀ x hx⟩⟩
  simp only [ratio]
  exact div_pos (hpos (x + 1)) (hpos x)

/-- Exercise 608_2, gap 3; use the fixed tail threshold. -/
theorem gap3 (f : ℝ → ℝ) (X₀ : ℝ) (n : ℕ)
    (hpos : ∀ x, 0 < f x) :
    0 < f (X₀ + n) / f X₀ := by
  exact div_pos (hpos (X₀ + n)) (hpos X₀)

/-- Exercise 608_2, gap 4; replace the product ellipsis by `shiftedProduct`. -/
theorem gap4 (f : ℝ → ℝ) (X₀ : ℝ) (n : ℕ)
    (hpos : ∀ x, 0 < f x) :
    f (X₀ + n) / f X₀ = shiftedProduct f X₀ n := by
  induction n with
  | zero =>
      simp [shiftedProduct, (hpos X₀).ne']
  | succ n ih =>
      have hIcc : Finset.Icc 1 (Nat.succ n) =
          insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hx : X₀ + (Nat.succ n : ℝ) - 1 = X₀ + (n : ℝ) := by
        rw [Nat.cast_succ]
        ring
      calc
        f (X₀ + (Nat.succ n : ℝ)) / f X₀ =
            (f (X₀ + (n : ℝ)) / f X₀) * ratio f (X₀ + (n : ℝ)) := by
          rw [Nat.cast_succ]
          rw [show X₀ + ((n : ℝ) + 1) = X₀ + (n : ℝ) + 1 by ring]
          simp only [ratio]
          field_simp [(hpos X₀).ne', (hpos (X₀ + (n : ℝ))).ne']
        _ = shiftedProduct f X₀ n * ratio f (X₀ + (n : ℝ)) := by
          rw [ih]
        _ = shiftedProduct f X₀ (Nat.succ n) := by
          unfold shiftedProduct
          rw [hIcc, Finset.prod_insert (by simp)]
          rw [hx]
          ring

/-- Exercise 608_2, gap 5; replace the product ellipsis by `shiftedProduct`. -/
theorem gap5 (f : ℝ → ℝ) (X₀ : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hhalf : ∀ k ∈ Finset.Icc 1 n, ratio f (X₀ + k - 1) < 1 / 2)
    (hpos : ∀ x, 0 < ratio f x) :
    shiftedProduct f X₀ n < (1 / 2 : ℝ) ^ n := by
  unfold shiftedProduct
  have hn1 : 1 ≤ n := by omega
  have hne : (Finset.Icc 1 n).Nonempty := by
    exact ⟨1, by simp [hn1]⟩
  calc
    (Finset.Icc 1 n).prod (fun k => ratio f (X₀ + k - 1)) <
        (Finset.Icc 1 n).prod (fun _ => (1 / 2 : ℝ)) :=
      Finset.prod_lt_prod_of_nonempty
        (fun k _ => hpos (X₀ + k - 1)) hhalf hne
    _ = (1 / 2 : ℝ) ^ n := by
      rw [Finset.prod_const]
      simp [hn1]

/-- Exercise 608_2, gap 6. -/
theorem gap6 (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := by
  positivity

/-- Exercise 608_2, gap 7; bind the tail threshold and geometric bound. -/
theorem gap7 (f : ℝ → ℝ) (X₀ : ℝ)
    (hbound : ∀ n, 0 < f (X₀ + n) ∧
      f (X₀ + n) ≤ f X₀ * (1 / 2 : ℝ) ^ n) :
    Filter.Tendsto (fun n : ℕ => f (X₀ + n)) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hupper : Filter.Tendsto
      (fun n : ℕ => f X₀ * (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n => (hbound (n : ℝ)).1.le)
    (fun n => by
      simpa [Real.rpow_natCast] using (hbound (n : ℝ)).2)

/-- Exercise 608_2, gap 8; make the contradiction with the positive lower bound explicit. -/
theorem gap8 (f : ℝ → ℝ) (A₁ c : ℝ) (hc : 0 < c)
    (hf : ∀ x, c ≤ f x)
    (hzero : A₁ = 0 → ∃ X₀,
      Filter.Tendsto (fun n : ℕ => f (X₀ + n)) Filter.atTop (nhds 0)) :
    A₁ = 0 → False := by
  intro hA
  obtain ⟨X₀, hlim⟩ := hzero hA
  have hev : ∀ᶠ n : ℕ in Filter.atTop, f (X₀ + n) < c :=
    (tendsto_order.1 hlim).2 c hc
  rcases hev.exists with ⟨n, hn⟩
  exact (not_lt_of_ge (hf (X₀ + n))) hn

/-- Exercise 608_2, gap 9. -/
theorem gap9 (A₁ : ℝ) (hnonneg : 0 ≤ A₁) (hnzero : A₁ = 0 → False) :
    0 < A₁ := by
  rcases hnonneg.eq_or_lt with h | h
  · exact (hnzero h.symm).elim
  · exact h

/-- Exercise 608_2, gap 10. -/
theorem gap10 (A₁ : ℝ) (hA : 0 < A₁) : 0 < A₁ := by
  exact hA

/-- Exercise 608_2, gap 11; formalize boundedness on each finite interval. -/
theorem gap11 (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) (hlocal : LocallyBounded f) :
    LocallyBounded (fun x => Real.log (f x)) := by
  intro a b hab
  obtain ⟨M, hM⟩ := hlocal a b hab
  refine ⟨max (-Real.log c) (Real.log M), ?_⟩
  intro x hax hxb
  have hfx : 0 < f x := lt_of_lt_of_le hc (hf x)
  have hfxM : f x ≤ M := by
    have hx := hM x hax hxb
    simpa [abs_of_pos hfx] using hx
  have hMpos : 0 < M := lt_of_lt_of_le hfx hfxM
  have hlo : Real.log c ≤ Real.log (f x) :=
    Real.strictMonoOn_log.monotoneOn hc hfx (hf x)
  have hhi : Real.log (f x) ≤ Real.log M :=
    Real.strictMonoOn_log.monotoneOn hfx hMpos hfxM
  apply (abs_le).2
  constructor
  · have hmax := le_max_left (-Real.log c) (Real.log M)
    linarith
  · exact le_trans hhi (le_max_right _ _)

/-- Exercise 608_2, gap 12; compare the pointwise-equal logarithmic differences. -/
theorem gap12 (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x) (L : ℝ) :
    Filter.Tendsto (fun x => Real.log (f (x + 1)) - Real.log (f x))
        Filter.atTop (nhds L) ↔
      Filter.Tendsto (fun x => Real.log (ratio f x))
        Filter.atTop (nhds L) := by
  have heq :
      (fun x => Real.log (f (x + 1)) - Real.log (f x)) =
        (fun x => Real.log (ratio f x)) := by
    funext x
    rw [ratio, Real.log_div (hpos (x + 1)).ne' (hpos x).ne']
  rw [heq]

/-- Exercise 608_2, gap 13. -/
theorem gap13 (f : ℝ → ℝ) (A₁ : ℝ) (hA : 0 < A₁)
    (hratio : Filter.Tendsto (ratio f) Filter.atTop (nhds A₁)) :
    Filter.Tendsto (fun x => Real.log (ratio f x))
      Filter.atTop (nhds (Real.log A₁)) := by
  exact (Real.continuousAt_log hA.ne').tendsto.comp hratio

/-- Exercise 608_2, gap 14. -/
theorem gap14 (f : ℝ → ℝ) (A₁ : ℝ) (hpos : ∀ x, 0 < f x)
    (hlog : Filter.Tendsto (fun x => Real.log (ratio f x))
      Filter.atTop (nhds (Real.log A₁))) :
    Filter.Tendsto (fun x => Real.log (f (x + 1)) - Real.log (f x))
      Filter.atTop (nhds (Real.log A₁)) := by
  exact (gap12 f hpos (Real.log A₁)).2 hlog

private theorem tendsto_div_atTop_of_unitDiff
    (g : ℝ → ℝ) (L : ℝ) (hlocal : LocallyBounded g)
    (hdiff : Filter.Tendsto (fun x => g (x + 1) - g x)
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun x => g x / x) Filter.atTop (nhds L) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨X, hX⟩ := (Metric.tendsto_atTop.mp hdiff) δ hδ
  let K : ℕ := ⌈max X 0⌉₊
  have hmaxK : max X 0 ≤ (K : ℝ) := by
    dsimp [K]
    exact Nat.le_ceil _
  have hXK : X ≤ (K : ℝ) :=
    (le_max_left X 0).trans hmaxK
  have htail : ∀ y : ℝ, (K : ℝ) ≤ y →
      |(g (y + 1) - g y) - L| < δ := by
    intro y hy
    have hyX : X ≤ y := hXK.trans hy
    have hy' := hX y hyX
    rw [Real.dist_eq] at hy'
    convert hy' using 1 <;> ring
  obtain ⟨M, hM⟩ :=
    hlocal ((K : ℝ) - 1) ((K : ℝ) + 2) (by linarith)
  have hM0 : 0 ≤ M := by
    have hMK := hM (K : ℝ) (by linarith) (by linarith)
    exact (abs_nonneg (g (K : ℝ))).trans hMK
  let C : ℝ := M + |L| * ((K : ℝ) + 1)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨max ((K : ℝ) + 1) (C / δ + 1), ?_⟩
  intro x hx
  have hxK : (K : ℝ) + 1 ≤ x :=
    (le_max_left ((K : ℝ) + 1) (C / δ + 1)).trans hx
  have hxC : C / δ + 1 ≤ x :=
    (le_max_right ((K : ℝ) + 1) (C / δ + 1)).trans hx
  have hxpos : 0 < x := by
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  let n : ℕ := ⌊x⌋₊
  let r : ℝ := x - n
  have hxnonneg : 0 ≤ x := hxpos.le
  have hnle : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hxnonneg
  have hxlt : x < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one x
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hKn : K ≤ n := by
    dsimp [n]
    exact (Nat.le_floor_iff hxnonneg).2 (by linarith)
  have hbase :
      |g (r + (K : ℝ)) - L * (r + (K : ℝ))| ≤ C := by
    have hry_lo : (K : ℝ) - 1 < r + (K : ℝ) := by linarith
    have hry_hi : r + (K : ℝ) < (K : ℝ) + 2 := by linarith
    have hry_nonneg : 0 ≤ r + (K : ℝ) := by positivity
    have hry_le : r + (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
    calc
      |g (r + (K : ℝ)) - L * (r + (K : ℝ))| ≤
          |g (r + (K : ℝ))| + |L * (r + (K : ℝ))| :=
        abs_sub _ _
      _ ≤ M + |L| * ((K : ℝ) + 1) := by
        apply add_le_add (hM _ hry_lo hry_hi)
        rw [abs_mul, abs_of_nonneg hry_nonneg]
        exact mul_le_mul_of_nonneg_left hry_le (abs_nonneg L)
      _ = C := rfl
  have hiter : ∀ m : ℕ, K ≤ m →
      |g (r + (m : ℝ)) - L * (r + (m : ℝ))| ≤
        C + ((m - K : ℕ) : ℝ) * δ := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        simpa using hbase
    | succ m hm ih =>
        have hKm : (K : ℝ) ≤ r + (m : ℝ) := by
          have hcast : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          exact hcast.trans (le_add_of_nonneg_left hr0)
        have hstep := htail (r + (m : ℝ)) hKm
        have hdecomp :
            g (r + ((m + 1 : ℕ) : ℝ)) -
                L * (r + ((m + 1 : ℕ) : ℝ)) =
              (g (r + (m : ℝ)) - L * (r + (m : ℝ))) +
                ((g ((r + (m : ℝ)) + 1) - g (r + (m : ℝ))) - L) := by
          push_cast
          ring
        rw [hdecomp]
        calc
          |(g (r + (m : ℝ)) - L * (r + (m : ℝ))) +
              ((g ((r + (m : ℝ)) + 1) - g (r + (m : ℝ))) - L)| ≤
              |g (r + (m : ℝ)) - L * (r + (m : ℝ))| +
                |(g ((r + (m : ℝ)) + 1) - g (r + (m : ℝ))) - L| :=
            abs_add_le _ _
          _ ≤ (C + ((m - K : ℕ) : ℝ) * δ) + δ :=
            add_le_add ih hstep.le
          _ = C + (((m + 1) - K : ℕ) : ℝ) * δ := by
            have hsub : (m + 1) - K = (m - K) + 1 := by omega
            rw [hsub]
            push_cast
            ring
  have hrn : r + (n : ℝ) = x := by
    dsimp [r]
    ring
  have hmain := hiter n hKn
  rw [hrn] at hmain
  have hsuble : (((n - K : ℕ) : ℝ)) ≤ x := by
    exact (Nat.cast_le.2 (Nat.sub_le n K)).trans hnle
  have herr_div :
      (((n - K : ℕ) : ℝ) * δ) / x ≤ δ := by
    rw [div_le_iff₀ hxpos]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hsuble hδ.le)
  have hCx : C / x < δ := by
    have hCδx : C / δ < x := by linarith
    have hC_lt : C < x * δ := (div_lt_iff₀ hδ).1 hCδx
    exact (div_lt_iff₀ hxpos).2 (by simpa [mul_comm] using hC_lt)
  rw [Real.dist_eq]
  have hrewrite : g x / x - L = (g x - L * x) / x := by
    field_simp [hxpos.ne']
  rw [hrewrite, abs_div, abs_of_pos hxpos]
  calc
    |g x - L * x| / x ≤
        (C + ((n - K : ℕ) : ℝ) * δ) / x :=
      div_le_div_of_nonneg_right hmain hxpos.le
    _ = C / x + (((n - K : ℕ) : ℝ) * δ) / x := by ring
    _ ≤ C / x + δ := add_le_add le_rfl herr_div
    _ < δ + δ := add_lt_add_of_lt_of_le hCx le_rfl
    _ = ε := by dsimp [δ]; ring

/-- Exercise 608_2, gap 15; apply the additive difference theorem to `log ∘ f`. -/
theorem gap15 (f : ℝ → ℝ) (A₁ : ℝ)
    (hlocal : LocallyBounded (fun x => Real.log (f x)))
    (hdiff : Filter.Tendsto
      (fun x => Real.log (f (x + 1)) - Real.log (f x))
      Filter.atTop (nhds (Real.log A₁))) :
    Filter.Tendsto (fun x => Real.log (f x) / x)
      Filter.atTop (nhds (Real.log A₁)) := by
  exact tendsto_div_atTop_of_unitDiff
    (fun x => Real.log (f x)) (Real.log A₁) hlocal hdiff

/-- Exercise 608_2, gap 16; state the positive-base identity pointwise. -/
theorem gap16 (f : ℝ → ℝ) (x : ℝ) (hfx : 0 < f x) :
    rootExpr f x = Real.rpow (Real.exp (Real.log (f x))) (1 / x) := by
  rw [rootExpr, Real.exp_log hfx]

/-- Exercise 608_2, gap 17; rewrite the real power as an exponential. -/
theorem gap17 (f : ℝ → ℝ) (x : ℝ) (hfx : 0 < f x) :
    Real.rpow (Real.exp (Real.log (f x))) (1 / x) =
      Real.exp (Real.log (f x) / x) := by
  change (Real.exp (Real.log (f x))) ^ (1 / x : ℝ) =
    Real.exp (Real.log (f x) / x)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- Exercise 608_2, gap 18. -/
theorem gap18 (f : ℝ → ℝ) (A₁ : ℝ)
    (hlog : Filter.Tendsto (fun x => Real.log (f x) / x)
      Filter.atTop (nhds (Real.log A₁))) :
    Filter.Tendsto (fun x => Real.exp (Real.log (f x) / x))
      Filter.atTop (nhds (Real.exp (Real.log A₁))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp hlog

/-- Exercise 608_2, gap 19. -/
theorem gap19 (A₁ : ℝ) (hA : 0 < A₁) :
    Real.exp (Real.log A₁) = A₁ := by
  exact Real.exp_log hA

/-- Exercise 608_2, gap 20. -/
theorem gap20 (f : ℝ → ℝ) (A₁ : ℝ) (hA : 0 < A₁)
    (hpos : ∀ x, 0 < f x)
    (hlog : Filter.Tendsto (fun x => Real.log (f x) / x)
      Filter.atTop (nhds (Real.log A₁))) :
    Filter.Tendsto (rootExpr f) Filter.atTop (nhds A₁) := by
  have heq : rootExpr f =
      (fun x => Real.exp (Real.log (f x) / x)) := by
    funext x
    calc
      rootExpr f x = Real.rpow (Real.exp (Real.log (f x))) (1 / x) :=
        gap16 f x (hpos x)
      _ = Real.exp (Real.log (f x) / x) := gap17 f x (hpos x)
  rw [heq]
  simpa [gap19 A₁ hA] using gap18 f A₁ hlog

/-- Exercise 608_2, gap 21; corrected ratio-to-root limit theorem. -/
theorem gap21 (f : ℝ → ℝ) (A₁ c : ℝ) (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) (hlocal : LocallyBounded f)
    (hratio : Filter.Tendsto (ratio f) Filter.atTop (nhds A₁)) :
    Filter.Tendsto (rootExpr f) Filter.atTop (nhds A₁) := by
  have hposF : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hc (hf x)
  have hnonneg : 0 ≤ A₁ := gap1 f A₁ c hc hf hratio
  have hzero : A₁ = 0 → ∃ X₀,
      Filter.Tendsto (fun n : ℕ => f (X₀ + n)) Filter.atTop (nhds 0) := by
    intro hA0
    obtain ⟨X₀, hX₀⟩ := gap2 f A₁ hposF hratio hA0
    have hboundNat : ∀ n : ℕ, 0 < f (X₀ + n) ∧
        f (X₀ + n) ≤ f X₀ * (1 / 2 : ℝ) ^ n := by
      intro n
      induction n with
      | zero =>
          constructor
          · simpa using hposF X₀
          · simp
      | succ n hn =>
          have hr : ratio f (X₀ + (n : ℝ)) < (1 / 2 : ℝ) :=
            (hX₀ (X₀ + (n : ℝ))
              (le_add_of_nonneg_right (Nat.cast_nonneg n))).2
          have heq : f (X₀ + (Nat.succ n : ℝ)) =
              f (X₀ + (n : ℝ)) * ratio f (X₀ + (n : ℝ)) := by
            rw [Nat.cast_succ]
            rw [show X₀ + ((n : ℝ) + 1) = X₀ + (n : ℝ) + 1 by ring]
            simp only [ratio]
            field_simp [hn.1.ne']
          have hstep : f (X₀ + (Nat.succ n : ℝ)) <
              f (X₀ + (n : ℝ)) * (1 / 2 : ℝ) := by
            rw [heq]
            exact mul_lt_mul_of_pos_left hr hn.1
          constructor
          · exact hposF _
          · calc
              f (X₀ + (Nat.succ n : ℝ)) ≤
                  f (X₀ + (n : ℝ)) * (1 / 2 : ℝ) := hstep.le
              _ ≤ (f X₀ * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) :=
                mul_le_mul_of_nonneg_right hn.2 (by norm_num)
              _ = f X₀ * (1 / 2 : ℝ) ^ Nat.succ n := by
                rw [pow_succ]
                simp [mul_assoc]
    have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    have hupper : Filter.Tendsto
        (fun n : ℕ => f X₀ * (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hpow)
    refine ⟨X₀, ?_⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper
      (fun n => (hboundNat n).1.le)
      (fun n => (hboundNat n).2)
  have hnzero : A₁ = 0 → False := gap8 f A₁ c hc hf hzero
  have hA : 0 < A₁ := gap9 A₁ hnonneg hnzero
  have hlogLocal : LocallyBounded (fun x => Real.log (f x)) :=
    gap11 f c hc hf hlocal
  have hlogRatio : Filter.Tendsto (fun x => Real.log (ratio f x))
      Filter.atTop (nhds (Real.log A₁)) := gap13 f A₁ hA hratio
  have hdiff : Filter.Tendsto
      (fun x => Real.log (f (x + 1)) - Real.log (f x))
      Filter.atTop (nhds (Real.log A₁)) := gap14 f A₁ hposF hlogRatio
  have hlog : Filter.Tendsto (fun x => Real.log (f x) / x)
      Filter.atTop (nhds (Real.log A₁)) := gap15 f A₁ hlogLocal hdiff
  exact gap20 f A₁ hA hposF hlog

end

end ProofGap.Exercise608_2
