import ProofGapLean.Prelude.Analysis

open Filter Topology

namespace ProofGap.Exercise124

noncomputable section

def nthRootN (n : ℕ) : ℝ :=
  Real.rpow n (1 / (n : ℝ))

/-- Exercise 124, gap 1. -/
theorem gap1 :
    Tendsto nthRootN atTop (𝓝 1) := by
  have hlog :
      Tendsto (fun r : ℝ => Real.log r / r) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    hlog.comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hexp :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log (n : ℝ) / (n : ℝ)))
        atTop (𝓝 (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hnat
  norm_num at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold nthRootN
  symm
  calc
    Real.rpow (n : ℝ) (1 / (n : ℝ)) =
        Real.exp (Real.log (n : ℝ) * (1 / (n : ℝ))) :=
      Real.rpow_def_of_pos (by exact_mod_cast hn) _
    _ = Real.exp (Real.log (n : ℝ) / (n : ℝ)) := by
      congr 1
      simp [div_eq_mul_inv]

private theorem mul_nthRootN_tendsto
    (x : ℕ → ℝ) (p : ℕ → ℕ) (l : ℝ)
    (hp : StrictMono p)
    (hx : Tendsto (x ∘ p) atTop (𝓝 l)) :
    Tendsto (fun k => x (p k) * nthRootN (p k)) atTop (𝓝 l) := by
  have hroot :
      Tendsto (nthRootN ∘ p) atTop (𝓝 1) :=
    gap1.comp hp.tendsto_atTop
  have hmul := hx.mul hroot
  norm_num at hmul
  exact hmul

/-- Exercise 124, gap 2. -/
theorem gap2
    (x : ℕ → ℝ)
    (y : ℕ → ℝ)
    (hy : ∀ n : ℕ, 0 < n → y n = x n * nthRootN n) :
    ∀ p : ℕ → ℕ, StrictMono p →
      (ProofGap.ConvergentSeq (x ∘ p) ↔
        ProofGap.ConvergentSeq (y ∘ p)) := by
  intro p hp
  have hroot :
      Tendsto (nthRootN ∘ p) atTop (𝓝 1) :=
    gap1.comp hp.tendsto_atTop
  have hevent : ∀ᶠ k : ℕ in atTop, 0 < p k :=
    hp.tendsto_atTop (eventually_ge_atTop 1)
  constructor
  · rintro ⟨l, hlim⟩
    refine ⟨l, ?_⟩
    have hmul :
        Tendsto
          (fun k : ℕ => x (p k) * nthRootN (p k))
          atTop (𝓝 l) :=
      mul_nthRootN_tendsto x p l hp hlim
    apply hmul.congr'
    filter_upwards [hevent] with k hk
    simpa [Function.comp_apply] using (hy (p k) hk).symm
  · rintro ⟨l, hlim⟩
    refine ⟨l, ?_⟩
    have hdiv :
        Tendsto
          (fun k : ℕ => y (p k) / nthRootN (p k))
          atTop (𝓝 (l / 1)) :=
      hlim.div hroot (by norm_num)
    norm_num at hdiv
    apply hdiv.congr'
    filter_upwards [hevent] with k hk
    have hpos : 0 < nthRootN (p k) := by
      unfold nthRootN
      exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _
    rw [hy (p k) hk]
    field_simp
    rfl

/-- Exercise 124, gap 3; equality of limits is a shared Tendsto value. -/
theorem gap3
    (x : ℕ → ℝ) (p : ℕ → ℕ) (l : ℝ)
    (hp : StrictMono p)
    (hx : Tendsto (x ∘ p) atTop (𝓝 l)) :
    Tendsto (fun k => x (p k) * nthRootN (p k)) atTop (𝓝 l) := by
  exact mul_nthRootN_tendsto x p l hp hx

/-- Exercise 124, gap 4. -/
theorem gap4
    (x y : ℕ → ℝ)
    (hy : ∀ n : ℕ, 0 < n → y n = x n * nthRootN n) :
    ProofGap.ClusterSet x = ProofGap.ClusterSet y := by
  ext l
  constructor
  · rintro ⟨p, hp, hlim⟩
    refine ⟨p, hp, ?_⟩
    have hmul := gap3 x p l hp hlim
    have hevent : ∀ᶠ k : ℕ in atTop, 0 < p k :=
      hp.tendsto_atTop (eventually_ge_atTop 1)
    apply hmul.congr'
    filter_upwards [hevent] with k hk
    simpa [Function.comp_apply] using (hy (p k) hk).symm
  · rintro ⟨p, hp, hlim⟩
    refine ⟨p, hp, ?_⟩
    have hroot :
        Tendsto (nthRootN ∘ p) atTop (𝓝 1) :=
      gap1.comp hp.tendsto_atTop
    have hdiv :
        Tendsto
          (fun k : ℕ => y (p k) / nthRootN (p k))
          atTop (𝓝 (l / 1)) :=
      hlim.div hroot (by norm_num)
    norm_num at hdiv
    have hevent : ∀ᶠ k : ℕ in atTop, 0 < p k :=
      hp.tendsto_atTop (eventually_ge_atTop 1)
    apply hdiv.congr'
    filter_upwards [hevent] with k hk
    have hpos : 0 < nthRootN (p k) := by
      unfold nthRootN
      exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _
    rw [hy (p k) hk]
    field_simp
    rfl

/-- Exercise 124, gap 5. -/
theorem gap5
    (x y : ℕ → ℝ)
    (h : ProofGap.ClusterSet x = ProofGap.ClusterSet y) :
    ProofGap.ClusterSet x = ProofGap.ClusterSet y := by
  exact h

end

end ProofGap.Exercise124
