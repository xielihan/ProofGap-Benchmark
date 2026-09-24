import ProofGapLean.Prelude.Full

namespace ProofGap.Exercise731_5

noncomputable section

noncomputable def f (x : ℝ) : ℝ := by
  classical
  exact if Irrational x then 0 else Real.sin (Real.pi * x)

def IsInteger (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)
def SingularPoint (g : ℝ → ℝ) (a : ℝ) : Prop := ¬ ContinuousAt g a

/-- Exercise 731_5, gap 1; remove the free outer
`SingularPoint(f,x)` guard and quantify the point whose limit is tested. -/
theorem gap1 :
    ∀ x : ℝ, ¬ IsInteger x →
      ¬ ∃ L : ℝ, Filter.Tendsto f (nhds x) (nhds L) := by
  intro x hx
  rintro ⟨L, hlim⟩
  have hLzero : L = 0 := by
    by_contra hne
    have hd : 0 < dist (0 : ℝ) L := dist_pos.mpr (Ne.symm hne)
    have hev : ∀ᶠ y in nhds x, dist (f y) L < dist (0 : ℝ) L :=
      (Metric.tendsto_nhds.1 hlim) (dist (0 : ℝ) L) hd
    rcases Metric.eventually_nhds_iff.1 hev with ⟨δ, hδ, hnear⟩
    obtain ⟨y, hyirr, hylo, hyhi⟩ :=
      exists_irrational_btwn (show x - δ < x + δ by linarith)
    have hydist : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hfy : f y = 0 := by
      simp [f, hyirr]
    have hclose := hnear hydist
    rw [hfy] at hclose
    exact (lt_irrefl _ hclose)
  have hsinL : Real.sin (Real.pi * x) = L := by
    by_contra hne
    have hd : 0 < dist (Real.sin (Real.pi * x)) L := dist_pos.mpr hne
    have hd3 : 0 < dist (Real.sin (Real.pi * x)) L / 3 := by
      positivity
    have hfnear :
        ∀ᶠ y in nhds x,
          dist (f y) L < dist (Real.sin (Real.pi * x)) L / 3 :=
      (Metric.tendsto_nhds.1 hlim)
        (dist (Real.sin (Real.pi * x)) L / 3) hd3
    have hcont :
        ContinuousAt (fun y : ℝ => Real.sin (Real.pi * y)) x :=
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).continuousAt
    have hgnear :
        ∀ᶠ y in nhds x,
          dist (Real.sin (Real.pi * y)) (Real.sin (Real.pi * x)) <
            dist (Real.sin (Real.pi * x)) L / 3 :=
      (Metric.tendsto_nhds.1 hcont)
        (dist (Real.sin (Real.pi * x)) L / 3) hd3
    rcases Metric.eventually_nhds_iff.1 (hfnear.and hgnear) with
      ⟨δ, hδ, hnear⟩
    obtain ⟨q, hqlo, hqhi⟩ :=
      exists_rat_btwn (show x - δ < x + δ by linarith)
    have hqdist : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    rcases hnear hqdist with ⟨hfclose, hgclose⟩
    have hqnot : ¬ Irrational (q : ℝ) := by
      simp [Irrational]
    have hfq : f (q : ℝ) = Real.sin (Real.pi * (q : ℝ)) := by
      simp [f, hqnot]
    have hqL :
        dist (Real.sin (Real.pi * (q : ℝ))) L <
          dist (Real.sin (Real.pi * x)) L / 3 := by
      simpa only [hfq] using hfclose
    have hxq :
        dist (Real.sin (Real.pi * x)) (Real.sin (Real.pi * (q : ℝ))) <
          dist (Real.sin (Real.pi * x)) L / 3 := by
      simpa only [dist_comm] using hgclose
    have hsum :
        dist (Real.sin (Real.pi * x)) (Real.sin (Real.pi * (q : ℝ))) +
            dist (Real.sin (Real.pi * (q : ℝ))) L <
          dist (Real.sin (Real.pi * x)) L := by
      linarith
    have hbad :
        dist (Real.sin (Real.pi * x)) L <
          dist (Real.sin (Real.pi * x)) L :=
      lt_of_le_of_lt
        (dist_triangle (Real.sin (Real.pi * x))
          (Real.sin (Real.pi * (q : ℝ))) L)
        hsum
    exact (lt_irrefl _ hbad)
  have hsin : Real.sin (Real.pi * x) = 0 := hsinL.trans hLzero
  apply hx
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  nlinarith [Real.pi_pos]

/-- Exercise 731_5, gap 2; remove the free outer guard. -/
theorem gap2 :
    ∀ x : ℝ, ¬ IsInteger x → SingularPoint f x := by
  intro x hx hcont
  exact gap1 x hx ⟨f x, hcont⟩

/-- Exercise 731_5, gap 3. -/
theorem gap3 (x : ℝ) (hx : x ∈ {x : ℝ | ¬ IsInteger x}) :
    SingularPoint f x := by
  exact gap2 x hx

end

end ProofGap.Exercise731_5
