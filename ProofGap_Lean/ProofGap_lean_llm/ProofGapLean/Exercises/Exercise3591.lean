import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/- Support development for Exercise3591, kept in the exercise module so the
benchmark case has no bespoke local-file dependency. -/

open scoped ContDiff

noncomputable section

namespace ProofGap.Exercise3591Support

abbrev P := ℝ × ℝ
private def ex : P := (1, 0)
private def ey : P := (0, 1)
private def lx : ℝ →L[ℝ] P := ContinuousLinearMap.inl ℝ ℝ ℝ
private def ly : ℝ →L[ℝ] P := ContinuousLinearMap.inr ℝ ℝ ℝ

private def evalCMLM {n : ℕ} (v : Fin n → P) :
    (P [×n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun M => M v
      map_add' := by intro M N; simp
      map_smul' := by intro c M; simp }
    (∏ i, ‖v i‖)
    (fun M => by
      simpa [mul_comm] using M.le_opNorm v)

private lemma exists_global_contDiff_eventuallyEq
    (f : P → ℝ) (p : P) (hf : ContDiffAt ℝ ω f p) :
    ∃ g : P → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[nhds p] f := by
  rcases hf.contDiffOn' le_rfl (by simp) with ⟨u, hu_open, hpu, hfu⟩
  simp only [Set.insert_eq_of_mem (Set.mem_univ p), Set.univ_inter] at hfu
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 (hu_open.mem_nhds hpu)
  let b : ContDiffBump p :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g : P → ℝ := fun z => b z * f z
  have hb_support : tsupport (b : P → ℝ) ⊆ u := by
    rw [b.tsupport_eq]
    change Metric.closedBall p (r / 2) ⊆ u
    exact (Metric.closedBall_subset_ball (by linarith)).trans hru
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (b : P → ℝ)
    · have hb : ContDiff ℝ ∞ (b : P → ℝ) := b.contDiff
      have hff : ContDiffAt ℝ ∞ f z :=
        (hfu.contDiffAt (hu_open.mem_nhds (hb_support hz))).of_le
          (le_of_lt (WithTop.coe_lt_top (⊤ : ℕ∞)))
      exact hb.contDiffAt.mul
        hff
    · have hbzero : (b : P → ℝ) =ᶠ[nhds z] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 hz
      have hgzero : g =ᶠ[nhds z] (fun _ => 0) := by
        filter_upwards [hbzero] with w hw
        simp [g, hw]
      exact contDiffAt_const.congr_of_eventuallyEq hgzero
  refine ⟨g, hg, ?_⟩
  filter_upwards [b.eventuallyEq_one] with z hz
  simp [g, hz]

private lemma dependent_multilinear_app_cast
    (A : (n : ℕ) → P [×n]→L[ℝ] ℝ) {n m : ℕ}
    (e : n = m) (v : Fin n → P) :
    A n v = A m (v ∘ Fin.cast e.symm) := by
  subst m
  rfl

private lemma iterX_eq (f : P → ℝ) (hf : ContDiff ℝ ∞ f)
    (mx : ℕ) (x y : ℝ) :
    (deriv^[mx]) (fun z => f (z, y)) x =
      iteratedFDeriv ℝ mx f (x, y) (fun _ => ex) := by
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_eq_iteratedFDeriv]
  have hs : ContDiff ℝ ∞ (fun z : P => f (z + (0, y))) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hmx : (mx : WithTop ℕ∞) ≤ ∞ := by
    norm_cast
    exact le_top
  have H := lx.iteratedFDeriv_comp_right hs x (i := mx) hmx
  have H' := congrArg (fun M : ℝ [×mx]→L[ℝ] ℝ => M (fun _ => (1 : ℝ))) H
  simp [lx, Function.comp_def] at H'
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) mx (0, y) (x, 0)] at H'
  simpa [Function.comp_def, lx, ex] using H'

private lemma iterated_iterated_eq
    (f : P → ℝ) (hf : ContDiff ℝ ∞ f)
    (mx my : ℕ) (p : P) (vx : Fin mx → P) (vy : Fin my → P) :
    (iteratedFDeriv ℝ my (iteratedFDeriv ℝ mx f) p vy) vx =
      iteratedFDeriv ℝ (my + mx) f p (Fin.append vy vx) := by
  induction my generalizing p with
  | zero =>
      simp only [iteratedFDeriv_zero_apply, zero_add]
      have hv : vy = Fin.elim0 := Subsingleton.elim _ _
      subst vy
      simp only [Fin.elim0_append]
      exact dependent_multilinear_app_cast
        (fun n => iteratedFDeriv ℝ n f p) (Nat.zero_add mx).symm vx
  | succ my ih =>
      have hmy : (my : WithTop ℕ∞) < ∞ := by
        norm_cast
        exact ENat.coe_lt_top my
      have hc : ContDiff ℝ ∞ (iteratedFDeriv ℝ mx f) :=
        hf.iteratedFDeriv_right (by norm_cast)
      have hd :
          Differentiable ℝ (iteratedFDeriv ℝ my (iteratedFDeriv ℝ mx f)) :=
        hc.differentiable_iteratedFDeriv hmy
      have hd₁ :
          Differentiable ℝ
            (fun z =>
              iteratedFDeriv ℝ my (iteratedFDeriv ℝ mx f) z (Fin.tail vy)) :=
        hd.continuousMultilinear_apply_const (Fin.tail vy)
      rw [iteratedFDeriv_succ_apply_left]
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hd p) (Fin.tail vy) (vy 0)]
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hd₁ p) vx (vy 0)]
      have heq :
          (fun z =>
              (iteratedFDeriv ℝ my (iteratedFDeriv ℝ mx f) z (Fin.tail vy)) vx) =
            (fun z =>
              iteratedFDeriv ℝ (my + mx) f z (Fin.append (Fin.tail vy) vx)) := by
        funext z
        exact ih z (Fin.tail vy)
      rw [heq]
      have htotal : DifferentiableAt ℝ (iteratedFDeriv ℝ (my + mx) f) p := by
        apply hf.differentiable_iteratedFDeriv
        norm_cast
        exact ENat.coe_lt_top (my + mx)
      rw [fderiv_continuousMultilinear_apply_const_apply
        htotal (Fin.append (Fin.tail vy) vx) (vy 0)]
      calc
        ((fderiv ℝ (iteratedFDeriv ℝ (my + mx) f) p) (vy 0))
              (Fin.append (Fin.tail vy) vx) =
            iteratedFDeriv ℝ (my + mx + 1) f p
              (Fin.cons (vy 0) (Fin.append (Fin.tail vy) vx)) := by
                symm
                exact iteratedFDeriv_succ_apply_left _
        _ = iteratedFDeriv ℝ (my + 1 + mx) f p (Fin.append vy vx) := by
          conv_rhs =>
            rw [← Fin.cons_self_tail vy, Fin.append_cons]
          exact dependent_multilinear_app_cast
            (fun n => iteratedFDeriv ℝ n f p)
            (Nat.add_right_comm my 1 mx).symm
            (Fin.cons (vy 0) (Fin.append (Fin.tail vy) vx))

def iterXY0 (mx my : ℕ) (f : P → ℝ) (p : P) : ℝ :=
  (deriv^[my])
    (fun y => (deriv^[mx]) (fun x => f (x, y)) p.1) p.2

private lemma iterXY0_congr
    (f g : P → ℝ) (p : P) (hgf : g =ᶠ[nhds p] f)
    (mx my : ℕ) :
    iterXY0 mx my g p = iterXY0 mx my f p := by
  rw [iterXY0, iterXY0]
  simp only [← iteratedDeriv_eq_iterate]
  rw [nhds_prod_eq] at hgf
  rcases Filter.eventually_prod_iff.1 hgf with
    ⟨px, hpx, py, hpy, hxy⟩
  have hout :
      (fun y => iteratedDeriv mx (fun x => g (x, y)) p.1) =ᶠ[nhds p.2]
        (fun y => iteratedDeriv mx (fun x => f (x, y)) p.1) := by
    filter_upwards [hpy] with y hy
    apply Filter.EventuallyEq.iteratedDeriv_eq mx
    exact hpx.mono (fun x hx => hxy hx hy)
  exact Filter.EventuallyEq.iteratedDeriv_eq my hout

private lemma iterXY0_eq_total
    (f : P → ℝ) (hf : ContDiff ℝ ∞ f)
    (mx my : ℕ) (p : P) :
    iterXY0 mx my f p =
      iteratedFDeriv ℝ (my + mx) f p
        (Fin.append (fun _ => ey) (fun _ => ex)) := by
  have hfun :
      (fun y => (deriv^[mx]) (fun x => f (x, y)) p.1) =
        (fun y =>
          evalCMLM (fun _ : Fin mx => ex)
            (iteratedFDeriv ℝ mx f (p.1, y))) := by
    funext y
    exact iterX_eq f hf mx p.1 y
  rw [iterXY0, hfun, ← iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iteratedFDeriv]
  have hc : ContDiff ℝ ∞ (iteratedFDeriv ℝ mx f) :=
    hf.iteratedFDeriv_right (by norm_cast)
  have hA : ContDiff ℝ ∞
      (fun z =>
        evalCMLM (fun _ : Fin mx => ex) (iteratedFDeriv ℝ mx f z)) :=
    (evalCMLM (fun _ : Fin mx => ex)).contDiff.comp hc
  have hs : ContDiff ℝ ∞
      (fun z : P =>
        evalCMLM (fun _ : Fin mx => ex)
          (iteratedFDeriv ℝ mx f (z + (p.1, 0)))) :=
    hA.comp (contDiff_id.add contDiff_const)
  have hmy : (my : WithTop ℕ∞) ≤ ∞ := by
    norm_cast
    exact le_top
  have H := ly.iteratedFDeriv_comp_right hs p.2 (i := my) hmy
  have H' := congrArg
    (fun M : ℝ [×my]→L[ℝ] ℝ => M (fun _ => (1 : ℝ))) H
  simp [ly, Function.comp_def] at H'
  rw [iteratedFDeriv_comp_add_right
    (f := fun z : P =>
      evalCMLM (fun _ : Fin mx => ex) (iteratedFDeriv ℝ mx f z))
    (𝕜 := ℝ) my (p.1, 0) (0, p.2)] at H'
  have H'' :
      (iteratedFDeriv ℝ my
          (fun y =>
            evalCMLM (fun _ : Fin mx => ex)
              (iteratedFDeriv ℝ mx f (p.1, y))) p.2)
          (fun _ => (1 : ℝ)) =
        (iteratedFDeriv ℝ my
          (fun z =>
            evalCMLM (fun _ : Fin mx => ex)
              (iteratedFDeriv ℝ mx f z)) p)
          (fun _ => ey) := by
    simpa [Prod.ext_iff] using H'
  have HE := (evalCMLM (fun _ : Fin mx => ex)).iteratedFDeriv_comp_left
    (hc.contDiffAt (x := p)) (i := my) hmy
  have HE' := congrArg
    (fun M : P [×my]→L[ℝ] ℝ => M (fun _ => ey)) HE
  simp [evalCMLM, Function.comp_def] at HE'
  rw [H'']
  change
    (iteratedFDeriv ℝ my
        (fun z => iteratedFDeriv ℝ mx f z (fun _ => ex)) p)
        (fun _ => ey) =
      iteratedFDeriv ℝ (my + mx) f p
        (Fin.append (fun _ => ey) (fun _ => ex))
  rw [HE']
  exact iterated_iterated_eq f hf mx my p
    (fun _ => ex) (fun _ => ey)

private lemma iterXY0_eq_total_of_analytic
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (mx my : ℕ) :
    iterXY0 mx my f p =
      iteratedFDeriv ℝ (my + mx) f p
        (Fin.append (fun _ => ey) (fun _ => ex)) := by
  rcases exists_global_contDiff_eventuallyEq f p hf.contDiffAt with
    ⟨g, hg, hgf⟩
  have hd :
      iteratedFDeriv ℝ (my + mx) g p =
        iteratedFDeriv ℝ (my + mx) f p :=
    (hgf.iteratedFDeriv ℝ (my + mx)).eq_of_nhds
  calc
    iterXY0 mx my f p = iterXY0 mx my g p :=
      (iterXY0_congr f g p hgf mx my).symm
    _ = iteratedFDeriv ℝ (my + mx) g p
        (Fin.append (fun _ => ey) (fun _ => ex)) :=
      iterXY0_eq_total g hg mx my p
    _ = iteratedFDeriv ℝ (my + mx) f p
        (Fin.append (fun _ => ey) (fun _ => ex)) := by rw [hd]

private lemma iteratedFDeriv_piecewise_eq_iterXY0
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n mx : ℕ) (hmx : mx ≤ n)
    (s : Finset (Fin n)) (hs : s.card = n - mx) :
    iteratedFDeriv ℝ n f p
        (s.piecewise (fun _ => ey) (fun _ => ex)) =
      iterXY0 mx (n - mx) f p := by
  let my := n - mx
  have e : my + mx = n := Nat.sub_add_cancel hmx
  have hsc : sᶜ.card = mx := by
    rw [Finset.card_compl, Fintype.card_fin, hs]
    omega
  let eS : Fin my ⊕ Fin mx ≃ Fin n :=
    finSumEquivOfFinset hs hsc
  let eC : Fin my ⊕ Fin mx ≃ Fin n :=
    finSumFinEquiv.trans (finCongr e)
  let σ : Equiv.Perm (Fin n) := eS.symm.trans eC
  let v : Fin n → P :=
    Fin.append (fun _ : Fin my => ey) (fun _ : Fin mx => ex) ∘
      Fin.cast e.symm
  have hv :
      v ∘ σ = s.piecewise (fun _ => ey) (fun _ => ex) := by
    funext i
    cases hi : eS.symm i with
    | inl j =>
        have hii : i = eS (Sum.inl j) := by
          rw [← eS.apply_symm_apply i, hi]
        subst i
        simp [v, σ, eC, eS, Finset.piecewise_eq_of_mem]
        rw [← finSumEquivOfFinset_inl hs hsc]
        rw [Equiv.symm_apply_apply]
        rw [finSumFinEquiv_apply_left, Fin.append_left]
    | inr j =>
        have hii : i = eS (Sum.inr j) := by
          rw [← eS.apply_symm_apply i, hi]
        subst i
        simp [v, σ, eC, eS, Finset.piecewise_eq_of_notMem]
        rw [← finSumEquivOfFinset_inr hs hsc]
        rw [Equiv.symm_apply_apply]
        have hnot :
            finSumEquivOfFinset hs hsc (Sum.inr j) ∉ s := by
          rw [finSumEquivOfFinset_inr]
          exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem sᶜ hsc j)
        rw [finSumFinEquiv_apply_right, Fin.append_right]
        exact (Finset.piecewise_eq_of_notMem
          s (fun _ => ey) (fun _ => ex) hnot).symm
  have hperm :=
    hf.contDiffAt.iteratedFDeriv_comp_perm v σ
  rw [hv] at hperm
  have hcast :
      iteratedFDeriv ℝ my f p
          (Fin.append (fun _ : Fin my => ey) (fun _ : Fin 0 => ex)) =
        iteratedFDeriv ℝ my f p
          (Fin.append (fun _ : Fin my => ey) (fun _ : Fin 0 => ex)) := rfl
  have hdegree :
      iteratedFDeriv ℝ (my + mx) f p
          (Fin.append (fun _ : Fin my => ey) (fun _ : Fin mx => ex)) =
        iteratedFDeriv ℝ n f p v := by
    exact dependent_multilinear_app_cast
      (fun degree => iteratedFDeriv ℝ degree f p) e
      (Fin.append (fun _ : Fin my => ey) (fun _ : Fin mx => ex))
  rw [hperm, ← hdegree]
  exact (iterXY0_eq_total_of_analytic f hf mx my).symm

private lemma iteratedFDeriv_piecewise_smul_eq
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n : ℕ) (s : Finset (Fin n)) (h k : ℝ) :
    iteratedFDeriv ℝ n f p
        (s.piecewise (fun _ => h • ex) (fun _ => k • ey)) =
      (h ^ s.card * k ^ (n - s.card)) *
        iterXY0 s.card (n - s.card) f p := by
  let c : Fin n → ℝ := s.piecewise (fun _ => h) (fun _ => k)
  let v : Fin n → P := s.piecewise (fun _ => ex) (fun _ => ey)
  have hcv :
      s.piecewise (fun _ => h • ex) (fun _ => k • ey) =
        fun i => c i • v i := by
    funext i
    by_cases hi : i ∈ s <;> simp [c, v, Finset.piecewise, hi]
  rw [hcv, ContinuousMultilinearMap.map_smul_univ]
  have hcprod :
      (∏ i, c i) = h ^ s.card * k ^ (n - s.card) := by
    rw [show (∏ i, c i) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), c i by simp]
    rw [Finset.prod_piecewise]
    simp only [Finset.univ_inter, Finset.prod_const]
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl,
      Fintype.card_fin]
  rw [hcprod]
  congr 1
  have hsle : s.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  have hscomp : sᶜ.card = n - s.card := by
    simpa using Finset.card_compl s
  have hvcomp :
      v = sᶜ.piecewise (fun _ => ey) (fun _ => ex) := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [v, Finset.piecewise, hi, Finset.mem_compl]
  rw [hvcomp]
  exact iteratedFDeriv_piecewise_eq_iterXY0
    f hf n s.card hsle sᶜ hscomp

private lemma iteratedFDeriv_diag_eq_sum
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n : ℕ) (h k : ℝ) :
    iteratedFDeriv ℝ n f p (fun _ => (h, k)) =
      ∑ mx ∈ Finset.range (n + 1),
        (n.choose mx : ℝ) *
          (h ^ mx * k ^ (n - mx) * iterXY0 mx (n - mx) f p) := by
  let D := iteratedFDeriv ℝ n f p
  have hvec :
      (fun _ : Fin n => (h, k)) =
        (fun _ => h • ex) + (fun _ => k • ey) := by
    funext i
    ext <;> simp [ex, ey]
  rw [hvec, D.map_add_univ]
  rw [← Finset.powerset_univ]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro mx hmx
  have hmxle : mx ≤ n := by
    simpa [Finset.mem_range] using hmx
  rw [show
      (∑ s ∈ Finset.powersetCard mx (Finset.univ : Finset (Fin n)),
          D (s.piecewise (fun _ => h • ex) (fun _ => k • ey))) =
        ∑ s ∈ Finset.powersetCard mx (Finset.univ : Finset (Fin n)),
          (h ^ s.card * k ^ (n - s.card)) *
            iterXY0 s.card (n - s.card) f p by
      apply Finset.sum_congr rfl
      intro s hs
      exact iteratedFDeriv_piecewise_smul_eq f hf n s h k]
  change
    (∑ s ∈ Finset.powersetCard mx (Finset.univ : Finset (Fin n)),
      (fun j => h ^ j * k ^ (n - j) * iterXY0 j (n - j) f p) s.card) =
      _
  calc
    _ = (Finset.univ : Finset (Fin n)).card.choose mx •
        (h ^ mx * k ^ (n - mx) * iterXY0 mx (n - mx) f p) :=
      Finset.sum_powersetCard mx (Finset.univ : Finset (Fin n))
        (fun j => h ^ j * k ^ (n - j) * iterXY0 j (n - j) f p)
    _ = _ := by
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat, Nat.cast_choose]

private lemma taylorCoefficient_eq_sum
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n : ℕ) (h k : ℝ) :
    (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n f p (fun _ => (h, k)) =
      ∑ mx ∈ Finset.range (n + 1),
        (h ^ mx * k ^ (n - mx) /
          ((mx.factorial : ℝ) * ((n - mx).factorial : ℝ))) *
          iterXY0 mx (n - mx) f p := by
  rw [iteratedFDeriv_diag_eq_sum f hf n h k]
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mx hmx
  have hmxle : mx ≤ n := by
    simpa [Finset.mem_range] using hmx
  have hfac :
      (n.choose mx : ℝ) * (mx.factorial : ℝ) *
          ((n - mx).factorial : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmxle
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hmxn : (mx.factorial : ℝ) ≠ 0 := by positivity
  have hmyn : ((n - mx).factorial : ℝ) ≠ 0 := by positivity
  have hden :
      (mx.factorial : ℝ) * ((n - mx).factorial : ℝ) ≠ 0 :=
    mul_ne_zero hmxn hmyn
  have hcoef :
      (n.factorial : ℝ)⁻¹ * (n.choose mx : ℝ) =
        1 / ((mx.factorial : ℝ) * ((n - mx).factorial : ℝ)) := by
    rw [eq_div_iff hden]
    calc
      (n.factorial : ℝ)⁻¹ * (n.choose mx : ℝ) *
            ((mx.factorial : ℝ) * ((n - mx).factorial : ℝ)) =
          (n.factorial : ℝ)⁻¹ *
            ((n.choose mx : ℝ) * (mx.factorial : ℝ) *
              ((n - mx).factorial : ℝ)) := by ring
      _ = (n.factorial : ℝ)⁻¹ * (n.factorial : ℝ) := by rw [hfac]
      _ = 1 := inv_mul_cancel₀ hn
  calc
    (n.factorial : ℝ)⁻¹ *
          ((n.choose mx : ℝ) *
            (h ^ mx * k ^ (n - mx) * iterXY0 mx (n - mx) f p)) =
        ((n.factorial : ℝ)⁻¹ * (n.choose mx : ℝ)) *
          (h ^ mx * k ^ (n - mx)) *
          iterXY0 mx (n - mx) f p := by ring
    _ = (1 / ((mx.factorial : ℝ) * ((n - mx).factorial : ℝ))) *
          (h ^ mx * k ^ (n - mx)) *
          iterXY0 mx (n - mx) f p := by rw [hcoef]
    _ = _ := by ring

def jointTerm0 (f : P → ℝ) (p : P) (h k : ℝ)
    (degree : ℕ) : ℝ :=
  ∑ mx ∈ Finset.range (degree + 1),
    (h ^ mx * k ^ (degree - mx) /
      ((mx.factorial : ℝ) * ((degree - mx).factorial : ℝ))) *
      iterXY0 mx (degree - mx) f p

def xTerm0 (f : P → ℝ) (p : P) (h : ℝ) (mx : ℕ) : ℝ :=
  h ^ mx / (mx.factorial : ℝ) * iterXY0 mx 0 f p

def yTerm0 (f : P → ℝ) (p : P) (k : ℝ) (my : ℕ) : ℝ :=
  k ^ my / (my.factorial : ℝ) * iterXY0 0 my f p

private lemma eventually_hasSum_joint
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      HasSum (jointTerm0 f p q.1 q.2) (f (p + q)) := by
  rcases hf with ⟨series, r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : P) hr.r_pos] with q hq
  refine HasSum.congr_fun (hr.hasSum_iteratedFDeriv hq) (fun degree => ?_)
  exact (taylorCoefficient_eq_sum f hr.analyticAt degree q.1 q.2).symm

private lemma taylorCoefficient_x
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n : ℕ) (h : ℝ) :
    (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n f p (fun _ => (h, 0)) =
      xTerm0 f p h n := by
  have hD := iteratedFDeriv_piecewise_smul_eq
    f hf n (Finset.univ : Finset (Fin n)) h 0
  simp only [Finset.piecewise_same, Finset.card_univ,
    Fintype.card_fin, Nat.sub_self, pow_zero, mul_one] at hD
  have hfun :
      (fun _ : Fin n => h • ex) = (fun _ => (h, 0)) := by
    funext i
    simp [ex]
  have hD' :
      iteratedFDeriv ℝ n f p (fun _ => (h, 0)) =
        h ^ n * iterXY0 n 0 f p := by
    rw [← hfun]
    simpa [Finset.piecewise] using hD
  rw [hD']
  simp only [xTerm0, smul_eq_mul]
  ring

private lemma taylorCoefficient_y
    (f : P → ℝ) (hf : AnalyticAt ℝ f p)
    (n : ℕ) (k : ℝ) :
    (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n f p (fun _ => (0, k)) =
      yTerm0 f p k n := by
  have hD := iteratedFDeriv_piecewise_smul_eq
    f hf n (∅ : Finset (Fin n)) 0 k
  simp only [Finset.piecewise_empty, Finset.card_empty, zero_pow,
    Nat.sub_zero, one_mul] at hD
  have hfun :
      (fun _ : Fin n => k • ey) = (fun _ => (0, k)) := by
    funext i
    simp [ey]
  have hD' :
      iteratedFDeriv ℝ n f p (fun _ => (0, k)) =
        k ^ n * iterXY0 0 n f p := by
    rw [← hfun]
    simpa [Finset.piecewise] using hD
  rw [hD']
  simp only [yTerm0, smul_eq_mul]
  ring

private lemma eventually_hasSum_x
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ h : ℝ in nhds 0,
      HasSum (xTerm0 f p h) (f (p + (h, 0))) := by
  rcases hf with ⟨series, r, hr⟩
  have he :
      Filter.Tendsto (fun h : ℝ => (h, 0)) (nhds 0) (nhds (0 : P)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards
    [he.eventually (Metric.eball_mem_nhds (0 : P) hr.r_pos)] with h hh
  refine HasSum.congr_fun (hr.hasSum_iteratedFDeriv hh) (fun n => ?_)
  exact (taylorCoefficient_x f hr.analyticAt n h).symm

private lemma eventually_hasSum_y
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ k : ℝ in nhds 0,
      HasSum (yTerm0 f p k) (f (p + (0, k))) := by
  rcases hf with ⟨series, r, hr⟩
  have he :
      Filter.Tendsto (fun k : ℝ => (0, k)) (nhds 0) (nhds (0 : P)) :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards
    [he.eventually (Metric.eball_mem_nhds (0 : P) hr.r_pos)] with k hk
  refine HasSum.congr_fun (hr.hasSum_iteratedFDeriv hk) (fun n => ?_)
  exact (taylorCoefficient_y f hr.analyticAt n k).symm

def jointSeries0 (f : P → ℝ) (p : P) (h k : ℝ) : ℝ :=
  ∑' degree, jointTerm0 f p h k degree

def xSeries0 (f : P → ℝ) (p : P) (h : ℝ) : ℝ :=
  ∑' mx, xTerm0 f p h mx

def ySeries0 (f : P → ℝ) (p : P) (k : ℝ) : ℝ :=
  ∑' my, yTerm0 f p k my

private lemma eventually_series_values
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      jointSeries0 f p q.1 q.2 = f (p + q) ∧
      xSeries0 f p q.1 = f (p + (q.1, 0)) ∧
      ySeries0 f p q.2 = f (p + (0, q.2)) := by
  have hj := eventually_hasSum_joint f p hf
  have hx := eventually_hasSum_x f p hf
  have hy := eventually_hasSum_y f p hf
  filter_upwards
    [hj, continuousAt_fst.eventually hx, continuousAt_snd.eventually hy]
      with q hq hxq hyq
  exact ⟨hq.tsum_eq, hxq.tsum_eq, hyq.tsum_eq⟩

theorem gap1_0
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      f (p.1 + q.1, p.2 + q.2) -
            f (p.1 + q.1, p.2) -
            f (p.1, p.2 + q.2) + f p =
        jointSeries0 f p q.1 q.2 -
            xSeries0 f p q.1 -
            ySeries0 f p q.2 + f p := by
  filter_upwards [eventually_series_values f p hf] with q hq
  rcases hq with ⟨hj, hx, hy⟩
  rw [hj, hx, hy]
  have hpq : p + q = (p.1 + q.1, p.2 + q.2) := by
    ext <;> simp
  have hpx : p + (q.1, 0) = (p.1 + q.1, p.2) := by
    ext <;> simp
  have hpy : p + (0, q.2) = (p.1, p.2 + q.2) := by
    ext <;> simp
  rw [hpq, hpx, hpy]

def coeff0 (f : P → ℝ) (p : P) (h k : ℝ)
    (degree mx : ℕ) : ℝ :=
  (h ^ mx * k ^ (degree - mx) /
    ((mx.factorial : ℝ) * ((degree - mx).factorial : ℝ))) *
    iterXY0 mx (degree - mx) f p

def mixedTerm0 (f : P → ℝ) (p : P) (h k : ℝ)
    (degree : ℕ) : ℝ :=
  ∑ mx ∈ Finset.Icc 1 (degree - 1), coeff0 f p h k degree mx

private lemma jointTerm_sub_axes
    (f : P → ℝ) (p : P) (h k : ℝ) (degree : ℕ) :
    jointTerm0 f p h k degree -
          xTerm0 f p h degree -
          yTerm0 f p k degree +
          (if degree = 0 then f p else 0) =
      mixedTerm0 f p h k degree := by
  cases degree with
  | zero =>
      simp [jointTerm0, xTerm0, yTerm0, mixedTerm0, coeff0, iterXY0]
  | succ n =>
      have hset :
          Finset.range (n + 1 + 1) =
            insert 0 (insert (n + 1) (Finset.Icc 1 n)) := by
        ext j
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnmem : n + 1 ∉ Finset.Icc 1 n := by
        simp
      have h0mem : 0 ∉ insert (n + 1) (Finset.Icc 1 n) := by
        simp
      rw [jointTerm0, show n + 1 + 1 = n + 2 by omega, hset]
      simp only [Finset.sum_insert h0mem, Finset.sum_insert hnmem]
      simp [coeff0, xTerm0, yTerm0, mixedTerm0, iterXY0]
      ring

private lemma eventually_hasSum_mixed
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      HasSum (mixedTerm0 f p q.1 q.2)
        (f (p + q) - f (p + (q.1, 0)) -
          f (p + (0, q.2)) + f p) := by
  have hj := eventually_hasSum_joint f p hf
  have hx := eventually_hasSum_x f p hf
  have hy := eventually_hasSum_y f p hf
  filter_upwards
    [hj, continuousAt_fst.eventually hx, continuousAt_snd.eventually hy]
      with q hq hxq hyq
  have hraw :=
    ((hq.sub hxq).sub hyq).add (hasSum_ite_eq (0 : ℕ) (f p))
  refine HasSum.congr_fun hraw (fun degree => ?_)
  exact (jointTerm_sub_axes f p q.1 q.2 degree).symm

theorem gap2_0
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      f (p.1 + q.1, p.2 + q.2) -
            f (p.1 + q.1, p.2) -
            f (p.1, p.2 + q.2) + f p =
        ∑' degree, mixedTerm0 f p q.1 q.2 degree := by
  filter_upwards [eventually_hasSum_mixed f p hf] with q hq
  rw [hq.tsum_eq]
  have hpq : p + q = (p.1 + q.1, p.2 + q.2) := by
    ext <;> simp
  have hpx : p + (q.1, 0) = (p.1 + q.1, p.2) := by
    ext <;> simp
  have hpy : p + (0, q.2) = (p.1, p.2 + q.2) := by
    ext <;> simp
  rw [hpq, hpx, hpy]

def tailTerm0 (f : P → ℝ) (p : P) (h k : ℝ)
    (degree : ℕ) : ℝ :=
  if 3 ≤ degree then
    ∑ mx ∈ Finset.Icc 1 (degree - 1),
      (h ^ (mx - 1) * k ^ (degree - mx - 1) /
        ((mx.factorial : ℝ) * ((degree - mx).factorial : ℝ))) *
        iterXY0 mx (degree - mx) f p
  else 0

private def coreTerm0 (f : P → ℝ) (p : P) (h k : ℝ)
    (degree : ℕ) : ℝ :=
  (if degree = 2 then iterXY0 1 1 f p else 0) +
    tailTerm0 f p h k degree

private lemma mixedTerm_factor
    (f : P → ℝ) (p : P) (h k : ℝ) (degree : ℕ) :
    mixedTerm0 f p h k degree =
      h * k * coreTerm0 f p h k degree := by
  by_cases h0 : degree = 0
  · subst degree
    simp [mixedTerm0, coreTerm0, tailTerm0]
  by_cases h1 : degree = 1
  · subst degree
    simp [mixedTerm0, coreTerm0, tailTerm0]
  by_cases h2 : degree = 2
  · subst degree
    simp [mixedTerm0, coreTerm0, tailTerm0, coeff0]
  have hd3 : 3 ≤ degree := by omega
  simp only [mixedTerm0, coreTerm0, h2, if_false, zero_add,
    tailTerm0, hd3, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mx hmx
  rw [Finset.mem_Icc] at hmx
  have hmxpos : 1 ≤ mx := hmx.1
  have hmyle : mx ≤ degree := by omega
  have hmypos : 1 ≤ degree - mx := by omega
  have hxpow : h ^ mx = h * h ^ (mx - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hmxpos]
    rw [pow_succ]
    ring
  have hkpow :
      k ^ (degree - mx) = k * k ^ (degree - mx - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hmypos]
    rw [pow_succ]
    ring
  simp only [coeff0, hxpow, hkpow]
  ring

private lemma mixedSeries_factor
    (f : P → ℝ) (p : P) (h k : ℝ)
    (hs : Summable (mixedTerm0 f p h k)) :
    (∑' degree, mixedTerm0 f p h k degree) =
      h * k *
        (iterXY0 1 1 f p + ∑' degree, tailTerm0 f p h k degree) := by
  by_cases hhk : h * k = 0
  · calc
      (∑' degree, mixedTerm0 f p h k degree) =
          ∑' degree, h * k * coreTerm0 f p h k degree :=
        tsum_congr (fun degree => mixedTerm_factor f p h k degree)
      _ = 0 := by simp [hhk]
      _ = h * k *
          (iterXY0 1 1 f p + ∑' degree, tailTerm0 f p h k degree) := by
        rw [hhk, zero_mul]
  · let delta : ℕ → ℝ :=
      fun degree => if degree = 2 then iterXY0 1 1 f p else 0
    have hcore : Summable (coreTerm0 f p h k) := by
      have H := hs.mul_left ((h * k)⁻¹)
      refine H.congr (fun degree => ?_)
      rw [mixedTerm_factor]
      calc
        (h * k)⁻¹ * (h * k * coreTerm0 f p h k degree) =
            ((h * k)⁻¹ * (h * k)) * coreTerm0 f p h k degree := by
          ring
        _ = coreTerm0 f p h k degree := by
          rw [inv_mul_cancel₀ hhk, one_mul]
    have hdelta : Summable delta :=
      (hasSum_ite_eq (2 : ℕ) (iterXY0 1 1 f p)).summable
    have htail : Summable (tailTerm0 f p h k) := by
      have H := hcore.sub hdelta
      refine H.congr (fun degree => ?_)
      simp [coreTerm0, delta]
    have hcore_tsum :
        (∑' degree, coreTerm0 f p h k degree) =
          iterXY0 1 1 f p +
            ∑' degree, tailTerm0 f p h k degree := by
      calc
        (∑' degree, coreTerm0 f p h k degree) =
            (∑' degree,
              (delta degree + tailTerm0 f p h k degree)) := by
          apply tsum_congr
          intro degree
          simp [coreTerm0, delta]
        _ = (∑' degree, delta degree) +
              ∑' degree, tailTerm0 f p h k degree :=
          hdelta.tsum_add htail
        _ = iterXY0 1 1 f p +
              ∑' degree, tailTerm0 f p h k degree := by
          rw [show (∑' degree, delta degree) = iterXY0 1 1 f p by
            simpa [delta] using
              (tsum_ite_eq (2 : ℕ) (fun _ : ℕ => iterXY0 1 1 f p))]
    calc
      (∑' degree, mixedTerm0 f p h k degree) =
          ∑' degree, h * k * coreTerm0 f p h k degree :=
        tsum_congr (fun degree => mixedTerm_factor f p h k degree)
      _ = h * k * ∑' degree, coreTerm0 f p h k degree :=
        tsum_mul_left
      _ = _ := by rw [hcore_tsum]

theorem gap3_0
    (f : P → ℝ) (p : P) (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : P in nhds 0,
      f (p.1 + q.1, p.2 + q.2) -
            f (p.1 + q.1, p.2) -
            f (p.1, p.2 + q.2) + f p =
        q.1 * q.2 *
          (iterXY0 1 1 f p +
            ∑' degree, tailTerm0 f p q.1 q.2 degree) := by
  filter_upwards [eventually_hasSum_mixed f p hf] with q hq
  have hpq : p + q = (p.1 + q.1, p.2 + q.2) := by
    ext <;> simp
  have hpx : p + (q.1, 0) = (p.1 + q.1, p.2) := by
    ext <;> simp
  have hpy : p + (0, q.2) = (p.1, p.2 + q.2) := by
    ext <;> simp
  rw [← hpq, ← hpx, ← hpy]
  calc
    f (p + q) - f (p + (q.1, 0)) - f (p + (0, q.2)) + f p =
        ∑' degree, mixedTerm0 f p q.1 q.2 degree :=
      hq.tsum_eq.symm
    _ = _ := mixedSeries_factor f p q.1 q.2 hq.summable

end ProofGap.Exercise3591Support

namespace ProofGap.Exercise3591

noncomputable section

abbrev Point2 := ℝ × ℝ

def iterXY (mx my : ℕ) (f : Point2 → ℝ) (p : Point2) : ℝ :=
  (deriv^[my])
    (fun y => (deriv^[mx]) (fun x => f (x, y)) p.1) p.2

def mixedDifference (f : Point2 → ℝ) (p : Point2) (h k : ℝ) : ℝ :=
  f (p.1 + h, p.2 + k) - f (p.1 + h, p.2) -
    f (p.1, p.2 + k) + f p

def jointTaylorSeries (f : Point2 → ℝ) (p : Point2) (h k : ℝ) : ℝ :=
  ∑' degree : ℕ, ∑ mx ∈ Finset.range (degree + 1),
    (h ^ mx * k ^ (degree - mx) /
      ((Nat.factorial mx : ℝ) * (Nat.factorial (degree - mx) : ℝ))) *
      iterXY mx (degree - mx) f p

def xTaylorSeries (f : Point2 → ℝ) (p : Point2) (h : ℝ) : ℝ :=
  ∑' mx : ℕ,
    h ^ mx / (Nat.factorial mx : ℝ) * iterXY mx 0 f p

def yTaylorSeries (f : Point2 → ℝ) (p : Point2) (k : ℝ) : ℝ :=
  ∑' my : ℕ,
    k ^ my / (Nat.factorial my : ℝ) * iterXY 0 my f p

def rawTaylorCombination (f : Point2 → ℝ) (p : Point2) (h k : ℝ) : ℝ :=
  jointTaylorSeries f p h k - xTaylorSeries f p h -
    yTaylorSeries f p k + f p

def mixedTaylorSeries (f : Point2 → ℝ) (p : Point2) (h k : ℝ) : ℝ :=
  ∑' degree : ℕ, ∑ mx ∈ Finset.Icc 1 (degree - 1),
    (h ^ mx * k ^ (degree - mx) /
      ((Nat.factorial mx : ℝ) * (Nat.factorial (degree - mx) : ℝ))) *
      iterXY mx (degree - mx) f p

def mixedTailSeries (f : Point2 → ℝ) (p : Point2) (h k : ℝ) : ℝ :=
  ∑' degree : ℕ, if 3 ≤ degree then
    ∑ mx ∈ Finset.Icc 1 (degree - 1),
      (h ^ (mx - 1) * k ^ (degree - mx - 1) /
        ((Nat.factorial mx : ℝ) * (Nat.factorial (degree - mx) : ℝ))) *
        iterXY mx (degree - mx) f p
  else 0

theorem gap1 (f : Point2 → ℝ) (p : Point2)
    (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : Point2 in nhds (0, 0),
      mixedDifference f p q.1 q.2 =
        rawTaylorCombination f p q.1 q.2 := by
  simpa [mixedDifference, rawTaylorCombination, jointTaylorSeries,
    xTaylorSeries, yTaylorSeries,
    Exercise3591Support.jointSeries0, Exercise3591Support.jointTerm0,
    Exercise3591Support.xSeries0, Exercise3591Support.xTerm0,
    Exercise3591Support.ySeries0, Exercise3591Support.yTerm0,
    Exercise3591Support.iterXY0, iterXY] using
      Exercise3591Support.gap1_0 f p hf

theorem gap2 (f : Point2 → ℝ) (p : Point2)
    (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : Point2 in nhds (0, 0),
      mixedDifference f p q.1 q.2 =
        mixedTaylorSeries f p q.1 q.2 := by
  simpa [mixedDifference, mixedTaylorSeries,
    Exercise3591Support.mixedTerm0, Exercise3591Support.coeff0,
    Exercise3591Support.iterXY0, iterXY] using
      Exercise3591Support.gap2_0 f p hf

theorem gap3 (f : Point2 → ℝ) (p : Point2)
    (hf : AnalyticAt ℝ f p) :
    ∀ᶠ q : Point2 in nhds (0, 0),
      mixedDifference f p q.1 q.2 =
        q.1 * q.2 *
          (iterXY 1 1 f p + mixedTailSeries f p q.1 q.2) := by
  simpa [mixedDifference, mixedTailSeries,
    Exercise3591Support.tailTerm0, Exercise3591Support.iterXY0,
    iterXY] using
      Exercise3591Support.gap3_0 f p hf

end

end ProofGap.Exercise3591
