import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise1237

noncomputable section

open Filter

def StationaryOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ c ∈ s, deriv f c = 0

def tanMap (t : ℝ) : ℝ := Real.tan t
def rightMap (a b₀ t : ℝ) : ℝ := (b₀ - a) * t / (b₀ - t)

theorem gap1 (f F : ℝ → ℝ) (a b A : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hleft : Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds A))
    (hright : Tendsto f (nhdsWithin b (Set.Iio b)) (nhds A))
    (hF : ∀ x ∈ Set.Ioo a b, F x = f x) (hFa : F a = A) (hFb : F b = A) :
    ContinuousOn F (Set.Icc a b) := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    have hb_event : ∀ᶠ y in nhdsWithin a (Set.Ioi a), y < b :=
      Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hab)
    have heq : F =ᶠ[nhdsWithin a (Set.Ioi a)] f := by
      filter_upwards [self_mem_nhdsWithin, hb_event] with y hay hyb
      exact hF y ⟨hay, hyb⟩
    have hside : ContinuousWithinAt F (Set.Ioi a) a := by
      change Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds (F a))
      rw [hFa]
      exact hleft.congr' heq.symm
    have hsing : ContinuousWithinAt F ({a} : Set ℝ) a :=
      continuousWithinAt_singleton
    have hwhole : ContinuousWithinAt F (({a} : Set ℝ) ∪ Set.Ioi a) a :=
      hsing.union hside
    have hset : ({a} : Set ℝ) ∪ Set.Ioi a = Set.Ici a := by
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro hy
        rcases hy with hy | hy
        · subst y
          exact le_rfl
        · exact le_of_lt hy
      · intro hy
        rcases lt_or_eq_of_le hy with hy | hy
        · exact Or.inr hy
        · exact Or.inl hy.symm
    rw [hset] at hwhole
    exact hwhole.mono fun y hy => hy.1
  · by_cases hxb : x = b
    · subst x
      have ha_event : ∀ᶠ y in nhdsWithin b (Set.Iio b), a < y :=
        Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds hab)
      have heq : F =ᶠ[nhdsWithin b (Set.Iio b)] f := by
        filter_upwards [self_mem_nhdsWithin, ha_event] with y hyb hay
        exact hF y ⟨hay, hyb⟩
      have hside : ContinuousWithinAt F (Set.Iio b) b := by
        change Tendsto F (nhdsWithin b (Set.Iio b)) (nhds (F b))
        rw [hFb]
        exact hright.congr' heq.symm
      have hsing : ContinuousWithinAt F ({b} : Set ℝ) b :=
        continuousWithinAt_singleton
      have hwhole : ContinuousWithinAt F (({b} : Set ℝ) ∪ Set.Iio b) b :=
        hsing.union hside
      have hset : ({b} : Set ℝ) ∪ Set.Iio b = Set.Iic b := by
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Iio, Set.mem_Iic]
        constructor
        · intro hy
          rcases hy with hy | hy
          · subst y
            exact le_rfl
          · exact le_of_lt hy
        · intro hy
          rcases lt_or_eq_of_le hy with hy | hy
          · exact Or.inr hy
          · exact Or.inl hy
      rw [hset] at hwhole
      exact hwhole.mono fun y hy => hy.2
    · have hxi : x ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
      have hfx : ContinuousAt f x :=
        ((hf x hxi).differentiableAt (Ioo_mem_nhds hxi.1 hxi.2)).continuousAt
      have heq : F =ᶠ[nhds x] f := by
        filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
        exact hF y hy
      have ht : Tendsto F (nhds x) (nhds (f x)) := hfx.congr' heq.symm
      change Tendsto F (nhdsWithin x (Set.Icc a b)) (nhds (F x))
      rw [hF x hxi]
      exact ht.mono_left inf_le_left

theorem gap2 (f F : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hF : ∀ x ∈ Set.Ioo a b, F x = f x) :
    DifferentiableOn ℝ F (Set.Ioo a b) := by
  intro x hx
  have hfx : DifferentiableAt ℝ f x :=
    (hf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have heq : F =ᶠ[nhds x] f := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hF y hy
  exact (hfx.congr_of_eventuallyEq heq).differentiableWithinAt

theorem gap3 (F : ℝ → ℝ) (a b A : ℝ) (hFa : F a = A) (hFb : F b = A) :
    F a = F b := by
  calc
    F a = A := hFa
    _ = F b := hFb.symm

theorem gap4 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ F (Set.Ioo a b)) (heq : F a = F b) :
    StationaryOn F (Set.Ioo a b) := by
  rcases exists_deriv_eq_slope F hab hcont hdiff with ⟨c, hc, hderiv⟩
  refine ⟨c, hc, ?_⟩
  rw [hderiv, heq]
  simp

theorem gap5 (f F : ℝ → ℝ) (a b x : ℝ) (hx : x ∈ Set.Ioo a b)
    (hF : ∀ z ∈ Set.Ioo a b, F z = f z) :
    deriv F x = deriv f x := by
  have heq : F =ᶠ[nhds x] f := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hF y hy
  exact heq.deriv_eq

theorem gap6 (f F : ℝ → ℝ) (a b : ℝ)
    (hstat : StationaryOn F (Set.Ioo a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, deriv F x = deriv f x) :
    StationaryOn f (Set.Ioo a b) := by
  rcases hstat with ⟨c, hc, hzero⟩
  refine ⟨c, hc, ?_⟩
  rw [← hderiv c hc]
  exact hzero

theorem gap7 (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hlim : ∃ L, Tendsto f atBot (nhds L) ∧ Tendsto f atTop (nhds L)) :
    StationaryOn (fun t => f (tanMap t))
      (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
  rcases hlim with ⟨L, hbot, htop⟩
  have hab : -Real.pi / 2 < Real.pi / 2 := by
    linarith [Real.pi_pos]
  have htan_left :
      Tendsto tanMap (nhdsWithin (-Real.pi / 2) (Set.Ioi (-Real.pi / 2))) atBot := by
    simpa [tanMap, neg_div] using Real.tendsto_tan_neg_pi_div_two
  have htan_right :
      Tendsto tanMap (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) atTop := by
    simpa [tanMap] using Real.tendsto_tan_pi_div_two
  have hleft : Tendsto (fun t => f (tanMap t))
      (nhdsWithin (-Real.pi / 2) (Set.Ioi (-Real.pi / 2))) (nhds L) :=
    hbot.comp htan_left
  have hright : Tendsto (fun t => f (tanMap t))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) :=
    htop.comp htan_right
  have hdiff : DifferentiableOn ℝ (fun t => f (tanMap t))
      (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    intro t ht
    have hcpos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using ht)
    have htan : DifferentiableAt ℝ tanMap t := by
      simpa [tanMap] using (Real.hasDerivAt_tan hcpos.ne').differentiableAt
    exact ((hf (tanMap t)).comp t htan).differentiableWithinAt
  let F : ℝ → ℝ := fun t =>
    if t = -Real.pi / 2 then L
    else if t = Real.pi / 2 then L
    else f (tanMap t)
  have hF : ∀ t ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
      F t = f (tanMap t) := by
    intro t ht
    simp [F, ne_of_gt ht.1, ne_of_lt ht.2]
  have hFa : F (-Real.pi / 2) = L := by simp [F]
  have hFb : F (Real.pi / 2) = L := by
    simp [F, ne_of_gt hab]
  have hcont := gap1 (fun t => f (tanMap t)) F
    (-Real.pi / 2) (Real.pi / 2) L hab hdiff hleft hright hF hFa hFb
  have hdiffF := gap2 (fun t => f (tanMap t)) F
    (-Real.pi / 2) (Real.pi / 2) hdiff hF
  have heq := gap3 F (-Real.pi / 2) (Real.pi / 2) L hFa hFb
  have hstat := gap4 F (-Real.pi / 2) (Real.pi / 2) hab hcont hdiffF heq
  exact gap6 (fun t => f (tanMap t)) F (-Real.pi / 2) (Real.pi / 2)
    hstat (fun x hx => gap5 (fun t => f (tanMap t)) F
      (-Real.pi / 2) (Real.pi / 2) x hx hF)

theorem gap8 (f : ℝ → ℝ) (t₀ : ℝ)
    (ht : t₀ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (hf : DifferentiableAt ℝ f (tanMap t₀)) :
    deriv (fun t => f (tanMap t)) t₀ =
      deriv f (tanMap t₀) * (1 / Real.cos t₀) ^ 2 := by
  have hcpos : 0 < Real.cos t₀ :=
    Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using ht)
  have hchain :=
    (hf.hasDerivAt.comp t₀ (Real.hasDerivAt_tan hcpos.ne')).deriv
  simpa [tanMap, div_pow] using hchain

theorem gap9 (f : ℝ → ℝ) (t₀ : ℝ)
    (hzero : deriv (fun t => f (tanMap t)) t₀ = 0)
    (hchain : deriv (fun t => f (tanMap t)) t₀ =
      deriv f (tanMap t₀) * (1 / Real.cos t₀) ^ 2) :
    deriv f (tanMap t₀) * (1 / Real.cos t₀) ^ 2 = 0 := by
  calc
    deriv f (tanMap t₀) * (1 / Real.cos t₀) ^ 2 =
        deriv (fun t => f (tanMap t)) t₀ := hchain.symm
    _ = 0 := hzero

theorem gap10 (f : ℝ → ℝ) (t₀ : ℝ)
    (hzero : deriv (fun t => f (tanMap t)) t₀ = 0) :
    deriv (fun t => f (tanMap t)) t₀ = 0 := by
  exact hzero

theorem gap11 (t₀ : ℝ)
    (ht : t₀ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
    (1 / Real.cos t₀) ^ 2 ≠ 0 := by
  have hcpos : 0 < Real.cos t₀ :=
    Real.cos_pos_of_mem_Ioo (by simpa [neg_div] using ht)
  exact pow_ne_zero 2 (one_div_ne_zero hcpos.ne')

theorem gap12 (f : ℝ → ℝ) (t₀ : ℝ)
    (ht : t₀ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (hprod : deriv f (tanMap t₀) * (1 / Real.cos t₀) ^ 2 = 0) :
    deriv f (tanMap t₀) = 0 := by
  exact (mul_eq_zero.mp hprod).resolve_right (gap11 t₀ ht)

theorem gap13 (f : ℝ → ℝ) (a b₀ : ℝ)
    (hb : b₀ > max a 0)
    (hstat : StationaryOn (fun t => f (rightMap a b₀ t)) (Set.Ioo a b₀)) :
    ∃ t₀ ∈ Set.Ioo a b₀,
      deriv (fun t => f (rightMap a b₀ t)) t₀ = 0 := by
  exact hstat

theorem gap14 (f : ℝ → ℝ) (a b₀ t₀ : ℝ)
    (hb : b₀ > max a 0) (ht : t₀ ∈ Set.Ioo a b₀)
    (hf : DifferentiableAt ℝ f (rightMap a b₀ t₀)) :
    deriv (fun t => f (rightMap a b₀ t)) t₀ =
      deriv f (rightMap a b₀ t₀) *
        (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) := by
  have hden : b₀ - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  have hnum : HasDerivAt (fun t : ℝ => (b₀ - a) * t) (b₀ - a) t₀ := by
    simpa using (hasDerivAt_id t₀).const_mul (b₀ - a)
  have hdenom : HasDerivAt (fun t : ℝ => b₀ - t) (-1) t₀ := by
    simpa using (hasDerivAt_const t₀ b₀).sub (hasDerivAt_id t₀)
  have hraw : HasDerivAt (fun t : ℝ => (b₀ - a) * t / (b₀ - t))
      (((b₀ - a) * (b₀ - t₀) - ((b₀ - a) * t₀) * (-1)) /
        (b₀ - t₀) ^ 2) t₀ :=
    hnum.div hdenom hden
  have hinner : HasDerivAt (rightMap a b₀)
      (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) t₀ := by
    change HasDerivAt (fun t : ℝ => (b₀ - a) * t / (b₀ - t))
      (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) t₀
    exact hraw.congr_deriv (by ring)
  exact (hf.hasDerivAt.comp t₀ hinner).deriv

theorem gap15 (f : ℝ → ℝ) (a b₀ t₀ : ℝ)
    (hzero : deriv (fun t => f (rightMap a b₀ t)) t₀ = 0)
    (hchain : deriv (fun t => f (rightMap a b₀ t)) t₀ =
      deriv f (rightMap a b₀ t₀) *
        (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2)) :
    deriv f (rightMap a b₀ t₀) *
      (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) = 0 := by
  calc
    deriv f (rightMap a b₀ t₀) *
        (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) =
        deriv (fun t => f (rightMap a b₀ t)) t₀ := hchain.symm
    _ = 0 := hzero

theorem gap16 (f : ℝ → ℝ) (a b₀ t₀ : ℝ)
    (hzero : deriv (fun t => f (rightMap a b₀ t)) t₀ = 0) :
    deriv (fun t => f (rightMap a b₀ t)) t₀ = 0 := by
  exact hzero

theorem gap17 (a b₀ t₀ : ℝ) (hb : b₀ > max a 0)
    (ht : t₀ ∈ Set.Ioo a b₀) :
    b₀ * (b₀ - a) / (b₀ - t₀) ^ 2 > 0 := by
  have hbpos : 0 < b₀ :=
    lt_of_le_of_lt (le_max_right a 0) hb
  have hbapos : 0 < b₀ - a :=
    sub_pos.mpr (lt_of_le_of_lt (le_max_left a 0) hb)
  have hdenpos : 0 < (b₀ - t₀) ^ 2 :=
    pow_pos (sub_pos.mpr ht.2) 2
  exact div_pos (mul_pos hbpos hbapos) hdenpos

theorem gap18 (f : ℝ → ℝ) (a b₀ t₀ : ℝ)
    (hb : b₀ > max a 0) (ht : t₀ ∈ Set.Ioo a b₀)
    (hprod : deriv f (rightMap a b₀ t₀) *
      (b₀ * (b₀ - a) / (b₀ - t₀) ^ 2) = 0) :
    deriv f (rightMap a b₀ t₀) = 0 := by
  have hfactor : b₀ * (b₀ - a) / (b₀ - t₀) ^ 2 ≠ 0 :=
    ne_of_gt (gap17 a b₀ t₀ hb ht)
  exact (mul_eq_zero.mp hprod).resolve_right hfactor

theorem gap19 (f : ℝ → ℝ) (b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Iio b))
    (hlim : ∃ L, Tendsto f atBot (nhds L) ∧
      Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L)) :
    StationaryOn f (Set.Iio b) := by
  rcases hlim with ⟨L, hbot, hbnd⟩
  let g : ℝ → ℝ := fun t => f (b - Real.exp t)
  have harg_bot : Tendsto (fun t : ℝ => b - Real.exp t) atBot
      (nhdsWithin b (Set.Iio b)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => b) atBot (nhds b)).sub
          Real.tendsto_exp_atBot)
    · exact Filter.Eventually.of_forall fun t =>
        sub_lt_self b (Real.exp_pos t)
  have harg_top : Tendsto (fun t : ℝ => b - Real.exp t) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro c
    filter_upwards [Real.tendsto_exp_atTop.eventually
      (eventually_ge_atTop (b - c))] with t ht
    linarith
  have hg_bot : Tendsto g atBot (nhds L) := by
    exact hbnd.comp harg_bot
  have hg_top : Tendsto g atTop (nhds L) := by
    exact hbot.comp harg_top
  have hgdiff : Differentiable ℝ g := by
    intro t
    have harg : b - Real.exp t ∈ Set.Iio b :=
      sub_lt_self b (Real.exp_pos t)
    have hfat : DifferentiableAt ℝ f (b - Real.exp t) :=
      (hf _ harg).differentiableAt (Iio_mem_nhds harg)
    have hinner : DifferentiableAt ℝ (fun x : ℝ => b - Real.exp x) t :=
      ((hasDerivAt_const t b).sub (Real.hasDerivAt_exp t)).differentiableAt
    simpa [g] using hfat.comp t hinner
  rcases gap7 g hgdiff ⟨L, hg_bot, hg_top⟩ with ⟨s, hs, hzero⟩
  have hgchain := gap8 g s hs (hgdiff (tanMap s))
  have hgprod := gap9 g s hzero hgchain
  have hgzero : deriv g (tanMap s) = 0 := gap12 g s hs hgprod
  have harg : b - Real.exp (tanMap s) ∈ Set.Iio b :=
    sub_lt_self b (Real.exp_pos (tanMap s))
  have hfat : DifferentiableAt ℝ f (b - Real.exp (tanMap s)) :=
    (hf _ harg).differentiableAt (Iio_mem_nhds harg)
  have hinner : HasDerivAt (fun x : ℝ => b - Real.exp x)
      (-Real.exp (tanMap s)) (tanMap s) := by
    simpa using
      (hasDerivAt_const (tanMap s) b).sub (Real.hasDerivAt_exp (tanMap s))
  have hchain : deriv g (tanMap s) =
      deriv f (b - Real.exp (tanMap s)) * (-Real.exp (tanMap s)) := by
    simpa [g] using (hfat.hasDerivAt.comp (tanMap s) hinner).deriv
  have hprod : deriv f (b - Real.exp (tanMap s)) *
      (-Real.exp (tanMap s)) = 0 := by
    rw [← hchain]
    exact hgzero
  have hfzero : deriv f (b - Real.exp (tanMap s)) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right
      (neg_ne_zero.mpr (Real.exp_ne_zero (tanMap s)))
  exact ⟨b - Real.exp (tanMap s), harg, hfzero⟩

theorem gap20 (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hlim : ∃ L, Tendsto f atBot (nhds L) ∧ Tendsto f atTop (nhds L)) :
    ∃ c : ℝ, deriv f c = 0 := by
  rcases gap7 f hf hlim with ⟨t₀, ht, hzero⟩
  have hchain := gap8 f t₀ ht (hf (tanMap t₀))
  have hprod := gap9 f t₀ hzero hchain
  have hfzero := gap12 f t₀ ht hprod
  exact ⟨tanMap t₀, hfzero⟩

end

end ProofGap.Exercise1237
