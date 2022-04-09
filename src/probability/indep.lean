import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α β β' γ γ' : Type*} {mα : measurable_space α} {μ : measure α}

lemma set.indicator_inter {s t : set α} :
  (s ∩ t).indicator (1 : α → ℝ) = s.indicator 1 * t.indicator 1 :=
begin
  classical,
  ext,
  simp only [set.indicator, pi.one_apply, pi.mul_apply, boole_mul],
  convert ite_and (x ∈ s) (x ∈ t) (1 : ℝ) (0 : ℝ),
end

namespace probability_theory

theorem indep_fun_iff_integral_comp_mul [is_finite_measure μ] {f : α → β} {g : α → β'}
  {mβ : measurable_space β} {mβ' : measurable_space β'} {hfm : measurable f} {hgm : measurable g} :
  indep_fun f g μ ↔
  ∀ {φ : β → ℝ} {ψ : β' → ℝ},
    measurable φ → measurable ψ → integrable (φ ∘ f) μ → integrable (ψ ∘ g) μ →
    integral μ ((φ ∘ f) * (ψ ∘ g)) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) :=
begin
  have I : ∀ {A : set α} (hA : measurable_set A), integral μ (A.indicator 1) = (μ A).to_real,
    from λ _ hA, (integral_indicator_const (1 : ℝ) hA).trans ((smul_eq_mul _).trans (mul_one _)),
  refine ⟨λ hfg _ _ hφ hψ, indep_fun.integral_mul_of_integrable (hfg.comp hφ hψ), _⟩,
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  specialize h (measurable_one.indicator hA) (measurable_one.indicator hB)
    ((integrable_const 1).indicator (hfm.comp measurable_id hA))
    ((integrable_const 1).indicator (hgm.comp measurable_id hB)),
  rwa [← ennreal.to_real_eq_to_real (measure_ne_top μ _), ← I ((hfm hA).inter (hgm hB)),
    set.indicator_inter, ennreal.to_real_mul, ← I (hfm hA), ← I (hgm hB)],
  exact ennreal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)
end

end probability_theory

namespace measure_theory

lemma ae_strongly_measurable.mono {m1 m2 : measurable_space α} {μ : measure α} (hm : m1 ≤ m2)
  {f : α → ℝ} :
  ae_strongly_measurable f (μ.trim hm) → ae_strongly_measurable f μ :=
by { rintro ⟨ff, h1, h2⟩, exact ⟨ff, h1.mono hm, ae_eq_of_ae_eq_trim h2⟩ }

noncomputable def Lp_trim_to_Lp {m1 m2 : measurable_space α} {μ : measure α} (hm : m1 ≤ m2) :
  Lp ℝ 1 (μ.trim hm) → Lp ℝ 1 μ :=
λ f, (mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f

lemma Lp_trim_to_Lp.ae_eq {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} : Lp_trim_to_Lp hm f =ᵐ[μ] f :=
by simp only [Lp_trim_to_Lp, mem_ℒp.coe_fn_to_Lp]

lemma Lp_trim_to_Lp.continuous {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  continuous (@Lp_trim_to_Lp α m1 m2 μ hm) :=
begin
  rw metric.continuous_iff,
  rintro f ε hε,
  use ε,
  use hε,
  rintro g,
  suffices : dist (Lp_trim_to_Lp hm g) (Lp_trim_to_Lp hm f) = dist g f, rw this, exact id,
  simp_rw Lp.dist_def,
  simp only [snorm, snorm', one_ne_zero, ennreal.one_ne_top, ennreal.one_to_real, pi.sub_apply,
    ennreal.rpow_one, div_one, if_false],
  refine congr_arg ennreal.to_real _,
  rw lintegral_trim_ae,
  { apply lintegral_congr_ae,
    apply filter.eventually_eq.fun_comp,
    apply filter.eventually_eq.fun_comp,
    apply filter.eventually_eq.sub;
    exact Lp_trim_to_Lp.ae_eq },
  { apply measurable.comp_ae_measurable,
    exact measurable_coe_nnreal_ennreal,
    apply measurable.comp_ae_measurable,
    exact measurable_nnnorm,
    apply ae_measurable.sub;
    { apply ae_strongly_measurable.ae_measurable, apply Lp.ae_strongly_measurable } }
end

lemma continuous_integral_trim {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα} :
  continuous (λ (f : Lp ℝ 1 (μ.trim hm)), integral μ f) :=
begin
  convert continuous_integral,
  exact funext (λ f, integral_trim_ae hm (Lp.ae_strongly_measurable f))
end

example {P Q : Prop} : P → Q → P := by { exact imp_intro}

lemma continuous_integral_trim_restrict {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα}
  {S : set α} (hS : mα.measurable_set' S) :
  continuous (λ f : Lp ℝ 1 (μ.trim hm), ∫ a in S, f a ∂μ) :=
begin
  let Ψ := λ f : Lp ℝ 1 μ, ∫ a in S, f a ∂μ,
  have h : ∀ {f}, Ψ (Lp_trim_to_Lp hm f) = ∫ a in S, f a ∂μ :=
    by { intro f,
      apply set_integral_congr_ae hS,
      apply Lp_trim_to_Lp.ae_eq.mono,
      exact λ _, imp_intro },
  simp_rw ← h,
  exact (continuous_set_integral S).comp Lp_trim_to_Lp.continuous,
end

example
  {α : Type*} {mα' : measurable_space α} {mα : measurable_space α} {μ : measure α}
  [is_finite_measure μ]
  {hm : mα' ≤ mα}
  {S : set α} {hS1 : mα.measurable_set' S} {hS : indep_sets mα'.measurable_set' {S} μ}
  {f : α → ℝ} {hf : integrable f (μ.trim hm)}
  :
  ∫ a in S, f a ∂μ = (μ S).to_real • ∫ a, f a ∂μ :=
begin
  revert f, apply integrable.induction,
  { rintro c s hs1 -,
    have hs' := hm _ hs1,
    have h1 : (μ.restrict S) s ≠ ⊤ := by { rw [measure.restrict_apply hs'], apply measure_ne_top },
    rw ← integral_congr_ae (@indicator_const_Lp_coe_fn α ℝ mα 1 μ _ s hs' (measure_ne_top _ _) c),
    rw ← integral_congr_ae (@indicator_const_Lp_coe_fn α ℝ mα 1 (μ.restrict S) _ s hs' h1 c),
    rw [integral_indicator_const_Lp, integral_indicator_const_Lp, measure.restrict_apply hs'],
    rw [hS s S hs1 (set.mem_singleton _), ennreal.to_real_mul],
    simp only [algebra.id.smul_eq_mul],
    ring },
  { rintro f g - hf hg h1 h2,
    have hf' : integrable f μ := integrable_of_integrable_trim hm hf,
    have hg' : integrable g μ := integrable_of_integrable_trim hm hg,
    rw [integral_add', integral_add' hf' hg', h1, h2, smul_add],
    { exact integrable_on_univ.mp ((integrable_on_univ.mpr hf').restrict measurable_set.univ) },
    { exact integrable_on_univ.mp ((integrable_on_univ.mpr hg').restrict measurable_set.univ) } },
  {
    simp,
    simp_rw ← @sub_eq_zero ℝ _ (integral _ _) _,
    simp_rw ← set.mem_singleton_iff,
    apply is_closed.preimage,
    apply continuous.sub,
    { exact continuous_integral_trim_restrict hS1 },
    { refine continuous_const.mul _,
      exact continuous_integral_trim },
    { exact t1_space.t1 0 }
  },
  { rintro f g hfg - h,
    have h1 : f =ᵐ[μ] g := ae_eq_of_ae_eq_trim hfg,
    have h2 : f =ᵐ[μ.restrict S] g := filter.eventually_eq.restrict h1,
    rwa [← integral_congr_ae h1, ← integral_congr_ae h2] }
end

end measure_theory
