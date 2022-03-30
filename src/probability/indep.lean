import probability.independence
import probability.integration
import probability.notation

open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory
noncomputable theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

namespace probability_theory

lemma indep_fun_comp_of_indep_fun {α α' β β' : Type*}
  [measurable_space α] [measurable_space α'] [measurable_space β] [measurable_space β']
  {f : Ω → α} {g : Ω → α'} (hfg : indep_fun f g)
  {φ : α → β} {ψ : α' → β'} {hφ : measurable φ} {hψ : measurable ψ} :
indep_fun (φ ∘ f) (ψ ∘ g) :=
begin
  rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩, apply hfg,
  exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩,
  exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
end

lemma integrable_mul_of_integrable_of_indep_fun {X Y : Ω → ℝ} {h : indep_fun X Y}
  {hXm : measurable X} {hXi : integrable X} {hYm : measurable Y} {hYi : integrable Y} :
integrable (X * Y) :=
begin
  have hXpm : measurable (λ a, ∥X a∥₊ : Ω → ennreal) := hXm.nnnorm.coe_nnreal_ennreal,
  have hYpm : measurable (λ a, ∥Y a∥₊ : Ω → ennreal) := hYm.nnnorm.coe_nnreal_ennreal,

  refine ⟨hXi.1.mul hYi.1, _⟩,
  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul],
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun hXpm hYpm _,
  simp only [pi.mul_apply] at this, rw this, clear this,
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hXi.2, hYi.2⟩),
  apply indep_fun_comp_of_indep_fun; try { exact measurable_coe_nnreal_ennreal },
  apply indep_fun_comp_of_indep_fun h; exact measurable_nnnorm
end

-- TODO: should work on `ae_measurable`
lemma integral_indep_of_pos {X Y : Ω → ℝ} {hXYind : indep_fun X Y}
  {hXpos : 0 ≤ X} {hXmes : measurable X} {hYpos : 0 ≤ Y} {hYmes : measurable Y}:
  𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  rw [@integral_eq_lintegral_of_nonneg_ae _ _ _ (X * Y)
      (filter.eventually_of_forall (λ ω, mul_nonneg (hXpos ω) (hYpos ω)))
      (hXmes.mul hYmes).ae_measurable,
    integral_eq_lintegral_of_nonneg_ae (filter.eventually_of_forall hXpos) hXmes.ae_measurable,
    integral_eq_lintegral_of_nonneg_ae (filter.eventually_of_forall hYpos) hYmes.ae_measurable],
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXpos _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
    hXmes.ennreal_of_real hYmes.ennreal_of_real (indep_fun_comp_of_indep_fun hXYind);
  exact ennreal.measurable_of_real
end

example {X : Ω → ℝ} : measurable X → measurable (X⁺) :=
λ h, measurable.sup_const h 0

lemma integral_indep {X Y : Ω → ℝ} {h : indep_fun X Y}
  {hXm : measurable X} {hX : integrable X} {hYm : measurable Y} {hY : integrable Y} :
𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  set Xp := (λ x : ℝ, max x 0) ∘ X, -- `X⁺` would be better but it makes `simp_rw` fail
  set Xm := (λ x : ℝ, max (-x) 0) ∘ X,
  set Yp := (λ x : ℝ, max x 0) ∘ Y,
  set Ym := (λ x : ℝ, max (-x) 0) ∘ Y,

  have hXpm : X = Xp - Xm := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (X ω)).symm),
  have hYpm : Y = Yp - Ym := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm),

  have hp1 : 0 ≤ Xm := λ ω, le_max_right _ _,
  have hp2 : 0 ≤ Xp := λ ω, le_max_right _ _,
  have hp3 : 0 ≤ Ym := λ ω, le_max_right _ _,
  have hp4 : 0 ≤ Yp := λ ω, le_max_right _ _,

  have hm1 : measurable Xm := hXm.neg.max measurable_const,
  have hm2 : measurable Xp := hXm.max measurable_const,
  have hm3 : measurable Ym := hYm.neg.max measurable_const,
  have hm4 : measurable Yp := hYm.max measurable_const,

  have hv1 : integrable Xm := hX.neg.max_zero,
  have hv1 : integrable Xp := hX.max_zero,
  have hv1 : integrable Ym := hY.neg.max_zero,
  have hv1 : integrable Yp := hY.max_zero,

  have hi1 : indep_fun Xm Ym := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi2 : indep_fun Xp Ym := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi3 : indep_fun Xm Yp := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi4 : indep_fun Xp Yp := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },

  have hl1 : integrable (Xm * Ym) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl2 : integrable (Xp * Ym) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl3 : integrable (Xm * Yp) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl4 : integrable (Xp * Yp) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },

  have hl5 : integrable (Xp * Yp - Xm * Yp) := by { apply integrable.sub; assumption },
  have hl5 : integrable (Xp * Ym - Xm * Ym) := by { apply integrable.sub; assumption },

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  repeat { rw [integral_sub'] },
  repeat { rw [integral_indep_of_pos] },
  ring,
  assumption'
end

end probability_theory
