import probability.indep
open measure_theory probability_theory filter
open_locale big_operators measure_theory probability_theory topological_space

variables {α β γ : Type*} {mα : measurable_space α} {μ : measure α} [is_finite_measure μ]

namespace probability_theory

noncomputable def cov (X Y : Lp ℝ 2 μ) : ℝ := integral μ (X * Y) - integral μ X * integral μ Y

lemma indep_fun.cov_eq_zero {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  cov X Y = 0 :=
sub_eq_zero_of_eq h.integral_mul_of_Lp

noncomputable def var (X : Lp ℝ 2 μ) : ℝ := integral μ (X^2) - (integral μ X)^2

lemma indep_fun.var_add {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  var (X + Y) = var X + var Y :=
begin
  have hX : integrable X μ := Lp.integrable X,
  have hY : integrable Y μ := Lp.integrable Y,
  have h1 : integrable (X * X) μ := L2.integrable_mul X X,
  have h2 : integrable (X * Y) μ := L2.integrable_mul X Y,
  have h3 : integrable (Y * Y) μ := L2.integrable_mul Y Y,
  have h4 : ⇑(X + Y) =ᵐ[μ] X + Y := Lp.coe_fn_add X Y,
  have h5 : ⇑(X + Y) * ⇑(X + Y) =ᵐ[μ] (X + Y) * (X + Y) := h4.mul h4,

  simp_rw [var, pow_two, integral_congr_ae h4, integral_congr_ae h5, add_mul, mul_add,
    mul_comm (Y : α → ℝ) X, integral_add' (h1.add h2) (h2.add h3), integral_add' h1 h2,
    integral_add' h2 h3, integral_add' hX hY, h.integral_mul_of_integrable hX hY],
  ring
end

noncomputable def partial_avg (X : ℕ → α → ℝ) (n : ℕ) : α → ℝ :=
(∑ i in finset.range n, X i) / n

noncomputable def partial_avg' (X : ℕ → α → ℝ) (a : α) (n : ℕ) : ℝ :=
(∑ i : fin n, X i a) / n

lemma fin.sum.add (n : ℕ) (f g : ℕ → ℝ) :
  ∑ i : fin n, (f i + g i) = ∑ i : fin n, f i + ∑ i : fin n, g i :=
begin
  induction n,
  { simp },
  { simp [fin.sum_univ_cast_succ, n_ih], ring }
end

lemma fin.sum.sub (n : ℕ) (f g : ℕ → ℝ) :
  ∑ i : fin n, (f i - g i) = ∑ i : fin n, f i - ∑ i : fin n, g i :=
begin
  induction n,
  { simp },
  { simp [fin.sum_univ_cast_succ, n_ih], ring }
end

lemma integral_pos_add_neg {ν : measure ℝ} (h_int : integrable id ν) :
  let pos : ℝ → ℝ := λ (x : ℝ), max x 0,
      neg : ℝ → ℝ := λ (x : ℝ), max (-x) 0
  in integral ν id = integral (measure.map pos ν) id - integral (measure.map neg ν) id :=
begin
  intros pos neg,
  rw [integral_map, integral_map, ← integral_sub],
  { simpa only [id.def, max_zero_sub_max_neg_zero_eq_self] },
  { exact h_int.max_zero },
  { exact h_int.neg.max_zero },
  { exact (measurable_neg.max measurable_const).ae_measurable },
  { exact measurable_id.ae_strongly_measurable },
  { exact (measurable_id.max measurable_const).ae_measurable },
  { exact measurable_id.ae_strongly_measurable }
end

theorem lln_of_nonneg
  (X : ℕ → α → ℝ)
  (h_int : ∀ i, integrable (X i) μ)
  (h_dist : ∀ i, μ.map (X i) = μ.map (X 0))
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ))
  (h_pos : ∀ i, 0 ≤ᵐ[μ] X i)
  :
  ∀ᵐ a ∂μ, tendsto (partial_avg' X a) at_top (𝓝 (integral μ (X 0))) :=
sorry

lemma bla2
  {mβ : measurable_space β} {mγ : measurable_space γ}
  {X Y : α → β} {mX : measurable X} {mY : measurable Y}
  (φ : β → γ) {mφ : measurable φ}
  (h : μ.map X = μ.map Y) :
  μ.map (φ ∘ X) = μ.map (φ ∘ Y) :=
by rw [← measure.map_map mφ mX, ← measure.map_map mφ mY, h]

lemma bla1
  {X Y : α → ℝ} (hX : measurable X) (hY : measurable Y) (hXY : μ.map X = μ.map Y) :
  (μ.map (X ⊔ 0) = μ.map (Y ⊔ 0)) :=
begin
  have : X ⊔ 0 = (⊔ 0) ∘ X := by refl, rw this,
  apply bla2; measurability
end

theorem lln
  (X : ℕ → α → ℝ)
  (h_int : ∀ i, integrable (X i) μ)
  (h_dist' : ∀ i, μ.map (X i) = μ.map (X 0))
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ)) :
  ∀ᵐ a ∂μ, tendsto (partial_avg' X a) at_top (𝓝 (integral μ (X 0))) :=
begin
  let neg : ℝ → ℝ := λ x, max (-x) 0,
  let Xp := X ⊔ 0,
  let Xm := -X ⊔ 0,

  have h1 : ∀ i, μ.map (X i ⊔ 0) = μ.map (X 0 ⊔ 0) := λ i, bla1 (h_int i) (h_int 0) (h_dist' i),
  have h3 : measurable (⊔ (0 : real)) := measurable_id.max measurable_const,
  have h4 : ∀ i, μ.map (- X i ⊔ 0) = μ.map (- X 0 ⊔ 0) := sorry,
  have h5 : measurable ((⊔ (0 : real)) ∘ neg) := sorry,
  have h6 : ∀ i, Xm i = ((⊔ 0) ∘ neg) ∘ X i := sorry,
  have h7 : ∀ x : ℝ, x ⊔ 0 - (-x) ⊔ 0 = x := sorry,

  have Hp : ∀ᵐ a ∂μ, tendsto (partial_avg' Xp a) at_top (𝓝 (integral μ (Xp 0))),
  { apply lln_of_nonneg,
    { exact λ i, (h_int i).max_zero },
    { simp only [Xp, h1, pi.sup_apply, pi.zero_apply, forall_const] },
    { exact λ i j hij, by apply indep_fun.comp (h_indep i j hij) h3 h3 },
    { exact λ i, ae_of_all _ (by simp [Xp]) } },

  have Hn : ∀ᵐ a ∂μ, tendsto (partial_avg' Xm a) at_top (𝓝 (integral μ (Xm 0))),
  { apply lln_of_nonneg,
    { exact λ i, (h_int i).neg.max_zero },
    { simp only [Xm, h4, pi.sup_apply, pi.neg_apply, pi.zero_apply, forall_const] },
    { intros i j hij,
      rw [h6, h6],
      apply indep_fun.comp (h_indep i j hij) h5 h5 },
    { exact λ i, ae_of_all _ (by simp [Xm]) } },

  apply (Hp.and Hn).mono,
  rintro a ⟨c1, c2⟩,
  convert c1.sub c2,
  { funext n,
    simp only [partial_avg', Xp, Xm],
    rw [← sub_div, ← @fin.sum.sub n (λ n, Xp n a) (λ n, Xm n a)],
    simp only [Xp, Xm, h7, pi.sup_apply, pi.zero_apply, pi.neg_apply] },
  { rw ← integral_sub,
    { simp [h7] },
    { exact (h_int 0).max_zero },
    { exact (h_int 0).neg.max_zero } }
end

end probability_theory
