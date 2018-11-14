import data.polynomial ring_theory.associated

open finset

namespace polynomial

variables {α : Type*} [decidable_eq α]

theorem degree_add_eq_of_degree_gt [comm_semiring α]
  {f g : polynomial α} (H : degree g < degree f) :
  degree (f + g) = degree f :=
add_comm g f ▸ degree_add_eq_of_degree_lt H

theorem degree_sub_eq_of_degree_gt [comm_ring α]
  {f g : polynomial α} (H : degree g < degree f) :
  degree (f - g) = degree f :=
degree_add_eq_of_degree_gt ((degree_neg g).symm ▸ H)

theorem leading_coeff_add_of_degree_gt [comm_semiring α]
  {f g : polynomial α} (H : degree g < degree f) :
  leading_coeff (f + g) = leading_coeff f :=
add_comm g f ▸ leading_coeff_add_of_degree_lt H

theorem leading_coeff_sub_of_degree_gt [comm_ring α]
  {f g : polynomial α} (H : degree g < degree f) :
  leading_coeff (f - g) = leading_coeff f :=
leading_coeff_add_of_degree_gt ((degree_neg g).symm ▸ H)

theorem leading_coeff_X_sub_C [comm_ring α] {r : α} :
  leading_coeff (X - C r) = 1 :=
begin
  by_cases h : (0:α) = 1,
  { haveI := subsingleton_of_zero_eq_one _ h,
    apply subsingleton.elim, },
  letI : nonzero_comm_ring α := { zero_ne_one := h, .. (infer_instance : comm_ring α)},
  rw [leading_coeff_sub_of_degree_gt, leading_coeff_X],
  apply lt_of_le_of_lt degree_C_le,
  rw degree_X, exact dec_trivial
end

theorem leading_coeff_neg [comm_ring α] {p : polynomial α} :
  leading_coeff (-p) = -leading_coeff p :=
by simp only [leading_coeff, nat_degree, degree_neg, coeff_neg]

section
variables [comm_semiring α] {ι : Type*} [decidable_eq ι] {f : ι → polynomial α} {s : finset ι}

theorem eval_prod {x : α} : eval x (s.prod f) = s.prod (λ i, eval x (f i)) :=
eq.symm $ prod_hom (eval x) eval_one (λ _ _, eval_mul)
end

section
variables [integral_domain α] {ι : Type*} [decidable_eq ι] {f : ι → polynomial α} {s : finset ι}

theorem degree_prod : degree (s.prod f) = s.sum (λ i, degree (f i)) :=
finset.induction_on s (by rw [prod_empty, degree_one, sum_empty]) $ λ a s has ih,
by rw [prod_insert has, degree_mul_eq, ih, sum_insert has]

theorem leading_coeff_prod : leading_coeff (s.prod f) = s.prod (λ i, leading_coeff (f i)) :=
eq.symm $ prod_hom leading_coeff leading_coeff_one leading_coeff_mul
end

end polynomial

namespace int

theorem mul_eq_neg_one {p q : ℤ} : p * q = -1 ↔ p = 1 ∧ q = -1 ∨ p = -1 ∧ q = 1 :=
begin
  split,
  { intro hpq,
    have : p.nat_abs ∣ 1,
    { existsi q.nat_abs, rw [← nat_abs_mul, hpq], refl },
    rw nat.dvd_one at this,
    replace this := congr_arg (coe : ℕ → ℤ) this,
    cases le_total p 0 with hp hp,
    { rw [of_nat_nat_abs_of_nonpos hp, neg_eq_iff_neg_eq] at this, subst p,
      rw [int.coe_nat_one, neg_one_mul, neg_inj'] at hpq, subst q,
      right, split; refl },
    { rw [nat_abs_of_nonneg hp] at this, subst p,
      rw [int.coe_nat_one, one_mul] at hpq, subst q,
      left, split; refl } },
  { rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); refl }
end

end int

@[simp] lemma with_bot.nat_cast (n : ℕ) : @eq (with_bot ℕ) (@coe _ _ (@coe_to_lift _ _ (@coe_base _ _ nat.cast_coe)) n) n :=
nat.rec_on n rfl (λ n (ih : nat.cast _ = _), show _ + _ = _, by rw ih; refl)

@[simp] lemma with_bot_zero : (0 : with_bot ℕ) = (0:ℕ) := rfl
@[simp] lemma with_bot_one : (1 : with_bot ℕ) = (1:ℕ) := rfl
@[simp] lemma with_bot_bit0 (n:ℕ) : bit0 (n : with_bot ℕ) = (bit0 n : ℕ) := rfl
@[simp] lemma with_bot_bit1 (n:ℕ) : bit1 (n : with_bot ℕ) = (bit1 n : ℕ) := rfl

open polynomial

theorem q5 (s : finset ℤ) (hs : s ≠ ∅) : irreducible (s.prod (λ n, X - C n) - 1 : polynomial ℤ) :=
begin
  have deg_prod : degree (s.prod (λ n, X - C n)) = card s,
  { simp only [degree_prod, degree_X_sub_C, sum_const,
      add_monoid.smul_one, with_bot.nat_cast] },
  have deg_lt : degree (1 : polynomial ℤ) < degree (s.prod (λ n, X - C n)),
  { rwa [deg_prod, degree_one, with_bot_zero, with_bot.coe_lt_coe, card_pos] },
  split,
  { show ¬is_unit (s.prod (λ n, X - C n) - 1),
    assume h : is_unit (s.prod (λ n, X - C n) - 1),
    rcases h with ⟨⟨f, g, hfg, hgf⟩, hf⟩,
    change s.prod (λ n, X - C n) - 1 = f at hf, subst f,
    replace hfg := congr_arg degree hfg,
    rw [degree_mul_eq, degree_sub_eq_of_degree_gt deg_lt] at hfg,
    rw [deg_prod, degree_one, with_bot_zero] at hfg,
    cases degree g with dg,
    case option.none { cases hfg },
    case option.some { 
      change some (s.card + dg) = some 0 at hfg,
      rw [option.some_inj, add_eq_zero_iff, card_eq_zero] at hfg,
      exact hs hfg.1 } },
  { show ∀ p q, s.prod (λ n, X - C n) - 1 = p * q → is_unit p ∨ is_unit q,
    assume p q : polynomial ℤ,
    assume hpq : s.prod (λ n, X - C n) - 1 = p * q,
    have hpq0 : p + q ≠ 0,
    { assume h : p + q = 0,
      rw add_eq_zero_iff_neg_eq at h, subst q,
      rw mul_neg_eq_neg_mul_symm at hpq,
      replace hpq := congr_arg leading_coeff hpq,
      rw [leading_coeff_sub_of_degree_gt deg_lt] at hpq,
      rw [leading_coeff_prod, leading_coeff_neg, leading_coeff_mul] at hpq,
      simp only [leading_coeff_X_sub_C, prod_const_one] at hpq,
      refine absurd hpq (ne_of_gt (lt_of_le_of_lt (neg_nonpos.2 _) _)),
      { exact mul_self_nonneg _ },
      { exact dec_trivial } },
    have hp0 : p ≠ 0,
    { assume h : p = 0, subst p,
      replace hpq := congr_arg degree hpq,
      rw [degree_sub_eq_of_degree_gt deg_lt, deg_prod, zero_mul, degree_zero] at hpq,
      cases hpq },
    have hq0 : q ≠ 0,
    { assume h : q = 0, subst q,
      replace hpq := congr_arg degree hpq,
      rw [degree_sub_eq_of_degree_gt deg_lt, deg_prod, mul_zero, degree_zero] at hpq,
      cases hpq },
    have hroots : s ⊆ roots (p + q),
    { show ∀ x, x ∈ s → x ∈ roots (p + q),
      intros x hxs, rw [mem_roots hpq0, is_root.def, eval_add],
      replace hpq := congr_arg (eval x) hpq,
      rw [eval_sub, eval_one, eval_mul, eval_prod] at hpq,
      simp only [eval_sub, eval_X, eval_C] at hpq,
      rw [prod_eq_zero hxs (sub_self x), zero_sub, eq_comm, int.mul_eq_neg_one] at hpq,
      rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩; rw [hp, hq]; refl },
    have hdpmq : degree (p * q) = s.card,
    { rw [← hpq, degree_sub_eq_of_degree_gt deg_lt, deg_prod] },
    have hdpdq : degree p + degree q = s.card,
    { rw [← degree_mul_eq, hdpmq] },
    rw [degree_eq_nat_degree hp0, degree_eq_nat_degree hq0, ← with_bot.coe_add, with_bot.coe_eq_coe] at hdpdq,
    have hdpq : degree (p + q) = s.card,
    { apply le_antisymm,
      { show degree (p + q) ≤ s.card,
        refine le_trans (degree_add_le _ _) (max_le _ _),
        { rw [degree_eq_nat_degree hp0, with_bot.coe_le_coe, ← hdpdq],
          exact nat.le_add_right _ _ },
        { rw [degree_eq_nat_degree hq0, with_bot.coe_le_coe, ← hdpdq],
          exact nat.le_add_left _ _ } },
      { show (s.card : with_bot ℕ) ≤ degree (p + q),
        refine le_trans _ (card_roots hpq0),
        rw [with_bot.coe_le_coe], exact card_le_of_subset hroots } },
    cases le_total (degree p) (degree q) with hdplq hdqlp,
    { have hdp0 : degree p ≤ 0,
      { rw [degree_eq_nat_degree hp0, with_bot_zero, with_bot.coe_le_coe],
        rw [← add_le_add_iff_right (nat_degree q), hdpdq, zero_add, ← with_bot.coe_le_coe],
        rw [← hdpq, ← degree_eq_nat_degree hq0],
        refine le_trans (degree_add_le _ _) (max_le hdplq (le_refl _)) },
      have : coeff p 0 = leading_coeff p,
      { rw leading_coeff, congr, rw [eq_C_of_degree_le_zero hdp0, nat_degree_C] },
      left, refine is_unit_of_mul_one _ (C (leading_coeff q)) _,
      rw [eq_C_of_degree_le_zero hdp0, this, ← C_mul, ← leading_coeff_mul, ← hpq],
      rw [leading_coeff_sub_of_degree_gt deg_lt, leading_coeff_prod],
      simp only [leading_coeff_X_sub_C, prod_const_one, C_1] },
    { have hdq0 : degree q ≤ 0,
      { rw [degree_eq_nat_degree hq0, with_bot_zero, with_bot.coe_le_coe],
        rw [← add_le_add_iff_left (nat_degree p), hdpdq, add_zero, ← with_bot.coe_le_coe],
        rw [← hdpq, ← degree_eq_nat_degree hp0],
        refine le_trans (degree_add_le _ _) (max_le (le_refl _) hdqlp) },
      have : coeff q 0 = leading_coeff q,
      { rw leading_coeff, congr, rw [eq_C_of_degree_le_zero hdq0, nat_degree_C] },
      right, refine is_unit_of_mul_one _ (C (leading_coeff p)) _,
      rw [eq_C_of_degree_le_zero hdq0, this, ← C_mul, ← leading_coeff_mul, mul_comm, ← hpq],
      rw [leading_coeff_sub_of_degree_gt deg_lt, leading_coeff_prod],
      simp only [leading_coeff_X_sub_C, prod_const_one, C_1] } }
end
