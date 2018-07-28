import data.fintype data.equiv.basic

namespace list

@[simp] lemma length_attach {α} (L : list α) :
  L.attach.length = L.length :=
length_pmap

@[simp] lemma nth_le_attach {α} (L : list α) (i) (H : i < L.attach.length) :
  (L.attach.nth_le i H).1 = L.nth_le i (length_attach L ▸ H) :=
calc  (L.attach.nth_le i H).1
    = (L.attach.map subtype.val).nth_le i (by simpa using H) : by rw nth_le_map'
... = L.nth_le i _ : by congr; apply attach_map_val

@[simp] lemma nth_le_range {n} (i) (H : i < (range n).length) :
  nth_le (range n) i H = i :=
option.some.inj $ by rw [← nth_le_nth _, nth_range (by simpa using H)]

attribute [simp] length_of_fn
attribute [simp] nth_le_of_fn

-- Congratulations, I proved that two things which have
-- equally few lemmas are equal.
theorem of_fn_eq_pmap {α n} {f : fin n → α} :
  of_fn f = pmap (λ i hi, f ⟨i, hi⟩) (range n) (λ _, mem_range.1) :=
by rw [pmap_eq_map_attach]; from ext_le (by simp)
  (λ i hi1 hi2, by simp at hi1; simp [nth_le_of_fn f ⟨i, hi1⟩])

theorem nodup_of_fn {α n} {f : fin n → α} (hf : function.injective f) :
  nodup (of_fn f) :=
by rw of_fn_eq_pmap; from nodup_pmap
  (λ _ _ _ _ H, fin.veq_of_eq $ hf H) (nodup_range n)

end list



section fin

variables {m n : ℕ}

def fin_zero_elim {C : Sort*} : fin 0 → C :=
λ x, false.elim $ nat.not_lt_zero x.1 x.2

def fin_sum : (fin m ⊕ fin n) ≃ fin (m + n) :=
{ to_fun := λ x, sum.rec_on x
    (λ y, ⟨y.1, nat.lt_of_lt_of_le y.2 $ nat.le_add_right m n⟩)
    (λ y, ⟨m + y.1, nat.add_lt_add_left y.2 m⟩),
  inv_fun := λ x, if H : x.1 < m
    then sum.inl ⟨x.1, H⟩
    else sum.inr ⟨x.1 - m, nat.lt_of_add_lt_add_left $
      show m + (x.1 - m) < m + n,
      from (nat.add_sub_of_le $ le_of_not_gt H).symm ▸ x.2⟩,
  left_inv := λ x, sum.cases_on x
    (λ y, by simp [y.2]; from fin.eq_of_veq rfl)
    (λ y, have H : ¬m + y.val < m, by simp [nat.zero_le],
       by simp [H, nat.add_sub_cancel_left];
       from fin.eq_of_veq rfl),
  right_inv := λ x, begin
    by_cases H : x.1 < m,
    { dsimp; rw [dif_pos H]; simp,
      exact fin.eq_of_veq rfl },
    { dsimp; rw [dif_neg H]; simp,
      apply fin.eq_of_veq; simp,
      rw [nat.add_sub_of_le (le_of_not_gt H)] }
  end }

def fin_prod : (fin m × fin n) ≃ fin (m * n) :=
{ to_fun := λ x, ⟨x.2.1 + n * x.1.1, calc
          x.2.1 + n * x.1.1 + 1
        = x.1.1 * n + x.2.1 + 1 : by ac_refl
    ... ≤ x.1.1 * n + n : nat.add_le_add_left x.2.2 _
    ... = (x.1.1 + 1) * n : eq.symm $ nat.succ_mul _ _
    ... ≤ m * n : nat.mul_le_mul_right _ x.1.2⟩,
  inv_fun := λ x, have H : n > 0,
      from nat.pos_of_ne_zero $ λ H,
        nat.not_lt_zero x.1 $ by subst H; from x.2,
    (⟨x.1 / n, (nat.div_lt_iff_lt_mul _ _ H).2 x.2⟩,
     ⟨x.1 % n, nat.mod_lt _ H⟩),
  left_inv := λ ⟨x, y⟩, have H : n > 0,
      from nat.pos_of_ne_zero $ λ H,
        nat.not_lt_zero y.1 $ H ▸ y.2,
    prod.ext
    (fin.eq_of_veq $ calc
            (y.1 + n * x.1) / n
          = y.1 / n + x.1 : nat.add_mul_div_left _ _ H
      ... = 0 + x.1 : by rw nat.div_eq_of_lt y.2
      ... = x.1 : nat.zero_add x.1)
    (fin.eq_of_veq $ calc
            (y.1 + n * x.1) % n
          = y.1 % n : nat.add_mul_mod_self_left _ _ _
      ... = y.1 : nat.mod_eq_of_lt y.2),
    right_inv := λ x, fin.eq_of_veq $ nat.mod_add_div _ _ }

@[simp] lemma fin.raise_val (k : fin n) :
  k.raise.val = k.val :=
rfl

def fin.fall : Π i : fin (n+1), i.1 < n → fin n :=
λ i h, ⟨i.1, h⟩

@[simp] lemma fin.fall_val (k : fin (n+1)) (H : k.1 < n) :
  (k.fall H).val = k.val :=
rfl

def fin.descend (pivot : fin (n+1)) : Π i : fin (n+1), i ≠ pivot → fin n :=
λ i H, if h : i.1 < pivot.1
  then i.fall (lt_of_lt_of_le h $ nat.le_of_lt_succ pivot.2)
  else i.pred (λ H1, H $ by subst H1;
    replace h := nat.eq_zero_of_le_zero (le_of_not_gt h);
    from fin.eq_of_veq h.symm)

def fin.ascend (pivot : fin (n+1)) : Π i : fin n, fin (n+1) :=
λ i, if i.1 < pivot.1 then i.raise else i.succ

theorem fin.ascend_ne (pivot : fin (n+1)) (i : fin n) :
  pivot.ascend i ≠ pivot :=
λ H, begin
  unfold fin.ascend at H,
  split_ifs at H;
  rw ← H at h;
  simp [lt_irrefl, nat.lt_succ_self] at h;
  cc
end

@[simp] lemma fin.ascend_descend (pivot i : fin (n+1))
  (H : i ≠ pivot) : pivot.ascend (pivot.descend i H) = i :=
begin
  unfold fin.descend fin.ascend,
  split_ifs with H1 H2 H3; apply fin.eq_of_veq; simp at *,
  { cases pivot with p hp,
    cases i with i hi,
    cases i with i, { simp at * },
    exfalso, apply H, apply fin.eq_of_veq,
    apply le_antisymm, { apply nat.succ_le_of_lt H2 },
    simpa using H1 },
  { cases pivot with p hp,
    cases i with i hi,
    cases i with i,
    { exfalso, apply H, apply fin.eq_of_veq, symmetry,
      apply nat.eq_zero_of_le_zero H2 },
    refl }
end

@[simp] lemma fin.descend_ascend (pivot : fin (n+1))
  (i : fin n) (H : pivot.ascend i ≠ pivot) :
  pivot.descend (pivot.ascend i) H = i :=
begin
  unfold fin.descend fin.ascend,
  apply fin.eq_of_veq,
  by_cases h : i.val < pivot.val,
  { simp [h] },
  { unfold ite dite,
    cases nat.decidable_lt ((ite (i.val < pivot.val) (fin.raise i) (fin.succ i)).val) (pivot.val) with h1 h1,
    { simp,
      cases nat.decidable_lt (i.val) (pivot.val),
      { simp },
      { cc } },
    { simp,
      cases nat.decidable_lt (i.val) (pivot.val) with h2 h2,
      { simp [h2] at h1,
        simp at *,
        exfalso, apply lt_asymm (nat.lt_succ_self i.1),
        apply lt_of_lt_of_le h1 h },
      { simp } } }
end

@[simp] lemma fin.succ_pred (i : fin (n+1)) (H : i ≠ 0) :
  (i.pred H).succ = i :=
begin
  apply fin.eq_of_veq,
  cases i with i hi,
  cases i,
  { exfalso, apply H, apply fin.eq_of_veq, refl },
  refl
end

@[simp] lemma fin.pred_succ (i : fin n) (H : i.succ ≠ 0) :
  i.succ.pred H = i :=
by cases i; refl

instance : decidable_linear_order (fin n) :=
{ le_refl := λ ⟨i, hi⟩, nat.le_refl i,
  le_trans := λ ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk, nat.le_trans hij hjk,
  le_antisymm := λ ⟨i, hi⟩ ⟨j, hj⟩ hij hji, fin.eq_of_veq $ nat.le_antisymm hij hji,
  le_total := λ ⟨i, hi⟩ ⟨j, hj⟩, or.cases_on (@nat.le_total i j) or.inl or.inr,
  decidable_le := fin.decidable_le,
  .. fin.has_le, .. }

end fin


section miscellaneous

theorem nat.pred_eq_of_eq_succ {m n : ℕ}
  (H : m = n.succ) : m.pred = n :=
by simp [H]

@[simp] lemma equiv.symm_apply_eq {α β} {e : α ≃ β} {x y} :
  e.symm x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

theorem finset.lt_wf {α} [decidable_eq α] :
  well_founded (@has_lt.lt (finset α) _) :=
have H : subrelation (@has_lt.lt (finset α) _)
    (inv_image (<) finset.card),
  from λ x y hxy, finset.card_lt_card hxy,
subrelation.wf H $ inv_image.wf _ $ nat.lt_wf

end miscellaneous



variable (n : ℕ)

def Sym : Type :=
equiv.perm (fin n)

instance : has_coe_to_fun (Sym n) :=
equiv.has_coe_to_fun

@[extensionality] theorem Sym.ext (σ τ : Sym n)
  (H : ∀ i, σ i = τ i) : σ = τ :=
equiv.ext _ _ H

theorem Sym.ext_iff (σ τ : Sym n) :
  σ = τ ↔ ∀ i, σ i = τ i :=
⟨λ H i, H ▸ rfl, Sym.ext _ _ _⟩

instance : decidable_eq (Sym n) :=
λ σ τ, decidable_of_iff' _ (Sym.ext_iff _ _ _)

instance : group (Sym n) :=
equiv.perm_group

variable {n}

section perm

def Sym.to_list (σ : Sym n) : list (fin n) :=
list.of_fn σ

theorem Sym.to_list_perm (σ : Sym n) :
  σ.to_list ~ list.of_fn (1 : Sym n) :=
(list.perm_ext
  (list.nodup_of_fn $ σ.bijective.1)
  (list.nodup_of_fn $ (1 : Sym n).bijective.1)).2 $ λ f,
by rw [list.of_fn_eq_pmap, list.of_fn_eq_pmap, list.mem_pmap, list.mem_pmap]; from
⟨λ _, ⟨f.1, by simp [f.2], fin.eq_of_veq rfl⟩,
λ _, ⟨(σ⁻¹ f).1, by simp [(σ⁻¹ f).2], by convert equiv.apply_inverse_apply σ f;
  from congr_arg _ (fin.eq_of_veq rfl)⟩⟩

def list.to_sym (L : list (fin n))
  (HL : L ~ list.of_fn (1 : Sym n)) : Sym n :=
{ to_fun := λ f, list.nth_le L f.1 $
    by rw [list.perm_length HL, list.length_of_fn]; from f.2,
  inv_fun := λ f, ⟨list.index_of f L,
    begin
      convert list.index_of_lt_length.2 _,
      { rw [list.perm_length HL, list.length_of_fn] },
      { rw [list.mem_of_perm HL, list.mem_iff_nth_le],
        refine ⟨f.1, _, _⟩,
        { rw list.length_of_fn,
          exact f.2 },
        { apply list.nth_le_of_fn } }
    end⟩,
  left_inv := λ f, fin.eq_of_veq $ list.nth_le_index_of
    ((list.perm_nodup HL).2 $ list.nodup_of_fn $ λ _ _, id) _ _,
  right_inv := λ f, list.index_of_nth_le $ list.index_of_lt_length.2 $
    (list.mem_of_perm HL).2 $ list.mem_iff_nth_le.2 $
    ⟨f.1, by rw list.length_of_fn; from f.2,
      list.nth_le_of_fn _ _⟩ }

@[simp] lemma list.to_sym_apply (L : list (fin n))
  (HL : L ~ list.of_fn (1 : Sym n)) (i) :
  (L.to_sym HL) i = L.nth_le i.1 (by simp [list.perm_length HL, i.2]) :=
rfl

@[simp] lemma Sym.to_list_to_sym (σ : Sym n) :
  σ.to_list.to_sym σ.to_list_perm = σ :=
Sym.ext _ _ _ $ λ i, fin.eq_of_veq $ by simp [Sym.to_list]

end perm

def Sym.equiv_0 : Sym 0 ≃ fin (0:ℕ).fact :=
{ to_fun    := λ _, ⟨0, dec_trivial⟩,
  inv_fun   := λ _, 1,
  left_inv  := λ _, Sym.ext _ _ _ $ λ ⟨n, H⟩, by cases H,
  right_inv := λ ⟨n, H⟩, fin.eq_of_veq $
    by cases H with H1 H1; [refl, cases H1] }

def Sym.descend (σ : Sym (n+1)) : Sym n :=
{ to_fun    := λ i, (σ 0).descend (σ i.succ)
    (λ H, by cases i; from nat.no_confusion
      (fin.veq_of_eq (σ.bijective.1 H))),
  inv_fun   := λ i, (σ.symm ((σ 0).ascend i)).pred $ λ H,
    fin.ascend_ne (σ 0) i $ by simpa using H,
  left_inv  := λ i, fin.eq_of_veq $ by dsimp; rw [fin.pred_val];
    apply nat.pred_eq_of_eq_succ; rw [← fin.succ_val];
    apply fin.veq_of_eq; simp,
  right_inv := λ i, fin.eq_of_veq $ by simp }

def Sym.ascend (σ : Sym n) (k : fin (n+1)) : Sym (n+1) :=
{ to_fun    := λ i, if H : i = 0 then k
    else k.ascend $ σ $ i.pred H,
  inv_fun   := λ i, if H : i = k then 0
    else (σ.symm $ k.descend i H).succ,
  left_inv  := λ i, fin.eq_of_veq $ begin
      dsimp,
      by_cases h1 : i = 0,
      { simp [h1] },
      { rw [dif_neg h1],
        rw [dif_neg (fin.ascend_ne k (σ (i.pred h1)))],
        simp }
    end,
  right_inv := λ i, fin.eq_of_veq $ begin
      dsimp,
      by_cases h1 : i = k,
      { simp [h1] },
      { rw [dif_neg h1, dif_neg], { simp },
        intro H,
        replace H := fin.veq_of_eq H,
        simp at H,
        exact nat.no_confusion H }
    end }

@[simp] lemma Sym.descend_ascend (σ : Sym n) (k : fin (n+1)) :
  Sym.descend (Sym.ascend σ k) = σ :=
begin
  ext i,
  dsimp [Sym.ascend, Sym.descend],
  have H : i.succ ≠ 0,
  { intro H,
    replace H := fin.veq_of_eq H,
    simp at H, injections },
  simp [H]
end

def Sym.equiv_succ (ih : Sym n ≃ fin n.fact) :
  Sym (n+1) ≃ (fin (n+1) × fin n.fact) :=
{ to_fun    := λ σ, (σ 0, ih $ Sym.descend σ),
  inv_fun   := λ F, Sym.ascend (ih.symm F.2) F.1,
  left_inv  := λ σ, Sym.ext _ _ _ $ λ i, begin
    dsimp, rw [equiv.inverse_apply_apply ih],
    dsimp [Sym.descend, Sym.ascend],
    split_ifs, {subst h},
    simp
  end,
  right_inv := λ F, prod.ext
      (fin.eq_of_veq $ by dsimp [Sym.ascend]; simp) $
    fin.eq_of_veq $ by simp }

def Sym.equiv : Sym n ≃ fin n.fact :=
nat.rec_on n Sym.equiv_0 $ λ n ih,
calc  Sym (n+1)
    ≃ (fin (n+1) × fin n.fact) : Sym.equiv_succ ih
... ≃ fin (n+1).fact : fin_prod

instance : fintype (Sym n) :=
fintype.of_equiv _ Sym.equiv.symm

theorem Sym.card : fintype.card (Sym n) = nat.fact n :=
(fintype.of_equiv_card Sym.equiv.symm).trans $
fintype.card_fin _

theorem Cayley (α : Type*) [group α] [fintype α] :
  ∃ f : α → Sym (fintype.card α), function.injective f ∧ is_group_hom f :=
nonempty.rec_on (fintype.card_eq.1 $ fintype.card_fin $ fintype.card α) $ λ φ,
⟨λ x, ⟨λ i, φ.symm (x * φ i), λ i, φ.symm (x⁻¹ * φ i),
  λ i, by simp, λ i, by simp⟩,
λ x y H, have H1 : _ := congr_fun (equiv.mk.inj H).1 (φ.symm 1), by simpa using H1,
⟨λ x y, Sym.ext _ _ _ $ λ i, by simp [mul_assoc]⟩⟩


@[simp] lemma Sym.mul_apply (σ τ : Sym n) (i : fin n) :
  (σ * τ) i = σ (τ i) :=
rfl

@[simp] lemma Sym.one_apply (i : fin n) :
  (1 : Sym n) i = i :=
rfl

@[simp] lemma Sym.inv_apply (σ : Sym n) (i : fin n) :
  σ⁻¹ i = σ.symm i :=
rfl

def Sym.swap (i j : fin n) : Sym n :=
{ to_fun    := λ k, if k = i then j
    else if k = j then i else k,
  inv_fun   := λ k, if k = i then j
    else if k = j then i else k,
  left_inv  := λ k, by dsimp; split_ifs; cc,
  right_inv := λ k, by dsimp; split_ifs; cc }

@[simp] lemma Sym.swap_left (i j : fin n) :
  Sym.swap i j i = j :=
by dsimp [Sym.swap]; cc

@[simp] lemma Sym.swap_right (i j : fin n) :
  Sym.swap i j j = i :=
by dsimp [Sym.swap]; split_ifs; cc

@[simp] lemma Sym.swap_mul_self (i j : fin n) :
  Sym.swap i j * Sym.swap i j = 1 :=
Sym.ext _ _ _ $ λ k, by dsimp [Sym.swap]; split_ifs; cc

theorem Sym.swap_comm (i j : fin n) :
  Sym.swap i j = Sym.swap j i :=
Sym.ext _ _ _ $ λ k, by dsimp [Sym.swap]; split_ifs; cc

@[simp] theorem Sym.swap_self (i : fin n) :
  Sym.swap i i = 1 :=
Sym.ext _ _ _ $ λ k, by dsimp [Sym.swap]; split_ifs; cc

def Sym.support (σ : Sym n) : finset (fin n) :=
finset.filter (λ i, σ i ≠ i) finset.univ

theorem Sym.support_def {σ : Sym n} {i : fin n} :
  i ∈ σ.support ↔ σ i ≠ i :=
⟨λ H, (finset.mem_filter.1 H).2, λ H, finset.mem_filter.2 ⟨finset.mem_univ _, H⟩⟩

def Sym.support_choice (σ : Sym n) (H : σ.support ≠ ∅) :
  { i // i ∈ σ.support } :=
⟨@option.get _ σ.support.min $
  let ⟨k, hk⟩ := finset.exists_mem_of_ne_empty H in
  let ⟨b, hb⟩ := finset.min_of_mem hk in by simp at hb; simp [hb],
finset.mem_of_min $ by simp⟩

theorem Sym.support_swap_mul {σ : Sym n} {i : fin n}
  (H : i ∈ σ.support) : (Sym.swap i (σ i) * σ).support < σ.support :=
begin
  split,
  { intros j h1,
    simp [Sym.support_def, Sym.swap] at *,
    split_ifs at h1,
    { intro h2, rw h2 at h, subst h, cc },
    { cc },
    { cc } },
  intro H1,
  specialize H1 H,
  simp [Sym.support_def, Sym.swap] at H1,
  apply H1,
  split_ifs; cc
end

def Sym.is_valid (L : list (Sym n)) : Prop :=
∀ τ ∈ L, ∃ i j, i ≠ j ∧ τ = Sym.swap i j

def Sym.list_swap.aux : has_well_founded (Sym n) :=
{ r := inv_image (<) Sym.support,
  wf := inv_image.wf _ finset.lt_wf }

local attribute [instance] Sym.list_swap.aux
attribute [elab_as_eliminator] well_founded.fix
attribute [elab_as_eliminator] well_founded.induction

def Sym.list_swap (σ : Sym n) : list (Sym n) :=
by refine well_founded.fix Sym.list_swap.aux.wf _ σ; from
λ σ ih, if H : σ.support = ∅ then []
  else let ⟨i, hi⟩ := σ.support_choice H in
    (Sym.swap i (σ i)) :: ih (Sym.swap i (σ i) * σ) (Sym.support_swap_mul hi)

theorem Sym.list_swap_valid (σ : Sym n) :
  Sym.is_valid σ.list_swap :=
well_founded.induction Sym.list_swap.aux.wf σ $ λ σ ih τ H,
begin
  dsimp [Sym.list_swap] at H,
  rw [well_founded.fix_eq] at H,
  split_ifs at H, { cases H },
  cases Sym.support_choice σ h with i hi,
  unfold Sym.list_swap._match_1 at H,
  cases H with H H,
  { subst H,
    rw [Sym.support_def] at hi,
    exact ⟨_, _, hi.symm, rfl⟩ },
  exact ih _ (Sym.support_swap_mul hi) τ H
end

theorem Sym.list_swap_prod (σ : Sym n) :
  σ.list_swap.prod = σ :=
well_founded.induction Sym.list_swap.aux.wf σ $ λ σ ih,
begin
  dsimp [Sym.list_swap],
  rw [well_founded.fix_eq],
  split_ifs,
  { ext, by_contra H,
    suffices : i ∈ (∅ : finset (fin n)),
    { simp at this, cc },
    rw [← h, Sym.support_def],
    exact mt eq.symm H },
  cases Sym.support_choice σ h with i hi,
  unfold Sym.list_swap._match_1,
  specialize ih _ (Sym.support_swap_mul hi),
  dsimp [Sym.list_swap] at ih,
  rw [list.prod_cons, ih, ← mul_assoc, Sym.swap_mul_self, one_mul]
end

section mu2

@[derive decidable_eq]
inductive mu2 : Type
| plus_one : mu2
| minus_one : mu2

open mu2

definition neg : mu2 → mu2
| plus_one := minus_one
| minus_one := plus_one

instance : has_one mu2 := ⟨plus_one⟩
instance : has_neg mu2 := ⟨neg⟩

instance : comm_group mu2 :=
{ mul := λ x y, mu2.rec_on x (mu2.rec_on y 1 (-1)) (mu2.rec_on y (-1) 1),
  mul_assoc := λ x y z, by cases x; cases y; cases z; refl,
  mul_one := λ x, by cases x; refl,
  one_mul := λ x, by cases x; refl,
  inv := id,
  mul_left_inv := λ x, by cases x; refl,
  mul_comm := λ x y, by cases x; cases y; refl,
  .. mu2.has_one }

instance : fintype mu2 :=
{ elems := {1, -1},
  complete := λ x, mu2.cases_on x (or.inr $ or.inl rfl) (or.inl rfl) }

theorem mu2.card : fintype.card mu2 = 2 :=
rfl

end mu2
