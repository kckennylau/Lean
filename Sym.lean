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

end fin


section miscellaneous

theorem nat.pred_eq_of_eq_succ {m n : ℕ}
  (H : m = n.succ) : m.pred = n :=
by simp [H]

@[simp] lemma equiv.symm_apply_eq {α β} {e : α ≃ β} {x y} :
  e.symm x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

end miscellaneous



variable (n : ℕ)

def Sym : Type :=
equiv.perm (fin n)

instance : has_coe_to_fun (Sym n) :=
equiv.has_coe_to_fun

@[extensionality] theorem Sym.ext (σ τ : Sym n)
  (H : ∀ i, σ i = τ i) : σ = τ :=
equiv.ext _ _ H

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

instance : decidable_eq (Sym n) :=
equiv.decidable_eq_of_equiv Sym.equiv

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
