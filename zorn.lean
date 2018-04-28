-- https://proofwiki.org/wiki/Axiom_of_Choice_Implies_Zorn%27s_Lemma/Proof_1

universe u

instance set.partial_order {α} : partial_order (set α) :=
{ le := (⊆),
  le_refl := λ A z, id,
  le_trans := λ A B C hab hbc z hz, hbc (hab hz),
  le_antisymm := λ A B hab hba, funext $ λ z, propext ⟨@hab z, @hba z⟩ }

local attribute [instance] classical.prop_decidable

namespace zorn

variables {α : Type u} (r : α → α → Prop)

inductive trichotomy (A B) : Prop
| inl (H : r A B) : trichotomy
| eq (H : A = B) : trichotomy
| inr (H : r B A) : trichotomy

theorem trichotomy.symm {r : α → α → Prop} {A B}
  (H : trichotomy r A B) :
  trichotomy r B A :=
trichotomy.cases_on H trichotomy.inr (λ H, trichotomy.eq r H.symm) trichotomy.inl

def chains : set (set α) :=
{ C | ∀ A ∈ C, ∀ B ∈ C, trichotomy r A B }

theorem chains.empty : ∅ ∈ chains r :=
λ _, false.elim

theorem chains.insert {C x} (H1 : C ∈ chains r) (H2 : ∀ y ∈ C, trichotomy r x y) :
  insert x C ∈ chains r :=
λ A HA B HB, or.cases_on HA
  (assume HA : A = x, or.cases_on HB
    (assume HB : B = x, trichotomy.eq r $ HA.trans HB.symm)
    (assume HB : B ∈ C, HA.symm ▸ H2 B HB))
  (assume HA : A ∈ C, or.cases_on HB
    (assume HB : B = x, trichotomy.symm $ HB.symm ▸ H2 A HA)
    (assume HB : B ∈ C, H1 A HA B HB))

theorem chains.union {C} (H1 : C ⊆ chains r) (H2 : C ∈ @chains (set α) (⊆)) :
  { A | ∃ t ∈ C, A ∈ t } ∈ chains r :=
λ A ⟨t, ht1, ht2⟩ B ⟨u, hu1, hu2⟩, trichotomy.cases_on (H2 t ht1 u hu1)
  (λ H3, (H1 hu1) _ (H3 ht2) _ hu2)
  (λ H3, (H1 ht1) A ht2 B (H3.symm ▸ hu2))
  (λ H3, (H1 ht1) _ ht2 _ (H3 hu2))

def extensions (A) : set α :=
{ x | insert x A ∈ chains r }

noncomputable def succ (A : set α) : set α :=
if H : ∃ x, x ∈ extensions r A \ A then insert (classical.some H) A else A

@[elab_as_eliminator] noncomputable def succ.rec {C : set α → set α → Sort*}
  (H1 : ∀ A, ∀ x ∈ extensions r A \ A, C A (insert x A))
  (H2 : ∀ A, extensions r A ⊆ A → C A A)
  (A : set α) : C A (succ r A) :=
if H : ∃ x, x ∈ extensions r A \ A then
  have succ r A = insert (classical.some H) A, from dif_pos H,
  eq.drec_on this.symm $ H1 _ (classical.some H) (classical.some_spec H)
else
  have succ r A = A, from dif_neg H,
  eq.drec_on this.symm $ H2 A $ λ z hz1,
  classical.by_contradiction $ λ hz2, H ⟨z, hz1, hz2⟩

@[elab_as_eliminator] noncomputable def succ.rec_on {C : set α → set α → Sort*}
  (A : set α)
  (H1 : ∀ A, ∀ x ∈ extensions r A \ A, C A (insert x A))
  (H2 : ∀ A, extensions r A ⊆ A → C A A) :
  C A (succ r A) :=
succ.rec r H1 H2 A

theorem succ.mem (A : set α) (x) (H1 : insert x A ∈ chains r) (H2 : x ∉ A) :
  ∃ x, x ∈ extensions r A ∧ x ∉ A ∧ succ r A = insert x A :=
have H : ∃ x, x ∈ extensions r A \ A := ⟨x, H1, H2⟩,
⟨_, and.assoc.1 ⟨classical.some_spec H, dif_pos H⟩⟩

theorem succ.cases (A : set α) :
  (∃ x, x ∉ A ∧ x ∈ extensions r A ∧ succ r A = insert x A) ∨ succ r A = A :=
@succ.rec_on α _ (λ t u, (∃ x, x ∉ t ∧ x ∈ extensions r t ∧ u = insert x t) ∨ u = t) A
  (λ A x hx, or.inl ⟨x, hx.2, hx.1, rfl⟩) (λ _ _, or.inr rfl)

theorem succ.subset {A : set α} : A ⊆ succ r A :=
succ.rec_on r A
  (λ t A H, show t ⊆ insert A t, from λ z, or.inr)
  (λ t H z, id)

theorem chains.succ {A : set α} : A ∈ chains r → succ r A ∈ chains r :=
@succ.rec_on α _ (λ t u, t ∈ chains r → u ∈ chains r) A
  (λ t X HX H, HX.1) (λ _ _, id)

theorem succ.eq_or_eq_of_subset_of_subset (A : set α) :
  ∀ B, A ⊆ B → B ⊆ succ r A → A = B ∨ B = succ r A :=
@succ.rec_on α _ (λ t u, ∀ B, t ⊆ B → B ⊆ u → t = B ∨ B = u) A
  (λ A x hx B HAB HBA, classical.by_cases
    (assume h : x ∈ B, or.inr $ le_antisymm HBA $ λ z hz, or.cases_on hz
      (λ hz1, hz1.symm ▸ h) (@HAB z))
    (assume h : x ∉ B, or.inl $ le_antisymm HAB $ λ z hz, or.cases_on (HBA hz)
      (λ hz1, false.elim $ h $ hz1 ▸ hz) id))
  (λ _ _ _ HBC HCB, or.inl $ le_antisymm HBC HCB)

inductive tower : set (set α)
| succ  : ∀ {A}, tower A → tower (succ r A)
| chain : ∀ {C}, C ⊆ chains r → C ∈ @chains (set α) (⊆) →
    (∀ A ∈ C, tower A) → tower { A | ∃ t ∈ C, A ∈ t }

theorem tower.empty : ∅ ∈ tower r :=
have H : { A | ∃ t ∈ (∅ : set (set α)), A ∈ t } = ∅,
  from le_antisymm (λ _ ⟨_, H, _⟩, H) (λ _, false.elim),
H ▸ tower.chain (λ _, false.elim) (λ _, false.elim) (λ _, false.elim)

theorem tower.subset_chains : tower r ⊆ chains r :=
λ A HA, tower.rec_on HA
  (λ A HA, chains.succ r)
  (λ C HC1 HC2 HC3 ih, chains.union r HC1 HC2)

/-- TLDR: proof by heavy induction -/
theorem tower.chains : tower r ∈ @chains (set α) (⊆) :=
λ A HA, tower.rec_on HA
  (λ C HC ih1 A HA, suffices A ⊆ C ∨ succ r C ⊆ A,
    from or.cases_on this (λ h, trichotomy.inr $ λ z hz, succ.subset r $ h hz) trichotomy.inl,
    tower.rec_on HA
      (λ A HA ih2, or.cases_on ih2
        (assume h1 : A ⊆ C, trichotomy.cases_on (ih1 (succ r A) (tower.succ HA))
          (assume h2 : C ⊆ succ r A, or.cases_on (succ.eq_or_eq_of_subset_of_subset r A C h1 h2)
            (assume h3 : A = C, or.inr $ λ _, h3 ▸ id)
            (assume h3 : C = succ r A, or.inl $ λ _, h3 ▸ id))
          (assume h2 : C = succ r A, or.inl $ λ _, h2 ▸ id)
          or.inl)
        (assume h1 : succ r C ⊆ A, or.inr $ λ z hz, succ.subset r $ h1 hz))
      (λ D HD1 HD2 HD3 ih2, trichotomy.cases_on (ih1 _ (tower.chain HD1 HD2 HD3))
        (λ h1, have H1 : C ⊆ {A : α | ∃ (t : set α) (H : t ∈ D), A ∈ t} ∩ succ r C,
            from λ z hz, ⟨h1 hz, succ.subset r hz⟩,
          have H2 : {A : α | ∃ (t : set α) (H : t ∈ D), A ∈ t} ∩ succ r C ⊆ succ r C,
            from λ _, and.right,
          or.cases_on (succ.eq_or_eq_of_subset_of_subset r _ _ H1 H2)
            (λ h2, or.cases_on (succ.cases r C)
              (λ ⟨x, hx1, hx2, hx3⟩, or.inl $ λ z ⟨t, ht1, ht2⟩,
                or.cases_on (ih2 t ht1) (λ h3, h3 ht2)
                  (λ h3, have H3 : x ∈ succ r C, from hx3.symm ▸ or.inl rfl,
                    false.elim $ hx1 $ h2.symm ▸ ⟨⟨t, ht1, h3 H3⟩, H3⟩))
              (λ h3, h3.symm ▸ or.inr h1))
            (λ h2, or.inr $ h2 ▸ λ _, and.left))
        (λ h1, or.inl $ λ _, h1 ▸ id)
        or.inl))
  (λ C HC1 HC2 HC3 ih B HB, classical.by_cases
      (assume h : ∃ A ∈ C, B ⊆ A, let ⟨A, HA1, HA2⟩ := h in
        trichotomy.inr $ λ z hz, ⟨A, HA1, HA2 hz⟩)
      (assume h : ¬∃ A ∈ C, B ⊆ A, trichotomy.inl $ λ z ⟨t, ht1, ht2⟩,
        trichotomy.cases_on (ih t ht1 B HB)
          (assume H : t ⊆ B, H ht2)
          (assume H : t = B, H ▸ ht2)
          (assume H : B ⊆ t, false.elim $ h ⟨t, ht1, H⟩)))

def fixed : set α :=
{A : α | ∃ t ∈ tower r, A ∈ t}

theorem fixed.tower : fixed r ∈ tower r :=
tower.chain (tower.subset_chains r) (tower.chains r) (λ A, id)

theorem fixed.succ_tower : succ r (fixed r) ∈ tower r :=
tower.succ (fixed.tower r)

theorem fixed.fixed : succ r (fixed r) = fixed r :=
le_antisymm (λ z hz, ⟨succ r (fixed r), fixed.succ_tower r, hz⟩) $
λ z hz, succ.subset r hz

theorem fixed.chains : fixed r ∈ chains r :=
chains.union r (tower.subset_chains r) (tower.chains r)

theorem zorn.aux {M} (HM : ∀ x ∈ fixed r, r x M)
  (trans : ∀ {a b c}, r a b → r b c → r a c) :
  ∀ A, r M A → r A M :=
λ A HA, HM A (classical.by_contradiction $ λ H,
  let ⟨y, hy1, hy2, hy3⟩ := succ.mem r (fixed r) A
    (chains.insert r (fixed.chains r) $ λ y hy,
    trichotomy.inr $ trans (HM y hy) HA) H in
  hy2 $ (fixed.fixed r) ▸ hy3.symm ▸ or.inl rfl)

theorem zorn [HN : nonempty α] [partial_order α]
  (H : ∀ C ∈ @chains α (≤), ∀ y ∈ C, ∃ M, ∀ x ∈ C, x ≤ M) :
  ∃ M : α, ∀ A, M ≤ A → M = A :=
nonempty.elim HN $ λ X,
let ⟨x, hx1, hx2, hx3⟩ := succ.mem (≤) ∅ X
  (chains.insert (≤) (chains.empty (≤)) (λ _, false.elim)) id in
let ⟨M, HM⟩ := H (fixed (≤)) (fixed.chains (≤)) x
  ⟨insert x ∅, hx3 ▸ tower.succ (tower.empty (≤)), or.inl rfl⟩ in
⟨M, λ A HA, le_antisymm HA $
zorn.aux (≤) HM (λ _ _ _, le_trans) A HA⟩

end zorn
