import order.lattice

set_option old_structure_cmd true

universe u

variable (α : Type u)

namespace zfc

class has_zmem extends has_mem α α

instance [has_zmem α] : has_subset α :=
⟨λ x y, ∀ z, z ∈ x → z ∈ y⟩

variable {α}

theorem subset.refl [has_zmem α] (x : α) : x ⊆ x := λ z, id
theorem subset.trans [has_zmem α] {x y z : α}
  (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
λ p hp, hyz p $ hxy p hp

instance [has_zmem α] : preorder α :=
⟨(⊆), _, subset.refl, λ x y z, subset.trans⟩

variable α

class is_extensional extends has_zmem α :=
(ext : ∀ x y : α, (∀ z, z ∈ x ↔ z ∈ y) → x = y )

variable {α}

theorem subset.antisymm [is_extensional α] {x y : α}
  (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y :=
is_extensional.ext x y $ λ z, ⟨λ hx, hxy z hx, λ hy, hyx z hy⟩

instance partial_order [is_extensional α] : partial_order α :=
{ le_antisymm := λ x y, subset.antisymm,
  .. zfc.preorder }

variable α

class has_zempty extends has_zmem α, has_emptyc α :=
(not_zmem_empty : ∀ x, x ∉ (∅:α))

class has_upair extends has_zmem α :=
(upair : α → α → α)
(zmem_upair_iff_eq_or_eq : ∀ x y z, z ∈ upair x y ↔ z = x ∨ z = y)

variable {α}

theorem not_zmem_empty [has_zempty α] : ∀ {x}, x ∉ (∅:α) :=
has_zempty.not_zmem_empty

def upair [has_upair α] : α → α → α :=
has_upair.upair

def zmem_upair_iff_eq_or_eq [has_upair α] {x y z : α} :
z ∈ upair x y ↔ z = x ∨ z = y :=
has_upair.zmem_upair_iff_eq_or_eq x y z

theorem zmem_upair_left [has_upair α] {x y : α} : x ∈ upair x y :=
zmem_upair_iff_eq_or_eq.2 $ or.inl rfl

theorem zmem_upair_right [has_upair α] {x y : α} : y ∈ upair x y :=
zmem_upair_iff_eq_or_eq.2 $ or.inr rfl

def opair [has_upair α] (x y : α) : α :=
upair (upair x x) (upair x y)

theorem opair.ext [has_upair α] {p q r s : α}
  (h : opair p q = opair r s) : p = r ∧ q = s :=
begin
  have h1 : upair p p ∈ opair p q,
    from zmem_upair_left,
  have h2 : upair p q ∈ opair p q,
    from zmem_upair_right,
  have h3 : p ∈ upair p p,
    from zmem_upair_left,
  have h4 : p ∈ upair p q,
    from zmem_upair_left,
  have h5 : q ∈ upair p q,
    from zmem_upair_right,
  have h6 : upair r r ∈ opair r s,
    from zmem_upair_left,
  have h7 : upair r s ∈ opair r s,
    from zmem_upair_right,
  have h8 : r ∈ upair r r,
    from zmem_upair_left,
  have h9 : r ∈ upair r s,
    from zmem_upair_left,
  have h0 : s ∈ upair r s,
    from zmem_upair_right,
  rw h at h1 h2,
  rw ← h at h6 h7,
  unfold opair at h1 h2 h6 h7,
  rw zmem_upair_iff_eq_or_eq at h1 h2 h6 h7,
  cases h1,
  { rw [h1, zmem_upair_iff_eq_or_eq, or_self] at h3,
    subst h3,
    cases h2,
    { rw [h2, zmem_upair_iff_eq_or_eq, or_self] at h5,
      subst h5,
      rw or_self at h7,
      rw [h7, zmem_upair_iff_eq_or_eq, or_self] at h0,
      subst h0,
      split, refl, refl },
    { rw [h2, zmem_upair_iff_eq_or_eq] at h5,
      cases h5; subst h5,
      { rw [← h2, zmem_upair_iff_eq_or_eq, or_self] at h0,
        subst h0,
        split, refl, refl },
      { split, refl, refl } } },
  { rw [← h1, zmem_upair_iff_eq_or_eq, or_self] at h9,
    subst h9,
    rw [← h1, zmem_upair_iff_eq_or_eq, or_self] at h0,
    subst h0,
    rw or_self at h2,
    rw [h2, zmem_upair_iff_eq_or_eq, or_self] at h5,
    subst h5,
    split, refl, refl }
end

variable α

class has_sUnion extends has_zmem α :=
(sUnion : α → α)
(zmem_sUnion_iff_zmem_zmem : ∀ x z, z ∈ sUnion x ↔ ∃ t, z ∈ t ∧ t ∈ x)

variable {α}

def sUnion [has_sUnion α] : α → α :=
has_sUnion.sUnion

def zmem_sUnion_iff_zmem_zmem [has_sUnion α] {x z : α} : z ∈ sUnion x ↔ ∃ t, z ∈ t ∧ t ∈ x :=
has_sUnion.zmem_sUnion_iff_zmem_zmem x z

variable α

class has_sUnion_upair extends has_sUnion α, has_upair α

instance [has_sUnion_upair α] : has_union α :=
⟨λ x y, sUnion $ upair x y⟩

instance [has_sUnion_upair α] : has_insert α α :=
⟨λ x A, upair x x ∪ A⟩

lemma union_def [has_sUnion_upair α] (x y : α) : x ∪ y = (sUnion $ upair x y) := rfl
lemma insert_def [has_sUnion_upair α] (x A : α) : has_insert.insert x A = upair x x ∪ A := rfl

variable {α}

lemma zmem_union_iff_zmem_or_zmem [has_sUnion_upair α] {x y z : α} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y :=
begin
  rw [union_def, zmem_sUnion_iff_zmem_zmem],
  split,
  { intro H,
    rcases H with ⟨t, H1, H2⟩,
    rw [zmem_upair_iff_eq_or_eq] at H2,
    cases H2; subst H2,
    { left, assumption },
    { right, assumption } },
  { intro H,
    cases H,
    { existsi x,
      split, exact H, exact zmem_upair_left },
    { existsi y,
      split, exact H, exact zmem_upair_right } }
end

lemma zmem_insert_iff_eq_or_zmem [has_sUnion_upair α] {x A z : α} : z ∈ has_insert.insert x A ↔ z = x ∨ z ∈ A :=
by rw [insert_def, zmem_union_iff_zmem_or_zmem, zmem_upair_iff_eq_or_eq, or_self]

theorem zmem_insert [has_sUnion_upair α] {x y : α} : x ∈ has_insert.insert x y :=
zmem_insert_iff_eq_or_zmem.2 $ or.inl rfl

theorem zmem_insert_of_zmem [has_sUnion_upair α] {x y z : α} (H : x ∈ z) : x ∈ has_insert.insert y z :=
zmem_insert_iff_eq_or_zmem.2 $ or.inr H

def succ [has_sUnion_upair α] : α → α :=
λ x, has_insert.insert x x

theorem zmem_succ_iff_eq_or_zmem [has_sUnion_upair α] {x y : α} : x ∈ succ y ↔ x = y ∨ x ∈ y :=
zmem_insert_iff_eq_or_zmem

theorem zmem_succ [has_sUnion_upair α] {x : α} : x ∈ succ x :=
zmem_succ_iff_eq_or_zmem.2 $ or.inl rfl

theorem zmem_succ_of_zmem [has_sUnion_upair α] {x y : α} (H : x ∈ y) : x ∈ succ y :=
zmem_succ_iff_eq_or_zmem.2 $ or.inr H

variable α

class has_powerset extends has_zmem α :=
(powerset : α → α)
(zmem_powerset : ∀ x z, z ∈ powerset x ↔ z ⊆ x)

class has_comprehension extends has_zmem α :=
(comprehension : α → (α → Prop) → α)
(zmem_comprehension_iff : ∀ A p x, x ∈ comprehension A p ↔ x ∈ A ∧ p x)

class has_infty :=
(infinity : α)

notation `∞` := has_infty.infinity _

class has_replacement extends has_zmem α :=
(replacement : α → (α → α → Prop) → α)
(zmem_replacement_iff : ∀ A (f : α → α → Prop) y (H : ∀ A B C, f A B → f A C → B = C), (y ∈ replacement A f ↔ ∃ x, x ∈ A ∧ f x y))

class has_infty_replacement_powerset extends has_infty α, has_replacement α, has_powerset α

class has_infty_replacement_powerset_sUnion extends has_infty_replacement_powerset α, has_sUnion α

variable {α}

instance has_infty.to_inhabited [has_infty α] : inhabited α :=
⟨∞⟩

def powerset [has_powerset α] : α → α :=
has_powerset.powerset

theorem zmem_powerset [has_powerset α] : ∀ {x z : α}, z ∈ powerset x ↔ z ⊆ x :=
has_powerset.zmem_powerset

def comprehension [has_comprehension α] : α → (α → Prop) → α :=
has_comprehension.comprehension

theorem zmem_comprehension_iff [has_comprehension α] : ∀ {A : α} {p x}, x ∈ comprehension A p ↔ x ∈ A ∧ p x :=
has_comprehension.zmem_comprehension_iff

def replacement [has_replacement α] : α → (α → α → Prop) → α :=
has_replacement.replacement

theorem zmem_replacement_iff [has_replacement α] {A} {f : α → α → Prop} {y} (H : ∀ A B C, f A B → f A C → B = C) :
  (y ∈ replacement A f ↔ ∃ x, x ∈ A ∧ f x y) :=
has_replacement.zmem_replacement_iff A f y H

instance has_comprehension.to_has_zempty [s : has_comprehension α] [inhabited α] : has_zempty α :=
{ emptyc := comprehension (inhabited.default α) (λ x, false),
  not_zmem_empty := λ x hx, begin
    simp [∅] at hx,
    rw [zmem_comprehension_iff] at hx,
    exact hx.2
  end,
  .. s }

instance has_replacement.to_has_comprehension [s : has_replacement α] : has_comprehension α :=
{ comprehension := λ A p, replacement A (λ x y, x = y ∧ p x),
  zmem_comprehension_iff := λ A p x, begin
    have h1 : ∀ A B C, A = B ∧ p A → A = C ∧ p A → B = C,
    { intros A B C h1 h2,
      rw [← h1.1, ← h2.1] },
    rw [zmem_replacement_iff h1],
    split,
    { intro H,
      rcases H with ⟨w, H1, H2, H3⟩,
      subst H2,
      exact ⟨H1, H3⟩ },
    { intro H,
      existsi x,
      simpa }
  end,
  .. s }

instance has_infty_replacement_powerset.to_has_zempty [s : has_infty_replacement_powerset α] : has_zempty α :=
{ .. s, .. has_comprehension.to_has_zempty }

instance has_infty_replacement_powerset.to_has_upair [s : has_infty_replacement_powerset α] : has_upair α :=
{ upair := λ x y, replacement (powerset (powerset ∅)) (λ m n, m = ∅ ∧ n = x ∨ m = powerset ∅ ∧ n = y),
     zmem_upair_iff_eq_or_eq := λ x y z, begin
       have h1 : ∀ (A B C : α),
         A = ∅ ∧ B = x ∨ A = powerset ∅ ∧ B = y →
         A = ∅ ∧ C = x ∨ A = powerset ∅ ∧ C = y → B = C,
       { intros A B C h1 h2,
         cases h1; cases h2;
         cases h1 with h3 h4;
         cases h2 with h5 h6,
         { subst h4, subst h6 },
         { exfalso,
           rw h3 at h5,
           have h7 : (∅:α) ∈ powerset ∅,
           { rw zmem_powerset,
             exact subset.refl ∅ },
           rw ← h5 at h7,
           exact not_zmem_empty h7 },
         { exfalso,
           rw h3 at h5,
           have h7 : (∅:α) ∈ powerset ∅,
           { rw zmem_powerset,
             exact subset.refl ∅ },
           rw h5 at h7,
           exact not_zmem_empty h7 },
         { subst h4, subst h6 } },
       rw zmem_replacement_iff h1,
       split,
       { intro H,
         rcases H with ⟨w, H1, ⟨H2, H3⟩ | ⟨H2, H3⟩⟩,
         { left, assumption },
         { right, assumption } },
       { intro H,
         cases H,
         { existsi ∅,
           split,
           { rw zmem_powerset,
             intros z hz,
             exfalso,
             exact not_zmem_empty hz },
           { left, split, refl, assumption } },
         { existsi powerset ∅,
           split,
           { rw zmem_powerset,
             exact subset.refl _ },
           { right, split, refl, assumption } } }
     end,
     .. s }

instance has_infty_replacement_powerset_sUnion.to_has_sUnion_upair [s : has_infty_replacement_powerset_sUnion α] : has_sUnion_upair α :=
{ .. s, .. has_infty_replacement_powerset.to_has_upair }

variable α

class has_zinfty extends has_infty α, has_infty_replacement_powerset_sUnion α :=
(empty_zmem_infinity : (∅:α) ∈ (∞:α))
(succ_zmem_infinity_of_zmem_infinity : ∀ x:α, x ∈ (∞:α) → succ x ∈ (∞:α))

class is_regular extends has_zmem α :=
(regular : ∀ x : α, (∃ y, y ∈ x) → (∃ y : α, y ∈ x ∧ ∀ z, z ∈ y → z ∈ x → false))

variable {α}

theorem empty_zmem_infinity [has_zinfty α] : (∅:α) ∈ (∞:α) :=
has_zinfty.empty_zmem_infinity α

theorem succ_zmem_infinity_of_zmem_infinity [has_zinfty α] : ∀ x:α, x ∈ (∞:α) → succ x ∈ (∞:α) :=
has_zinfty.succ_zmem_infinity_of_zmem_infinity

theorem regular [is_regular α] : ∀ x : α, (∃ y, y ∈ x) → (∃ y : α, y ∈ x ∧ ∀ z, z ∈ y → z ∈ x → false) :=
is_regular.regular

variable α

class zf extends has_zmem α, is_extensional α, has_sUnion α, has_powerset α, has_replacement α, has_zinfty α, is_regular α

section zf

variables {α} [zf α] {x y z : α}

theorem singleton_def : {x} = has_insert.insert x (∅:α) := rfl

theorem mem_singleton_iff : x ∈ ({y}:α) ↔ x = y :=
begin
  rw [singleton_def, zmem_insert_iff_eq_or_zmem],
  apply or_iff_left_of_imp,
  intro H,
  exfalso,
  exact not_zmem_empty H
end

theorem mem_singleton : x ∈ ({x}:α) :=
begin
  rw [singleton_def, zmem_insert_iff_eq_or_zmem],
  left, refl
end

theorem not_zmem_self : x ∉ x :=
λ h, begin
  rcases regular {x} ⟨x, mem_singleton⟩ with ⟨y, h1, h2⟩,
  rw mem_singleton_iff at h1,
  subst h1,
  exact h2 y h mem_singleton
end

theorem not_zmem_and_zmem : x ∈ y → y ∈ x → false :=
λ hxy hyx, begin
  rcases regular {x, y} ⟨x, by simp [zmem_insert_iff_eq_or_zmem]; right; exact mem_singleton⟩ with ⟨z, h1, h2⟩,
  rw [zmem_insert_iff_eq_or_zmem, mem_singleton_iff] at h1,
  cases h1; subst h1,
  { apply h2 _ hxy,
    simp [zmem_insert_iff_eq_or_zmem],
    right, exact mem_singleton },
  { apply h2 _ hyx,
    simp [zmem_insert_iff_eq_or_zmem] }
end

theorem succ.ext {x y : α} (H : succ x = succ y) : x = y :=
begin
  simp [succ] at H,
  have H1 : x ∈ has_insert.insert x x,
  { rw zmem_insert_iff_eq_or_zmem,
    left, refl },
  have H2 : y ∈ has_insert.insert y y,
  { rw zmem_insert_iff_eq_or_zmem,
    left, refl },
  rw [H, zmem_insert_iff_eq_or_zmem] at H1,
  rw [← H, zmem_insert_iff_eq_or_zmem] at H2,
  cases H1,
  { assumption },
  { cases H2,
    { subst H2 },
    { exfalso,
      exact not_zmem_and_zmem H1 H2 } }
end

def prod : α → α → α :=
λ X Y, comprehension (powerset $ powerset $ X ∪ Y) (λ z, ∃ x y, x ∈ X ∧ y ∈ Y ∧ z = opair x y)

theorem zmem_prod {A B : α} (hx : x ∈ A) (hy : y ∈ B) : opair x y ∈ prod A B :=
zmem_comprehension_iff.2
⟨zmem_powerset.2 $ λ z (hz : z ∈ opair x y),
   or.cases_on (zmem_upair_iff_eq_or_eq.1 hz)
     (λ hzx, zmem_powerset.2 $ λ w hw,
        or.cases_on (zmem_upair_iff_eq_or_eq.1 $ (hzx ▸ hw : w ∈ upair x x))
          (λ hwx, zmem_union_iff_zmem_or_zmem.2 $ or.inl $ hwx.symm ▸ hx)
          (λ hwx, zmem_union_iff_zmem_or_zmem.2 $ or.inl $ hwx.symm ▸ hx))
     (λ hzxy, zmem_powerset.2 $ λ w hw,
        or.cases_on (zmem_upair_iff_eq_or_eq.1 $ (hzxy ▸ hw : w ∈ upair x y))
          (λ hwx, zmem_union_iff_zmem_or_zmem.2 $ or.inl $ hwx.symm ▸ hx)
          (λ hwy, zmem_union_iff_zmem_or_zmem.2 $ or.inr $ hwy.symm ▸ hy)),
 x, y, hx, hy, rfl⟩

theorem zmem_left_of_zmem_prod {A B : α} (h : opair x y ∈ prod A B) : x ∈ A :=
let ⟨x1, y1, hx1, hy1, h⟩ := (zmem_comprehension_iff.1 h).2 in
(opair.ext h).1.symm ▸ hx1

theorem zmem_right_of_zmem_prod {A B : α} (h : opair x y ∈ prod A B) : y ∈ B :=
let ⟨x1, y1, hx1, hy1, h⟩ := (zmem_comprehension_iff.1 h).2 in
(opair.ext h).2.symm ▸ hy1

class is_relation (f : α) : Prop :=
(eq_opair_of_mem : ∀ z, z ∈ f → ∃ x y, z = opair x y)

def dom (f : α) : α :=
replacement f (λ z x, ∃ y, z = opair x y)

def range (f : α) : α :=
replacement f (λ z y, ∃ x, z = opair x y)

class is_function (f : α) extends is_relation f : Prop :=
(exists_unique : ∀ x, x ∈ dom f → ∃! y, opair x y ∈ f)

noncomputable def eval (f : α) [is_function f] (x : α) (H : x ∈ dom f) : α :=
classical.some $ is_function.exists_unique x H

theorem opair_eval_zmem {f : α} [is_function f] {x : α} (H : x ∈ dom f) : opair x (eval f x H) ∈ f :=
(classical.some_spec $ is_function.exists_unique x H).1

theorem eval_unique (f : α) [is_function f] (x y : α) (H : x ∈ dom f) (Hxy : opair x y ∈ f) : y = eval f x H :=
(classical.some_spec $ is_function.exists_unique x H).2 y Hxy

theorem zmem_dom_iff {f x : α} : x ∈ dom f ↔ ∃ y, opair x y ∈ f :=
begin
  have h1 : ∀ (A B C : α), (∃ (y : α), A = opair B y) → (∃ (y : α), A = opair C y) → B = C,
  { intros A B C h1 h2,
    cases h1 with m h1,
    cases h2 with n h2,
    subst h1,
    exact (opair.ext h2).1 },
  rw [dom, zmem_replacement_iff h1],
  split; intro H,
  { rcases H with ⟨z, h1, w, h2⟩,
    subst h2, existsi w, assumption },
  { cases H with z h,
    existsi opair x z,
    split, assumption, existsi z, refl }
end

theorem zmem_range_iff {f y : α} : y ∈ range f ↔ ∃ x, opair x y ∈ f :=
begin
  have h1 : ∀ (A B C : α), (∃ (x : α), A = opair x B) → (∃ (x : α), A = opair x C) → B = C,
  { intros A B C h1 h2,
    cases h1 with m h1,
    cases h2 with n h2,
    subst h1,
    exact (opair.ext h2).2 },
  rw [range, zmem_replacement_iff h1],
  split; intro H,
  { rcases H with ⟨z, h1, w, h2⟩,
    subst h2, existsi w, assumption },
  { cases H with z h,
    existsi opair z y,
    split, assumption, existsi z, refl }
end

theorem zmem_dom_of_opair_zmem {f : α} [is_function f] {x y : α} (H : opair x y ∈ f) : x ∈ dom f :=
zmem_dom_iff.2 ⟨_, H⟩

theorem zmem_range_of_opair_zmem {f : α} [is_function f] {x y : α} (H : opair x y ∈ f) : y ∈ range f :=
zmem_range_iff.2 ⟨_, H⟩

theorem eval_zmem_range {f : α} [is_function f] {x : α} (H : x ∈ dom f) : eval f x H ∈ range f :=
zmem_range_iff.2 ⟨_, opair_eval_zmem _⟩

variable α

def omega : α :=
comprehension ∞ (λ n, ∀ A:α, ∅ ∈ A → (∀ k, k ∈ A → succ k ∈ A) → n ∈ A)

notation `ω` := omega _

variable {α}

theorem empty_zmem_omega : (∅:α) ∈ (ω:α) :=
zmem_comprehension_iff.2 ⟨empty_zmem_infinity, λ A h1 h2, h1⟩

theorem succ_zmem_omega_of_zmem (H : x ∈ (ω:α)) : succ x ∈ (ω:α) :=
zmem_comprehension_iff.2
⟨succ_zmem_infinity_of_zmem_infinity x $ (zmem_comprehension_iff.1 H).1,
 λ A h1 h2, h2 x $ (zmem_comprehension_iff.1 H).2 A h1 h2⟩

theorem induction (p : α → Prop) (H1 : p ∅) (H2 : ∀ k, k ∈ omega α → p k → p (succ k)) (n : α) (Hn : n ∈ omega α) : p n :=
(zmem_comprehension_iff.1 $
 (zmem_comprehension_iff.1 Hn).2 (comprehension (omega α) p)
  (zmem_comprehension_iff.2 ⟨empty_zmem_omega, H1⟩)
  (λ k hk, zmem_comprehension_iff.2
   ⟨succ_zmem_omega_of_zmem $ (zmem_comprehension_iff.1 hk).1,
   H2 k (zmem_comprehension_iff.1 hk).1 (zmem_comprehension_iff.1 hk).2⟩)).2

theorem omega.structure (H : x ∈ (ω:α)) : x = ∅ ∨ ∃ y ∈ (ω:α), x = succ y :=
@induction α _ (λ z:α, z = ∅ ∨ ∃ y ∈ (ω:α), z = succ y)
  (or.inl rfl)
  (λ k hk1 hk2, or.inr ⟨k, hk1, rfl⟩)
  x H

class is_transitive (x : α) : Prop :=
(zmem_trans : ∀ m n, m ∈ n → n ∈ x → m ∈ x)

instance omega.transitive : is_transitive (ω:α) :=
{ zmem_trans := λ m n hmn hno, @induction α _ (λ z, ∀ x, x ∈ z → x ∈ (ω:α))
    (λ x hx, false.elim $ not_zmem_empty hx)
    (λ k hk1 hk2 x hx, or.cases_on (zmem_succ_iff_eq_or_zmem.1 hx)
       (λ hxk, hxk.symm ▸ hk1)
       (hk2 x))
    n hno m hmn }

variable α

def nat.to_omega : nat → α
| nat.zero     := ∅
| (nat.succ n) := succ (n.to_omega)

theorem nat.to_omega.mem_omega : ∀ n, nat.to_omega α n ∈ omega α
| nat.zero     := empty_zmem_omega
| (nat.succ n) := succ_zmem_omega_of_zmem $ nat.to_omega.mem_omega n

def nat.to_omega' : nat → {x // x ∈ omega α} :=
λ n, ⟨nat.to_omega α n, nat.to_omega.mem_omega α n⟩

theorem nat.to_omega.injective : function.injective (nat.to_omega α) :=
begin
  intros m n H,
  induction m with m ihm generalizing n H;
  induction n with n ihn,
  { refl },
  { exfalso,
    have h1 : nat.to_omega α n ∈ nat.to_omega α (nat.succ n),
    { unfold nat.to_omega,
      unfold succ,
      rw zmem_insert_iff_eq_or_zmem,
      left, refl },
    rw ← H at h1,
    exact not_zmem_empty h1 },
  { exfalso,
    have h1 : nat.to_omega α m ∈ nat.to_omega α (nat.succ m),
    { unfold nat.to_omega,
      unfold succ,
      rw zmem_insert_iff_eq_or_zmem,
      left, refl },
    rw H at h1,
    exact not_zmem_empty h1 },
  { unfold nat.to_omega at H,
    congr,
    exact ihm (succ.ext H) }
end

-- it isn't supposed to be surjective unless the model is transitive
theorem nat.to_omega.surjective_cheating : function.surjective (nat.to_omega' α) :=
begin
  intros x,
  cases x with x hx,
  dsimp [omega] at hx,
  rw zmem_comprehension_iff at hx,
  cases hx with h1 h2,
  let cheating := comprehension (omega α) (nat.to_omega α '' set.univ),
  specialize h2 cheating,
  simp [cheating, zmem_comprehension_iff] at h2,
  specialize h2 empty_zmem_omega,
  specialize h2 ⟨0, rfl⟩,
  specialize h2 (λ k hk1 ⟨n, hk2⟩, ⟨succ_zmem_omega_of_zmem hk1, nat.succ n, by rw ← hk2; refl⟩),
  rcases h2 with ⟨h2, n, h3⟩,
  existsi n,
  apply subtype.eq,
  exact h3
end

variable {α}

section erase

def erase (x y : α) : α :=
comprehension x (λ z, z ≠ y)

theorem zmem_erase_iff : z ∈ erase x y ↔ z ∈ x ∧ z ≠ y :=
zmem_comprehension_iff

theorem zmem_of_zmem_erase (H : z ∈ erase x y) : z ∈ x :=
(zmem_erase_iff.1 H).1

theorem ne_of_zmem_erase (H : z ∈ erase x y) : z ≠ y :=
(zmem_erase_iff.1 H).2

theorem zmem_erase_of_zmem_of_ne (H1 : z ∈ x) (H2 : z ≠ y) : z ∈ erase x y :=
zmem_erase_iff.2 ⟨H1, H2⟩

end erase

section recursion

variables (f A c : α) [is_function f] (H1 : dom f = prod ω A) (H2 : range f ⊆ A) (H3 : c ∈ A)

-- {(x,y) ∈ ω × A | ∃ h : ω → A, h(∅) = c ∧ (∀ m ∈ x, h(m⁺) = f(m, h(m))) ∧ h(x) = y}
def recursion : α :=
comprehension (prod ω A)
(λ z, ∃ (h x y : α) [is_function h] (H4 : z = opair x y) (H5 : dom h = ω) (H6 : range h ⊆ A)
 (H7 : opair ∅ c ∈ h) (H8: ∀ m hm hsm, m ∈ x → opair m hm ∈ h → opair (opair m hm) hsm ∈ f → opair (succ m) hsm ∈ h), z ∈ h)

include H3

theorem recursion.empty : opair ∅ c ∈ recursion f A c :=
begin
  let h : α := prod ω {c},
  have hf : is_function h,
  { split,
    { intros z hz,
      dsimp [h] at hz,
      rw [prod, zmem_comprehension_iff] at hz,
      replace hz := hz.2,
      rcases hz with ⟨x', y', _, _, h'⟩,
      exact ⟨x', y', h'⟩ },
    { intros x' hx',
      existsi c,
      rw [zmem_dom_iff] at hx',
      rcases hx' with ⟨y, hy⟩,
      dsimp [h] at hy ⊢,
      split,
      { exact zmem_prod (zmem_left_of_zmem_prod hy) mem_singleton },
      { intros y' hy',
        replace hy' := zmem_right_of_zmem_prod hy',
        rwa mem_singleton_iff at hy' } } },
  have H5 : dom h = ω,
  { apply is_extensional.ext,
    intro z,
    rw [zmem_dom_iff],
    split; intro h5,
    { cases h5 with y hy,
      exact zmem_left_of_zmem_prod hy },
    { existsi c,
      exact zmem_prod h5 mem_singleton } },
  have H6 : range h ⊆ A,
  { intros z hz,
    rw [zmem_range_iff] at hz,
    cases hz with y hy,
    replace hy := zmem_right_of_zmem_prod hy,
    rw mem_singleton_iff at hy,
    subst hy,
    exact H3 },
  have H7 : opair ∅ c ∈ h,
  { exact zmem_prod empty_zmem_omega mem_singleton },
  rw [recursion, zmem_comprehension_iff],
  split,
  { exact zmem_prod empty_zmem_omega H3 },
  { exact ⟨h, _, _, hf, rfl, H5, H6, H7, (λ m _ _ hm, false.elim $ not_zmem_empty hm), H7⟩ }
end

omit H3
include H1 H2 H3

theorem recursion.succ (h1 : opair x y ∈ recursion f A c) (h2 : opair (opair x y) z ∈ f) : opair (succ x) z ∈ recursion f A c :=
begin
  have h3 : opair x y ∈ prod ω A,
  { rw [← H1, zmem_dom_iff], exact ⟨z, h2⟩ },
  have h5 : z ∈ A,
  { apply H2, rw [zmem_range_iff], exact ⟨_, h2⟩ },
  rw [recursion, zmem_comprehension_iff] at h1,
  cases h1 with h1 h3,
  rcases h3 with ⟨h, x', y', hf, H4, H5, H6, H7, H8, H9⟩,
  have h4 : opair x y ∈ dom f,
  { rw H1, exact h1 },
  let h' : α := comprehension (prod ω A) (λ w, ∀ m n, w = opair m n → ((m = succ x ∧ n = z) ∨ (m ≠ succ x ∧ w ∈ h))),
  have hf' : is_function h' :=
  { eq_opair_of_mem := λ z hz, begin
        dsimp [h'] at hz,
        rw [zmem_comprehension_iff] at hz,
        cases hz with hz1 hz2,
        rw [prod, zmem_comprehension_iff] at hz1,
        rcases hz1.2 with ⟨x'', y'', _, _, h''⟩,
        exact ⟨x'', y'', h''⟩
      end,
    exists_unique := begin
        intros x hx,
        rw [zmem_dom_iff] at hx,
        cases hx with y hy,
        dsimp [h'] at hy,
        rw [zmem_comprehension_iff] at hy,
        cases hy with hy1 hy2,
        specialize hy2 x y rfl,
        cases hy2 with hy2 hy2;
        cases hy2 with hy2 hy3,
        { existsi y,
          split,
          { dsimp [h'],
            rw [zmem_comprehension_iff],
            split, exact hy1,
            intros m n hxy,
            cases opair.ext hxy with hxy1 hxy2,
            subst hxy1, subst hxy2,
            left, split, subst hy2, subst hy3 },
          { intros z hz,
            dsimp [h'] at hz,
            rw [zmem_comprehension_iff] at hz,
            cases hz with hz1 hz2,
            specialize hz2 _ _ rfl,
            cases hz2 with hz2 hz2;
            cases hz2 with hz2 hz3,
            { subst hy3, subst hz3 },
            { exfalso, exact hz2 hy2 } } },
        { existsi y,
          split,
          { dsimp [h'],
            rw [zmem_comprehension_iff],
            split, exact hy1,
            intros m n hxy,
            cases opair.ext hxy with hxy1 hxy2,
            subst hxy1, subst hxy2,
            right, split, exact hy2, exact hy3 },
          { intros z hz,
            dsimp [h'] at hz,
            rw [zmem_comprehension_iff] at hz,
            cases hz with hz1 hz2,
            specialize hz2 _ _ rfl,
            cases hz2 with hz2 hz2;
            cases hz2 with hz2 hz3,
            { exfalso, exact hy2 hz2 },
            { have hf1 := hf.exists_unique,
              have hf2 : x ∈ dom h,
              { rw [zmem_dom_iff], existsi y, exact hy3 },
              specialize hf1 _ hf2,
              exact unique_of_exists_unique hf1 hz3 hy3 } } }
      end },
  have H5' : dom h' = ω,
  { apply is_extensional.ext,
    intro w,
    rw [zmem_dom_iff],
    split; intro hw,
    { cases hw with w hw,
      dsimp [h'] at hw,
      rw [zmem_comprehension_iff] at hw,
      cases hw with hw1 hw2,
      exact zmem_left_of_zmem_prod hw1 },
    { cases classical.em (w = succ x) with hzk hzk,
      { existsi z,
        dsimp [h'],
        rw [zmem_comprehension_iff],
        split,
        { exact zmem_prod hw h5 },
        { intros m n hmn,
          cases opair.ext hmn with hmn1 hmn2,
          subst hmn1, subst hmn2,
          left, split, exact hzk, refl } },
      { have hf1 := hf.exists_unique,
        specialize hf1 w (H5.symm ▸ hw),
        rcases hf1 with ⟨w', hf1, hf2⟩,
        existsi w',
        dsimp [h'],
        rw [zmem_comprehension_iff],
        split,
        have hf3 : w' ∈ range h,
        { rw [zmem_range_iff], existsi w, exact hf1 },
        { exact zmem_prod hw (H6 _ hf3) },
        { intros m n hmn,
          cases opair.ext hmn with hmn1 hmn2,
          subst hmn1, subst hmn2,
          right, split, exact hzk, exact hf1 } } } },
  have H6' : range h' ⊆ A,
  { intros z hz,
    rw [zmem_range_iff] at hz,
    cases hz with w hw,
    dsimp [h'] at hw,
    rw [zmem_comprehension_iff] at hw,
    cases hw with hw1 hw2,
    specialize hw2 _ _ rfl,
    cases hw2 with hw2 hw2;
    cases hw2 with hw2 hw3,
    { subst hw3,
      apply H2,
      rw [zmem_range_iff],
      exact ⟨_, h2⟩ },
    { have hf1 : z ∈ range h,
      { rw [zmem_range_iff], existsi w, exact hw3 },
      exact H6 _ hf1 } },
  have H7' : opair ∅ c ∈ h',
  { dsimp [h'],
    rw [zmem_comprehension_iff],
    split,
    { exact zmem_prod empty_zmem_omega H3 },
    { intros m n hmn,
      cases opair.ext hmn with hmn1 hmn2,
      subst hmn1, subst hmn2,
      right, split,
      { intro hmn1,
        have hmn2 : x ∈ succ x := zmem_succ,
        rw ← hmn1 at hmn2,
        exact not_zmem_empty hmn2 },
      { exact H7 } } },
  have H8' : ∀ (m hm hsm : α), m ∈ succ x → opair m hm ∈ h' → opair (opair m hm) hsm ∈ f → opair (succ m) hsm ∈ h',
  { intros m hm hsm hm1 hm2 hm3,
    rw zmem_succ_iff_eq_or_zmem at hm1,
    cases hm1 with hm1 hm1,
    { subst hm1,
      dsimp [h'],
      rw [zmem_comprehension_iff],
      have hm4 : hsm ∈ range f,
      { rw [zmem_range_iff], existsi _, exact hm3 },
      have hm5 : m ∈ ω,
      { rw ← H5', rw [zmem_dom_iff], existsi _, exact hm2 },
      split,
      { exact zmem_prod (succ_zmem_omega_of_zmem hm5) (H2 _ hm4) },
      { intros m n hmn,
        cases opair.ext hmn with hmn1 hmn2,
        subst hmn1, subst hmn2,
        left, split, refl,
        dsimp [h'] at hm2,
        rw [zmem_comprehension_iff] at hm2,
        cases hm2 with hm8 hm6,
        specialize hm6 _ _ rfl,
        cases hm6 with hm6 hm6;
        cases hm6 with hm6 hm7,
        { exfalso,
          have hm9 : m ∈ succ m := zmem_succ,
          rw ← hm6 at hm9,
          exact not_zmem_self hm9 },
        { have hf1 := hf.exists_unique,
          have hf2 : m ∈ dom h,
          { rw H5, exact hm5 },
          specialize hf1 _ hf2,
          have hf3 := unique_of_exists_unique hf1 hm7 H9,
          subst hf3,
          have hf4 := is_function.exists_unique _ h4,
          exact unique_of_exists_unique hf4 hm3 h2 } } },
    { cases opair.ext H4 with H41 H42,
      subst H41, subst H42,
      dsimp [h'],
      rw [zmem_comprehension_iff],
      have hm4 : hsm ∈ range f,
      { rw [zmem_range_iff], existsi _, exact hm3 },
      have hm5 : m ∈ ω,
      { rw ← H5', rw [zmem_dom_iff], existsi _, exact hm2 },
      split,
      { exact zmem_prod (succ_zmem_omega_of_zmem hm5) (H2 _ hm4) },
      { intros m n hmn,
        cases opair.ext hmn with hmn1 hmn2,
        subst hmn1, subst hmn2,
        right, split,
        { intro hmk,
          replace hmk := succ.ext hmk,
          subst hmk,
          exact not_zmem_self hm1 },
        { have hm6 : opair m hm ∈ h,
          { dsimp [h'] at hm2,
            rw [zmem_comprehension_iff] at hm2,
            cases hm2 with hm8 hm6,
            specialize hm6 _ _ rfl,
            cases hm6 with hm6 hm6;
            cases hm6 with hm6 hm7,
            { exfalso,
              subst hm6,
              apply not_zmem_and_zmem hm1 zmem_succ },
            { exact hm7 } },
          exact H8 _ _ _ hm1 hm6 hm3 } } } },
  have H9' : opair (succ x) z ∈ h',
  { dsimp [h'],
    rw [zmem_comprehension_iff],
    split,
    { exact zmem_prod (succ_zmem_omega_of_zmem $ zmem_left_of_zmem_prod h3) h5 },
    { intros m n hmn,
      cases opair.ext hmn with hmn1 hmn2,
      subst hmn1, subst hmn2,
      left, split, refl, refl } },
  rw [recursion, zmem_comprehension_iff],
  split,
  { exact zmem_prod (succ_zmem_omega_of_zmem $ zmem_left_of_zmem_prod h3) h5 },
  { exact ⟨h', _, _, hf', rfl, H5', H6', H7', H8', H9'⟩ }
end

theorem recursion.dom_omega (n : α) (Hn : n ∈ (ω:α)) : ∃! y, opair n y ∈ recursion f A c :=
begin
  apply @induction _ _ _ _ _ n Hn,
  { existsi c,
    split,
    { exact recursion.empty f A c H3 },
    { intros y h1,
      rw [recursion, zmem_comprehension_iff] at h1,
      rcases h1 with ⟨h1, h, x', y', hf, H4, H5, H6, H7, H8, H9⟩,
      have hf1 := hf.exists_unique,
      specialize hf1 ∅ (H5.symm ▸ empty_zmem_omega),
      exact unique_of_exists_unique hf1 H9 H7 } },
  { intros k hk h1,
    rcases h1 with ⟨y, h1, h2⟩,
    have h4 : opair k y ∈ dom f,
    { rw [recursion, zmem_comprehension_iff] at h1,
      rw H1, exact h1.1 },
    existsi (eval f (opair k y) h4),
    split,
    { exact recursion.succ f A c H1 H2 H3 h1 (opair_eval_zmem h4) },
    { intros z hz,
      apply eval_unique f _ z h4,
      rw [recursion, zmem_comprehension_iff] at hz,
      rcases hz with ⟨hz1, h'', x'', y'', hf'', H4'', H5'', H6'', H7'', H8'', H9''⟩,
      cases opair.ext H4'' with H41'' H42'',
      subst H41'', subst H42'',
      rw [recursion, zmem_comprehension_iff] at h1,
      cases h1 with h1 h3,
      rcases h3 with ⟨h, x', y', hf, H4, H5, H6, H7, H8, H9⟩,      cases opair.ext H4 with H41 H42,
      subst H41, subst H42,
      cases omega.structure hk with h3 h3,
      { subst h3,
        have hf1 := hf.exists_unique,
        specialize hf1 ∅ (H5.symm ▸ empty_zmem_omega),
        have hf2 := unique_of_exists_unique hf1 H9 H7,
        subst hf2,
        specialize H8'' ∅ _ _ zmem_succ H7'' (opair_eval_zmem h4),
        have hf3 := hf''.exists_unique,
        specialize hf3 (succ ∅) (H5''.symm ▸ succ_zmem_omega_of_zmem empty_zmem_omega),
        have hf2 := unique_of_exists_unique hf3 H8'' H9'',
        subst hf2,
        apply opair_eval_zmem },
      { rcases h3 with ⟨k, H, hk⟩, subst hk,
        have h5 : succ k ∈ dom h'',
        { rw H5'', exact hk },
        have h6 : opair (succ k) (@@eval _ h'' hf'' (succ k) h5) ∈ recursion f A c,
        { rw [recursion, zmem_comprehension_iff],
          split,
          { exact zmem_prod hk (H6'' _ $ @eval_zmem_range _ _ _ hf'' _ _) },
          { exact ⟨h'', _, _, hf'', rfl, H5'', H6'', H7'',
              (λ m hm hsm hm1 hm2 hm3, H8'' m hm hsm (zmem_succ_of_zmem hm1) hm2 hm3),
              @opair_eval_zmem _ _ _ hf'' _ _⟩ } },
        specialize H8'' _ _ _ zmem_succ (@opair_eval_zmem _ _ _ hf'' _ h5)
          (opair_eval_zmem (H1.symm ▸ zmem_prod hk (H6'' _ $ @eval_zmem_range _ _ _ hf'' _ _))),
        specialize h2 _ h6,
        subst h2,
        have hf3 := hf''.exists_unique,
        specialize hf3 (succ (succ k)) (H5''.symm ▸ succ_zmem_omega_of_zmem hk),
        have hf2 := unique_of_exists_unique hf3 H8'' H9'',
        subst hf2,
        apply opair_eval_zmem } } }
end

instance recursion.is_function : is_function (recursion f A c) :=
{ eq_opair_of_mem := λ z hz, let ⟨x, y, _, _, h⟩ := (zmem_comprehension_iff.1 (zmem_comprehension_iff.1 hz).1).2 in ⟨x, y, h⟩,
  exists_unique := λ x hx, begin
    rw [zmem_dom_iff] at hx,
    cases hx with w hw,
    rw [recursion, zmem_comprehension_iff] at hw,
    have hx : x ∈ ω := zmem_left_of_zmem_prod hw.1,
    exact recursion.dom_omega f A c H1 H2 H3 x hx
  end }

theorem recursion.dom : dom (recursion f A c) = ω :=
begin
  apply is_extensional.ext,
  intro n,
  rw [zmem_dom_iff],
  split; intro hn,
  { cases hn with y hy,
    rw [recursion, zmem_comprehension_iff] at hy,
    exact zmem_left_of_zmem_prod hy.1 },
  { rcases recursion.dom_omega f A c H1 H2 H3 n hn with ⟨y, h1, h2⟩,
    exact ⟨y, h1⟩ }
end

theorem recursion.range : range (recursion f A c) ⊆ A :=
begin
  intros z hz,
  rw [zmem_range_iff] at hz,
  cases hz with n hn,
  rw [recursion, zmem_comprehension_iff] at hn,
  exact zmem_right_of_zmem_prod hn.1
end

-- recursion theorem:
-- for any function f : ω×A → A and c ∈ A, there is a unique function h : ω → A such that:
-- 1. h(0) = c
-- 2. h(m⁺) = f(m,h(m))
-- (I left uniqueness unproved)

end recursion

section transitive_closure

def transitive_closure (z : α) : α :=
sUnion $ replacement ω (λ x y, ∃ (A : α) (H1 : x ∈ (ω:α)) (H2 : ∀ p q r, opair p q ∈ A → opair p r ∈ A → q = r)
  (H3 : ∀ p q, opair p q ∈ A → p ∈ succ x) (H4 : ∀ p, p ∈ x → ∃ q, opair p q ∈ A) (H5 : opair ∅ z ∈ A)
  (H6 : ∀ p q, p ∈ x → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A), opair x y ∈ A)

theorem transitive_closure.aux.empty : ∃ (A : α) (H1 : (∅:α) ∈ (ω:α)) (H2 : ∀ (p q r : α), opair p q ∈ A → opair p r ∈ A → q = r)
    (H3 : ∀ (p q : α), opair p q ∈ A → p ∈ succ (∅:α))
    (H4 : ∀ (p : α), p ∈ (∅:α) → (∃ (q : α), opair p q ∈ A)) (H5 : opair ∅ z ∈ A)
    (H6 : ∀ (p q : α), p ∈ (∅:α) → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A),
    opair ∅ z ∈ A :=
begin
  have H2 : ∀ (p q r : α), opair p q ∈ {opair ∅ z} → opair p r ∈ {opair ∅ z} → q = r,
  { intros p q r hpq hpr,
    rw mem_singleton_iff at hpq hpr,
    have h1 := (opair.ext hpq).2,
    have h2 := (opair.ext hpr).2,
    subst h1, subst h2 },
  have H3 : ∀ (p q : α), opair p q ∈ {opair ∅ z} → p ∈ succ (∅:α),
  { intros p q h,
    rw mem_singleton_iff at h,
    rw (opair.ext h).1,
    exact zmem_succ },
  exact ⟨{opair ∅ z}, empty_zmem_omega, H2, H3, (λ p hp, false.elim $ not_zmem_empty hp),
    mem_singleton, (λ p q hp, false.elim $ not_zmem_empty hp), mem_singleton⟩
end

theorem transitive_closure.aux.succ {k : α} (hk : k ∈ (ω:α)) :
  (∃ (A : α) (H1 : k ∈ (ω:α)) (H2 : ∀ (p q r : α), opair p q ∈ A → opair p r ∈ A → q = r)
     (H3 : ∀ (p q : α), opair p q ∈ A → p ∈ succ k)
     (H4 : ∀ (p : α), p ∈ k → (∃ (q : α), opair p q ∈ A)) (H5 : opair ∅ z ∈ A)
     (H6 : ∀ (p q : α), p ∈ k → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A),
     opair k y ∈ A)
  →
  (∃ (A : α) (H1 : succ k ∈ (ω:α)) (H2 : ∀ (p q r : α), opair p q ∈ A → opair p r ∈ A → q = r)
     (H3 : ∀ (p q : α), opair p q ∈ A → p ∈ succ (succ k))
     (H4 : ∀ (p : α), p ∈ succ k → (∃ (q : α), opair p q ∈ A)) (H5 : opair ∅ z ∈ A)
     (H6 : ∀ (p q : α), p ∈ succ k → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A),
     opair (succ k) (sUnion y) ∈ A) :=
begin
  intro h1,
  rcases h1 with ⟨A, H1, H2, H3, H4, H5, H6, H7⟩,
  have H2' : ∀ (p q r : α),
    opair p q ∈ has_insert.insert (opair (succ k) (sUnion y)) A →
    opair p r ∈ has_insert.insert (opair (succ k) (sUnion y)) A →
    q = r,
  { intros p q r hpq hpr,
    rw zmem_insert_iff_eq_or_zmem at hpq hpr,
    cases hpq; cases hpr,
    { have h1 := (opair.ext hpq).2,
      have h2 := (opair.ext hpr).2,
      subst h1, subst h2 },
    { exfalso,
      have h1 := (opair.ext hpq).1,
      subst h1,
      exact not_zmem_self (H3 _ _ hpr) },
    { exfalso,
      have h1 := (opair.ext hpr).1,
      subst h1,
      exact not_zmem_self (H3 _ _ hpq) },
    { exact H2 _ _ _ hpq hpr } },
  have H3' : ∀ (p q : α), opair p q ∈ has_insert.insert (opair (succ k) (sUnion y)) A → p ∈ succ (succ k),
  { intros p q h,
    rw zmem_insert_iff_eq_or_zmem at h,
    cases h with h h,
    { rw (opair.ext h).1,
      exact zmem_succ },
    { exact zmem_succ_of_zmem (H3 _ _ h) } },
  have H4' : ∀ (p : α), p ∈ succ k → (∃ (q : α), opair p q ∈ has_insert.insert (opair (succ k) (sUnion y)) A),
  { intros p hp,
    rw zmem_succ_iff_eq_or_zmem at hp,
    cases hp with hp hp,
    { subst hp,
      existsi y,
      exact zmem_insert_of_zmem H7 },
    { cases H4 p hp with q hq,
      exact ⟨q, zmem_insert_of_zmem hq⟩ } },
  have H6' : ∀ (p q : α), p ∈ succ k →
    opair p q ∈ has_insert.insert (opair (succ k) (sUnion y)) A →
    opair (succ p) (sUnion q) ∈ has_insert.insert (opair (succ k) (sUnion y)) A,
  { intros p q hp hpq,
    rw zmem_succ_iff_eq_or_zmem at hp,
    rw zmem_insert_iff_eq_or_zmem at hpq,
    cases hp with hp hp;
    cases hpq with hpq hpq,
    { subst hp,
      exfalso,
      have h1 : p ∈ succ p := zmem_succ,
      rw ← (opair.ext hpq).1 at h1,
      exact not_zmem_self h1 },
    { subst hp,
      rw H2 _ _ _ hpq H7,
      exact zmem_insert },
    { exfalso,
      apply not_zmem_and_zmem hp,
      rw (opair.ext hpq).1,
      exact zmem_succ },
    { exact zmem_insert_of_zmem (H6 _ _ hp hpq) } },
  exact ⟨has_insert.insert (opair (succ k) (sUnion y)) A,
  succ_zmem_omega_of_zmem hk, H2', H3', H4',
  zmem_insert_of_zmem H5, H6', zmem_insert⟩
end

theorem transitive_closure.aux : ∀ x, x ∈ (ω:α) → ∃! y,
  ∃ (A : α) (H1 : x ∈ (ω:α)) (H2 : ∀ p q r, opair p q ∈ A → opair p r ∈ A → q = r)
  (H3 : ∀ p q, opair p q ∈ A → p ∈ succ x) (H4 : ∀ p, p ∈ x → ∃ q, opair p q ∈ A) (H5 : opair ∅ z ∈ A)
  (H6 : ∀ p q, p ∈ x → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A), opair x y ∈ A :=
begin
  apply induction,
  { existsi z,
    split,
    { exact transitive_closure.aux.empty },
    { intros y hy,
      rcases hy with ⟨A, H1, H2, H3, H4, H5, H6, H7⟩,
      exact H2 _ _ _ H7 H5 } },
  { intros k hk ih,
    rcases ih with ⟨y, h1, h2⟩,
    existsi sUnion y,
    split,
    { exact transitive_closure.aux.succ hk h1 },
    { intros w hw,
      rcases hw with ⟨A', H1', H2', H3', H4', H5', H6', H7'⟩,
      cases H4' _ zmem_succ with q hq,
      have h := H2' _ _ _ H7' (H6' _ _ zmem_succ hq), subst h,
      congr,
      have H3'' : ∀ (p q_1 : α), opair p q_1 ∈ erase A' (opair (succ k) (sUnion q)) → p ∈ succ k,
      { intros p q h,
        have h1 := H3' _ _ (zmem_of_zmem_erase h),
        cases zmem_succ_iff_eq_or_zmem.1 h1 with h3 h3,
        { exfalso, subst h3,
          have h3 := H2' _ _ _ (H6' _ _ zmem_succ hq) (zmem_of_zmem_erase h), subst h3,
          exact ne_of_zmem_erase h rfl },
        { exact h3 } },
      have H4'' : ∀ (p : α), p ∈ k → (∃ (q_1 : α), opair p q_1 ∈ erase A' (opair (succ k) (sUnion q))),
      { intros p hp,
        cases H4' p (zmem_succ_of_zmem hp) with q hq,
        existsi q,
        apply zmem_erase_of_zmem_of_ne hq,
        intro h,
        rw (opair.ext h).1 at hp,
        exact not_zmem_and_zmem hp zmem_succ },
      have H5'' : opair ∅ z ∈ erase A' (opair (succ k) (sUnion q)),
      { apply zmem_erase_of_zmem_of_ne H5',
        intro h,
        have h1 : k ∈ succ k := zmem_succ,
        rw ← (opair.ext h).1 at h1,
        exact not_zmem_empty h1 },
      have H6'' : ∀ (p q_1 : α), p ∈ k →
        opair p q_1 ∈ erase A' (opair (succ k) (sUnion q)) →
        opair (succ p) (sUnion q_1) ∈ erase A' (opair (succ k) (sUnion q)),
      { intros p q hp hpq,
        apply zmem_erase_of_zmem_of_ne,
        { exact H6' _ _ (zmem_succ_of_zmem hp) (zmem_of_zmem_erase hpq) },
        { intro h,
          rw succ.ext (opair.ext h).1 at hp,
          exact not_zmem_self hp } },
      have H7'' : opair k q ∈ erase A' (opair (succ k) (sUnion q)),
      { apply zmem_erase_of_zmem_of_ne hq,
        intro h,
        have h1 : k ∈ succ k := zmem_succ,
        rw ← (opair.ext h).1 at h1,
        exact not_zmem_self h1 },
      exact h2 q ⟨erase A' (opair (succ k) (sUnion q)), hk,
        λ p q r hpq hpr, H2' p q r (zmem_of_zmem_erase hpq) (zmem_of_zmem_erase hpr),
        H3'', H4'', H5'', H6'', H7''⟩ } }
end

theorem transitive_closure.aux.iff {w : α} : w ∈ transitive_closure z ↔ ∃ y, w ∈ y ∧ ∃ x, x ∈ (ω:α) ∧
  ∃ (A : α) (H1 : x ∈ (ω:α)) (H2 : ∀ p q r, opair p q ∈ A → opair p r ∈ A → q = r)
  (H3 : ∀ p q, opair p q ∈ A → p ∈ succ x) (H4 : ∀ p, p ∈ x → ∃ q, opair p q ∈ A) (H5 : opair ∅ z ∈ A)
  (H6 : ∀ p q, p ∈ x → opair p q ∈ A → opair (succ p) (sUnion q) ∈ A), opair x y ∈ A :=
begin
  rw [transitive_closure],
  rw [zmem_sUnion_iff_zmem_zmem],
  split; intro h; rcases h with ⟨h1, h2, h3⟩; refine ⟨h1, h2, _⟩;
  rwa [zmem_replacement_iff] <|> rwa [zmem_replacement_iff] at h3;
  { intros A B C hab hac,
    have hab1 := hab,
    rcases hab1 with ⟨_, h, _⟩,
    exact unique_of_exists_unique (transitive_closure.aux _ h) hab hac }
end

variable z

theorem transitive_closure.subset : z ⊆ transitive_closure z :=
λ w hw, transitive_closure.aux.iff.2 ⟨z, hw, ∅, empty_zmem_omega, transitive_closure.aux.empty⟩

instance transitive_closure.is_transitive : is_transitive (transitive_closure z) :=
{ zmem_trans := begin
    intros m n hmn hn,
    rw transitive_closure.aux.iff at hn ⊢,
    rcases hn with ⟨y, hny, k, hk, hn⟩,
    refine ⟨_, zmem_sUnion_iff_zmem_zmem.2 ⟨n, hmn, hny⟩, _, succ_zmem_omega_of_zmem hk, transitive_closure.aux.succ hk hn⟩
  end }

theorem transitive_closure.UMP (w : α) (H : z ⊆ w) [is_transitive w] : transitive_closure z ⊆ w :=
begin
  intros x hx,
  rw [transitive_closure.aux.iff] at hx,
  rcases hx with ⟨y, hxy, k, hk, A, H1, H2, H3, H4, H5, H6, H7⟩,
  revert x y A,
  apply induction _ _ _ k hk,
  { intros x y A hxy H2 H3 H4 H5 H6 H7,
    specialize H2 _ _ _ H7 H5,
    subst H2,
    exact H _ hxy },
  { clear hk H1 k,
    intros k hk ih x y A hxy H2 H3 H4 H5 H6 H7,
    cases H4 _ zmem_succ with q hq,
    have H2subst := H2 _ _ _ H7 (H6 _ _ zmem_succ hq),
    subst H2subst,
    rw zmem_sUnion_iff_zmem_zmem at hxy,
    rcases hxy with ⟨t, hxt, hty⟩,
    have H3' : ∀ (p q_1 : α), opair p q_1 ∈ erase A (opair (succ k) (sUnion q)) → p ∈ succ k,
    { intros p q h,
      have h1 := H3 _ _ (zmem_of_zmem_erase h),
      cases zmem_succ_iff_eq_or_zmem.1 h1 with h3 h3,
      { exfalso, subst h3,
        have h3 := H2 _ _ _ (H6 _ _ zmem_succ hq) (zmem_of_zmem_erase h), subst h3,
        exact ne_of_zmem_erase h rfl },
      { exact h3 } },
    have H4' : ∀ (p : α), p ∈ k → (∃ (q_1 : α), opair p q_1 ∈ erase A (opair (succ k) (sUnion q))),
    { intros p hp,
      cases H4 p (zmem_succ_of_zmem hp) with q hq,
      existsi q,
      apply zmem_erase_of_zmem_of_ne hq,
      intro h,
      rw (opair.ext h).1 at hp,
      exact not_zmem_and_zmem hp zmem_succ },
    have H5' : opair ∅ z ∈ erase A (opair (succ k) (sUnion q)),
    { apply zmem_erase_of_zmem_of_ne H5,
      intro h,
      have h1 : k ∈ succ k := zmem_succ,
      rw ← (opair.ext h).1 at h1,
      exact not_zmem_empty h1 },
    have H6' : ∀ (p q_1 : α), p ∈ k →
      opair p q_1 ∈ erase A (opair (succ k) (sUnion q)) →
      opair (succ p) (sUnion q_1) ∈ erase A (opair (succ k) (sUnion q)),
    { intros p q hp hpq,
      apply zmem_erase_of_zmem_of_ne,
      { exact H6 _ _ (zmem_succ_of_zmem hp) (zmem_of_zmem_erase hpq) },
      { intro h,
        rw succ.ext (opair.ext h).1 at hp,
        exact not_zmem_self hp } },
    have H7' : opair k q ∈ erase A (opair (succ k) (sUnion q)),
    { apply zmem_erase_of_zmem_of_ne hq,
      intro h,
      have h1 : k ∈ succ k := zmem_succ,
      rw ← (opair.ext h).1 at h1,
      exact not_zmem_self h1 },
    specialize ih t q (erase A (opair (succ k) (sUnion q))) hty
      (λ p q r hpq hpr, H2 p q r (zmem_of_zmem_erase hpq) (zmem_of_zmem_erase hpr))
      H3' H4' H5' H6' H7',
    exact is_transitive.zmem_trans _ _ hxt ih }
end

end transitive_closure

#check transitive_closure.UMP

end zf

end zfc
