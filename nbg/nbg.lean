universes u v

class nbg (α : Type u) (β : Type v) :=
(set_mem_set : α → α → Prop)
(set_mem_class : α → β → Prop)
(set_ext : ∀ x y, (∀ z, set_mem_set z x ↔ set_mem_set z y) → x = y)
(set_pair : α → α → α)
(set_pair_prop : ∀ x y z, set_mem_set z (set_pair x y) ↔ (z = x ∨ z = y))
(set_union : α → α)
(set_union_prop : ∀ x y, set_mem_set y (set_union x) ↔ ∃ t, set_mem_set y t ∧ set_mem_set t x)
(set_powerset : α → α)
(set_powerset_prop : ∀ x y, set_mem_set y (set_union x) ↔ ∀ z, set_mem_set z y → set_mem_set z x)
(set_empty : α)
(set_empty_prop : ∀ x, ¬set_mem_set x set_empty)
(set_infinity : α)
(set_infinity_prop_empty : set_mem_set set_empty set_infinity)
(set_infinity_prop_succ : ∀ x, set_mem_set x set_infinity → set_mem_set (set_union (set_pair x (set_pair x x))) set_infinity)
(class_ext : ∀ X Y, (∀ z, set_mem_class z X ↔ set_mem_class z Y) → X = Y)
(class_reg : β → α)
(class_reg_prop : ∀ X, set_mem_class (class_reg X) X ∧ ∀ z, ¬(set_mem_class z X ∧ set_mem_set z (class_reg X)))
(limitation : ∀ C, xor (∃ c, ∀ z, set_mem_set z c ↔ set_mem_class z C) (∃ F, (∀ y, (∃ x, set_mem_class x C ∧ set_mem_class (set_pair (set_pair x x) (set_pair x y)) F)) ∧ (∀ x y z, set_mem_class x C → set_mem_class (set_pair (set_pair x x) (set_pair x y)) F → set_mem_class (set_pair (set_pair x x) (set_pair x z)) F → y = z)))
(set_to_class : α → β)
(set_to_class_prop : ∀ x y, set_mem_set y x ↔ set_mem_class y (set_to_class x))
(class_comp : β → β)
(class_comp_prop : ∀ X y, xor (set_mem_class y X) (set_mem_class y (class_comp X)))
(class_int : β → β → β)
(class_int_prop : ∀ X Y z, set_mem_class z (class_int X Y) ↔ set_mem_class z X ∧ set_mem_class z Y)
(class_prod : β → β → β)
(class_prod_prop : ∀ X Y z, set_mem_class z (class_prod X Y) ↔ ∃ x y, set_mem_class x X ∧ set_mem_class y Y ∧ z = (set_pair (set_pair x x) (set_pair x y)))
(class_prod_comm : β → β)
(class_prod_comm_prop : ∀ X y, set_mem_class y (class_prod_comm X) ↔ ∃ a b, set_mem_class (set_pair (set_pair a a) (set_pair a b)) X ∧ y = set_pair (set_pair b b) (set_pair b a))
(class_prod_comm' : β → β)
(class_prod_comm'_prop : ∀ X y, set_mem_class y (class_prod_comm' X) ↔ ∃ a b c, set_mem_class (set_pair (set_pair a a) (set_pair a (set_pair (set_pair b b) (set_pair b c)))) X ∧ y = set_pair (set_pair b b) (set_pair b (set_pair (set_pair a a) (set_pair a c))))
(class_prod_assoc : β → β)
(class_prod_assoc_prop : ∀ X y, set_mem_class y (class_prod_assoc X) ↔ ∃ a b c, set_mem_class (set_pair (set_pair a a) (set_pair a (set_pair (set_pair b b) (set_pair b c)))) X ∧ y = set_pair (set_pair (set_pair (set_pair a a) (set_pair a b)) (set_pair (set_pair a a) (set_pair a b))) (set_pair (set_pair (set_pair a a) (set_pair a b)) c))
(class_prod_assoc' : β → β)
(class_prod_assoc'_prop : ∀ X y, set_mem_class y (class_prod_assoc' X) ↔ ∃ a b c d, set_mem_class (set_pair (set_pair d d) (set_pair d (set_pair (set_pair a a) (set_pair a (set_pair (set_pair b b) (set_pair b c)))))) X ∧ y = set_pair (set_pair d d) (set_pair d (set_pair (set_pair (set_pair (set_pair a a) (set_pair a b)) (set_pair (set_pair a a) (set_pair a b))) (set_pair (set_pair (set_pair a a) (set_pair a b)) c))))
(class_range : β → β)
(class_range_prop : ∀ X y, set_mem_class y (class_range X) ↔ ∃ x, set_mem_class (set_pair (set_pair x x) (set_pair x y)) X)
(class_mem : β)
(class_mem_prop : ∀ z, set_mem_class z class_mem ↔ ∃ x y, set_mem_set x y ∧ z = set_pair (set_pair x x) (set_pair x y))
(class_eq : β)
(class_eq_prop : ∀ z, set_mem_class z class_eq ↔ ∃ x, z = set_pair (set_pair x x) (set_pair x x))

theorem classical.dne (p : Prop) : ¬¬p → p
| hp := or.cases_on (classical.em p) id (λ h, false.elim (hp h))

theorem xor.not_right_of_left {p q : Prop} : xor p q → p → ¬q
| hpq hp := or.cases_on hpq (λ h, h.2) (λ h, false.rec ¬q $ h.2 hp)

theorem xor.right_of_not_left {p q : Prop} : xor p q → ¬p → q
| hpq hp := or.cases_on hpq (λ h, false.rec q $ hp h.1) (λ h, h.1)

theorem xor.not_left_of_right {p q : Prop} : xor p q → q → ¬p
| hpq hq := or.cases_on hpq (λ h, false.rec ¬p $ h.2 hq) (λ h, h.2)

theorem xor.left_of_not_right {p q : Prop} : xor p q → ¬q → p
| hpq hq := or.cases_on hpq (λ h, h.1) (λ h, false.rec p $ hq h.1)

namespace nbg

variables {α : Type u} (β : Type v) [nbg α β] (x y z a b c d : α) (X Y Z A B C D : β)

def pair := set_pair β (set_pair β x x) (set_pair β x y)

variables {β x y z a b c d X Y Z A B C D}

theorem set_pair_left : set_mem_set β x (set_pair β x y) :=
begin
  apply (set_pair_prop _ _ _ _).2, left, refl
end

theorem set_pair_right : set_mem_set β y (set_pair β x y) :=
begin
  apply (set_pair_prop _ _ _ _).2, right, refl
end

theorem pair_ext : pair β a b = pair β c d → a = c ∧ b = d :=
begin
  intro h,
  have hac : a = c,
  have : set_mem_set β (set_pair β a a) (pair β a b),
  apply set_pair_left,
  rw h at this,
  cases (set_pair_prop _ _ _ _).1 this,
  have : set_mem_set β a (set_pair β a a),
  apply set_pair_left,
  rw h_1 at this,
  cases (set_pair_prop _ _ _ _).1 this,
  exact h_2, exact h_2,
  have : set_mem_set β a (set_pair β a a),
  apply set_pair_left,
  rw h_1 at this,
  cases (set_pair_prop _ _ _ _).1 this,
  exact h_2,
  rw h_2,
  rw h_2 at h_1,
  have : set_mem_set β c (set_pair β c d),
  apply set_pair_left,
  rw ←h_1 at this,
  cases (set_pair_prop _ _ _ _).1 this,
  rw h_3, rw h_3,
  split, apply hac,
  have : set_mem_set β (set_pair β a b) (pair β a b),
  apply set_pair_right,
  rw h at this,
  cases (set_pair_prop _ _ _ _).1 this,
  have : set_mem_set β (set_pair β c d) (pair β c d),
  apply set_pair_right,
  rw ←h at this,
  cases (set_pair_prop _ _ _ _).1 this,
  have : set_mem_set β d (set_pair β c d),
  apply set_pair_right,
  rw h_2 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  rw this,
  have : set_mem_set β a (set_pair β a b),
  apply set_pair_left,
  rw h_1 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  rw this,
  have : set_mem_set β b (set_pair β a b),
  apply set_pair_right,
  rw h_1 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  rw this,
  have : set_mem_set β a (set_pair β a b),
  apply set_pair_left,
  rw h_1 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  have : set_mem_set β b (set_pair β a b),
  apply set_pair_right,
  rw h_1 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  dedup,
  rw [this_3, this_5] at h_2,
  rw this_5,
  have : set_mem_set β d (set_pair β c d),
  apply set_pair_right,
  rw h_2 at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  rw this,
  have : set_mem_set β b (set_pair β a b),
  apply set_pair_right,
  rw h_1 at this,
  cases (set_pair_prop _ _ _ _).1 this,
  rw [hac,h_2] at h,
  rw h_2,
  have : set_mem_set β (set_pair β c d) (pair β c d),
  apply set_pair_right,
  rw ←h at this,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this),
  have : set_mem_set β d (set_pair β c d),
  apply set_pair_right,
  dedup,
  rw this_3 at this_4,
  have := (or_self _).1 ((set_pair_prop _ _ _ _).1 this_4),
  rw this,
  exact h_2
end

theorem class_int_ext : set_mem_class x X → set_mem_class x Y → set_mem_class x (class_int α X Y)
| hX hY := (class_int_prop X Y x).2 ⟨hX, hY⟩

theorem class_prod_ext : set_mem_class x X → set_mem_class y Y → set_mem_class (pair β x y) (class_prod α X Y)
| hX hY := (class_prod_prop X Y (pair β x y)).2 ⟨x, y, hX, hY, rfl⟩

theorem class_prod_left : set_mem_class (pair β x y) (class_prod α X Y) → set_mem_class x X
| hxy :=
begin
  have hab := (class_prod_prop X Y (pair β x y)).1 hxy,
  cases hab with a hb,
  cases hb with b h,
  cases pair_ext h.2.2,
  exact left.symm ▸ h.1
end

theorem class_prod_right : set_mem_class (pair β x y) (class_prod α X Y) → set_mem_class y Y
| hxy :=
begin
  have hab := (class_prod_prop X Y (pair β x y)).1 hxy,
  cases hab with a hb,
  cases hb with b h,
  cases pair_ext h.2.2,
  exact right.symm ▸ h.2.1
end

theorem class_prod_split : set_mem_class (pair β x y) (class_prod α X Y) → set_mem_class x X ∧ set_mem_class y Y
| hxy := ⟨class_prod_left hxy, class_prod_right hxy⟩

theorem class_prod_comm_ext : set_mem_class (pair β x y) X → set_mem_class (pair β y x) (class_prod_comm α X)
| hxy := (class_prod_comm_prop X (pair β y x)).2 ⟨x, y, hxy, rfl⟩

theorem class_prod_of_prod_comm : set_mem_class (pair β y x) (class_prod_comm α X) → set_mem_class (pair β x y) X
| hyx :=
begin
  have hab := (class_prod_comm_prop X (pair β y x)).1 hyx,
  cases hab with a hb,
  cases hb with b h,
  cases pair_ext h.2,
  exact left.symm ▸ right.symm ▸ h.1
end

theorem class_prod_comm'_ext : set_mem_class (pair β x (pair β y z)) X → set_mem_class (pair β y (pair β x z)) (class_prod_comm' α X)
| hxyz := (class_prod_comm'_prop X (pair β y (pair β x z))).2 ⟨x, y, z, hxyz, rfl⟩

theorem class_prod_of_prod_comm' : set_mem_class (pair β y (pair β x z)) (class_prod_comm' α X) → set_mem_class (pair β x (pair β y z)) X
| hyxz :=
begin
  have habc := (class_prod_comm'_prop X (pair β y (pair β x z))).1 hyxz,
  cases habc with a hbc,
  cases hbc with b hc,
  cases hc with c h,
  cases pair_ext h.2,
  cases pair_ext right,
  exact left.symm ▸ left_1.symm ▸ right_1.symm ▸ h.1
end

theorem class_prod_assoc_ext : set_mem_class (pair β x (pair β y z)) X → set_mem_class (pair β (pair β x y) z) (class_prod_assoc α X)
| hxyz := (class_prod_assoc_prop X (pair β (pair β x y) z)).2 ⟨x, y, z, hxyz, rfl⟩

theorem class_prod_of_prod_assoc : set_mem_class (pair β (pair β x y) z) (class_prod_assoc α X) → set_mem_class (pair β x (pair β y z)) X
| hxyz :=
begin
  have habc := (class_prod_assoc_prop X (pair β (pair β x y) z)).1 hxyz,
  cases habc with a hbc,
  cases hbc with b hc,
  cases hc with c h,
  cases pair_ext h.2,
  cases pair_ext left,
  exact right.symm ▸ left_1.symm ▸ right_1.symm ▸ h.1
end

theorem class_prod_assoc'_ext : set_mem_class (pair β d (pair β a (pair β b c))) X → set_mem_class (pair β d (pair β (pair β a b) c)) (class_prod_assoc' α X)
| habcd := (class_prod_assoc'_prop X _).2 ⟨a, b, c, d, habcd, rfl⟩

theorem class_prod_of_prod_assoc' : set_mem_class (pair β d (pair β (pair β a b) c)) (class_prod_assoc' α X) → set_mem_class (pair β d (pair β a (pair β b c))) X
| hdabc :=
begin
  have hdabc := (class_prod_assoc'_prop X _).1 hdabc,
  cases hdabc with d habc,
  cases habc with a hbc,
  cases hbc with b hc,
  cases hc with c h,
  cases pair_ext h.2,
  cases pair_ext right,
  cases pair_ext left_1,
  exact left.symm ▸ right_1.symm ▸ left_2.symm ▸ right_2.symm ▸ h.1
end

theorem class_range_ext : set_mem_class (pair β x y) X → set_mem_class y (class_range α X)
| hxy := (class_range_prop X y).2 ⟨x, hxy⟩

theorem class_mem_ext : set_mem_set β x y → set_mem_class (pair β x y) (class_mem α β)
| hxy := (class_mem_prop β (pair β x y)).2 ⟨x, y, hxy, rfl⟩

theorem class_mem_of_mem : set_mem_class (pair β x y) (class_mem α β) → set_mem_set β x y
| hxy :=
begin
  have hab := (class_mem_prop β (pair β x y)).1 hxy,
  cases hab with a hb,
  cases hb with b h,
  cases pair_ext h.2,
  exact left.symm ▸ right.symm ▸ h.1
end

theorem class_eq_ext : x = y → set_mem_class (pair β x y) (class_eq α β)
| hxy := (class_eq_prop β (pair β x y)).2 ⟨x, hxy ▸ rfl⟩

theorem class_eq_of_eq : set_mem_class (pair β x y) (class_eq α β) → x = y
| hxy :=
begin
  have ha := (class_eq_prop β (pair β x y)).1 hxy,
  cases ha with a h,
  cases pair_ext h,
  exact right.symm ▸ left
end

theorem set_to_class_ext : set_mem_set β x y → set_mem_class x (set_to_class β y) :=
(set_to_class_prop β y x).1

theorem class_mem_of_to_class : set_mem_class x (set_to_class β y) → set_mem_set β x y :=
(set_to_class_prop β y x).2

variables (α β)
def class_univ : β := class_comp α (set_to_class β (set_empty α β))
variables {α β}

theorem class_univ_prop : set_mem_class x (class_univ α β) :=
begin
  cases class_comp_prop (set_to_class β (set_empty α β)) x,
  cases h,
  exfalso,
  rw ←set_to_class_prop at h_left,
  apply (set_empty_prop β) x, exact h_left,
  cases h,
  exact h_left
end

theorem no_set_univ : ¬∃ x:α, ∀ y, set_mem_set β y x :=
begin
  intro h,
  cases h,
  apply (limitation α $ set_to_class β h_w).not_left_of_right,
  existsi class_eq α β,
  split,
  intro y,
  existsi y,
  split,
  apply set_to_class_ext,
  exact h_h y,
  apply class_eq_ext,
  refl,
  intros x y z hx hxy hxz,
  rw ←class_eq_of_eq hxy,
  rw ←class_eq_of_eq hxz,
  existsi h_w,
  exact set_to_class_prop β h_w
end

theorem no_set_mem_self : ¬set_mem_set β x x :=
begin
  intro hx,
  cases class_reg_prop α (set_to_class β (@set_pair α β _ x x)),
  specialize right x,
  rw ←set_to_class_prop at left,
  rw set_pair_prop at left,
  rw or_self at left,
  rw left at right,
  rw ←set_to_class_prop at right,
  rw set_pair_prop at right,
  rw or_self at right,
  apply right,
  split, refl, exact hx
end

instance : has_emptyc α := ⟨set_empty α β⟩
instance : has_union α := ⟨λ x y, set_union β $ set_pair β x y⟩

variables (β x)

def singleton : α := set_pair β x x

variables {β x}

theorem singleton_prop : set_mem_set β y (singleton β x) ↔ y = x :=
begin
  unfold singleton,
  rw set_pair_prop,
  rw or_self
end

-- class of sets that contains x

variables (β x)

def contains_set : β := class_range α (class_int α (class_prod α (set_to_class β (singleton β x)) (class_univ α β)) (class_mem α β))

variables {β x}

theorem contains_set_prop : set_mem_class x (contains_set β c) ↔ set_mem_set β c x :=
begin
  unfold contains_set,
  rw class_range_prop,
  split,
  intro h,
  cases h with z hz,
  rw class_int_prop at hz,
  cases hz,
  rw class_prod_prop at hz_left,
  cases hz_left with p hp,
  cases hp with q h,
  cases h with hp' h,
  cases h with hp h,
  cases pair_ext h,
  rw [←left, ←right] at *,
  rw ←set_to_class_prop at hp',
  rw singleton_prop at hp',
  rw ←hp',
  rw class_mem_prop at hz_right,
  cases hz_right with r hr,
  cases hr with s hr,
  cases hr with hr1 hr2,
  cases pair_ext hr2,
  rw [←left_1, ←right_1] at *,
  exact hr1,
  intro hx,
  existsi c,
  apply class_int_ext,
  apply class_prod_ext,
  apply set_to_class_ext,
  rw singleton_prop,
  apply class_univ_prop,
  apply class_mem_ext,
  exact hx
end

variables (α β)

def class_ne : β := class_int α (class_prod α (class_univ α β) (class_univ α β)) (class_comp α (class_eq α β))

variables {α β}

theorem class_comp_prop1 : set_mem_class x (class_comp α X) ↔ ¬set_mem_class x X :=
⟨(class_comp_prop X x).not_left_of_right, (class_comp_prop X x).right_of_not_left⟩

theorem class_comp_prop2 : set_mem_class x X ↔ ¬set_mem_class x (class_comp α X) :=
⟨(class_comp_prop X x).not_right_of_left, (class_comp_prop X x).left_of_not_right⟩

variables (α β)

-- class of (a,(b,c)) where a in c and b in c
def class_two_mem : β := class_int α (class_prod α (class_univ α β) (class_mem α β)) (class_prod_comm' α ((class_prod α (class_univ α β) (class_mem α β))))
-- class of ((a,b),c) where a ≠ b and a ∈ c and b ∈ c
def class_ne_mem : β := class_int α (class_prod_assoc α $ class_two_mem α β) (class_prod α (class_ne α β) (class_univ α β))
-- class of singletons
def class_singleton : β := class_int α (class_comp α (set_to_class β (singleton β (@set_empty α β _)))) (class_comp α (class_range α (class_ne_mem α β)))

variables {α β}

theorem class_singleton_prop : set_mem_class x (class_singleton α β) ↔ ∃ y, x = singleton β y :=
begin
  unfold class_singleton, unfold class_ne_mem,
  split,
  intro h,
  rw class_int_prop at h,
  cases h with h1 h2,
  rw class_comp_prop1 at h1,
  rw ←set_to_class_prop at h1,
  rw singleton_prop at h1,
  rw class_comp_prop1 at h2,
  rw class_range_prop at h2,
  have : ∃ y, set_mem_set β y x,
  apply classical.dne,
  intro hy,
  apply h1,
  apply set_ext x (set_empty α β),
  intro z,
  split,
  intro h,
  exfalso,
  apply hy,
  existsi z,
  exact h,
  intro h,
  exfalso,
  apply set_empty_prop β z,
  exact h,
  cases this with y hy,
  existsi y,
  apply @set_ext _ β _ x,
  intro z,
  rw singleton_prop,
  split,
  intro hz,
  apply classical.dne,
  intro hzy,
  apply h2,
  existsi pair β y z,
  apply class_int_ext,
  apply class_prod_assoc_ext,
  unfold class_two_mem,
  apply class_int_ext,
  apply class_prod_ext,
  apply class_univ_prop,
  apply class_mem_ext,
  exact hz,
  apply class_prod_comm'_ext,
  apply class_prod_ext,
  apply class_univ_prop,
  apply class_mem_ext,
  exact hy,
  apply class_prod_ext,
  unfold class_ne,
  apply class_int_ext,
  apply class_prod_ext,
  apply class_univ_prop,
  apply class_univ_prop,
  rw class_comp_prop1,
  rw class_eq_prop,
  intro hx,
  cases hx with x hx,
  have := pair_ext hx,
  cases this,
  apply hzy,
  rw this_left,
  rw this_right,
  apply class_univ_prop,
  intro hzy,
  rw hzy,
  exact hy,
  intro hy,
  cases hy with y hy,
  rw hy at *,
  apply class_int_ext,
  apply class_comp_prop1.2,
  rw ←set_to_class_prop,
  rw singleton_prop,
  intro hx,
  have : set_mem_set β y (singleton β y),
  rw singleton_prop,
  rw hx at this,
  apply set_empty_prop β,
  exact this,
  apply class_comp_prop1.2,
  rw class_range_prop,
  intro hx,
  cases hx with z h,
  rw class_int_prop at h,
  cases h with h1 h2,
  have h3 := (and_iff_left class_univ_prop).1 (class_prod_split h2),
  unfold class_ne at h3,
  rw class_int_prop at h3,
  cases h3 with h3 h4,
  rw class_prod_prop at h3,
  cases h3 with a h3,
  cases h3 with b h3,
  have h3 := (and_iff_right class_univ_prop).1 ((and_iff_right class_univ_prop).1 h3),
  rw h3 at *,
  have h1 := class_prod_of_prod_assoc h1,
  unfold class_two_mem at h1,
  rw class_int_prop at h1,
  cases h1 with h1 h5,
  have h5 := class_mem_of_mem ((and_iff_right class_univ_prop).1 $ class_prod_split $ class_prod_of_prod_comm' h5),
  rw singleton_prop at h5,
  rw h5 at h2,
  have h1 := class_mem_of_mem ((and_iff_right class_univ_prop).1 $ class_prod_split h1),
  rw singleton_prop at h1,
  rw h1 at h2,
  have h2 := (and_iff_left class_univ_prop).1 (class_prod_split h2),
  unfold class_ne at h2,
  rw class_int_prop at h2,
  apply (class_comp_prop _ _).not_left_of_right h2.2,
  apply class_eq_ext,
  refl
end

variables (α β)

def class_pair_singleton : β := class_int α (class_mem α β) (class_prod α (class_univ α β) (class_singleton α β))

variables {α β}

theorem class_pair_singleton_prop : set_mem_class z (class_pair_singleton α β) ↔ ∃ x y, y = singleton β x ∧ z = pair β x y :=
begin
  unfold class_pair_singleton,
  rw class_int_prop,
  rw class_mem_prop,
  split,
  intro h,
  cases h with h1 h3,
  cases h1 with x h1,
  cases h1 with y h1,
  cases h1 with h1 h2,
  rw h2 at *,
  have h3 := (class_prod_split h3).2,
  rw class_singleton_prop at h3,
  cases h3 with a ha,
  existsi a,
  existsi y,
  split,
  exact ha,
  rw ha at *,
  rw singleton_prop at h1,
  rw h1 at *,
  refl,
  intro h,
  cases h with x h,
  cases h with y h,
  cases h with h1 h2,
  split,
  existsi x,
  existsi y,
  split,
  rw h1,
  rw singleton_prop,
  exact h2,
  rw h2,
  apply class_prod_ext,
  apply class_univ_prop,
  rw class_singleton_prop,
  existsi x,
  exact h1
end

theorem class_pair_singleton_pair : set_mem_class (pair β x y) (class_pair_singleton α β) ↔ y = singleton β x :=
begin
  rw class_pair_singleton_prop,
  split,
  intro h,
  cases h with a h,
  cases h with b h,
  cases pair_ext h.2,
  exact left.symm ▸ right.symm ▸ h.1,
  intro hyx,
  existsi x,
  existsi y,
  split,
  exact hyx,
  refl
end

theorem proper_class_singleton : ¬∃ x:α, ∀ y, set_mem_set β y x ↔ ∃ z, y = singleton β z :=
begin
  intro hx,
  cases hx with x h,
  apply (limitation α (class_singleton α β)).not_left_of_right,
  existsi class_prod_comm α (class_pair_singleton α β),
  split,
  intro y,
  existsi singleton β y,
  split,
  rw class_singleton_prop,
  existsi y,
  refl,
  apply class_prod_comm_ext,
  rw class_pair_singleton_pair,
  intros x y z hx hxy hxz,
  rw class_singleton_prop at hx,
  cases hx with a ha,
  rw ha at *,
  have hxy := class_prod_of_prod_comm hxy,
  rw class_pair_singleton_pair at hxy,
  have h1 := singleton_prop.2 (refl a),
  rw hxy at h1,
  rw singleton_prop at h1,
  rw ←h1,
  have hxz := class_prod_of_prod_comm hxz,
  rw class_pair_singleton_pair at hxz,
  have h1 := singleton_prop.2 (refl a),
  rw hxz at h1,
  rw singleton_prop at h1,
  rw ←h1,
  existsi x,
  intro z,
  rw h,
  rw class_singleton_prop
end

end nbg
