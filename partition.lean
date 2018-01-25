import data.set.basic

universe u

structure equivalence_relation (α : Type u) :=
(f : α → α → Prop)
(reflexive : ∀ x, f x x)
(symmetric : ∀ x y, f x y → f y x)
(transitive : ∀ x y z, f x y → f y z → f x z)

structure partition (α : Type u) :=
(A : set (set α))
(prop : ∀ x, ∃! t, x ∈ t ∧ t ∈ A)
(non_empty : ∀ X, X ∈ A → ∃ y, y ∈ X)

open equivalence_relation
open partition

variables {α : Type u}

def equivalence_relation.stage_1 (f : α → α → Prop) : α → set α := λ x y, f x y
def equivalence_relation.stage_2 (f : α → α → Prop) : set (set α) := set.image (equivalence_relation.stage_1 f) set.univ

variable α

instance equivalence_relation.to_partition : has_coe (equivalence_relation α) (partition α) :=
begin
  constructor,
  intro h,
  fapply partition.mk,
  exact equivalence_relation.stage_2 h.f,
  intro x,
  existsi equivalence_relation.stage_1 h.f x,
  split,
  split,
  exact h.reflexive x,
  existsi x,
  split,
  constructor,
  refl,
  intros X hy,
  cases hy with h1 h2,
  cases h2 with y h2,
  cases h2 with h2 h3,
  rw ←h3 at *,
  apply set.ext,
  intro z,
  split,
  intro h4,
  apply h.transitive x y z,
  apply h.symmetric,
  exact h1,
  exact h4,
  intro h4,
  apply h.transitive y x z,
  exact h1,
  exact h4,
  intros X h1,
  unfold equivalence_relation.stage_2 at h1,
  cases h1 with x h1,
  existsi x,
  rw ←h1.2,
  exact h.reflexive x
end

variable {α}

def partition.stage_1 (A : set (set α)) : α → α → Prop := λ x y, ∃ t, t ∈ A ∧ x ∈ t ∧ y ∈ t

variable α

instance partition.to_equivalence_relation : has_coe (partition α) (equivalence_relation α) :=
begin
  constructor,
  intro h,
  fapply equivalence_relation.mk,
  exact partition.stage_1 h.A,
  intro x,
  cases h.prop x with X h1,
  cases h1 with h1 h2,
  existsi X,
  exact ⟨h1.2, h1.1, h1.1⟩,
  intros x y h1,
  cases h1 with X h1,
  existsi X,
  exact ⟨h1.1, h1.2.2, h1.2.1⟩,
  intros x y z hxy hyz,
  cases hxy with X hxy,
  cases hyz with Y hyz,
  cases h.prop y with Z h1,
  have h2 := h1.2 X ⟨hxy.2.2, hxy.1⟩,
  have h3 := h1.2 Y ⟨hyz.2.1, hyz.1⟩,
  existsi X,
  rw h2 at *,
  rw h3 at *,
  exact ⟨hxy.1, hxy.2.1, hyz.2.2⟩
end

theorem equivalence_relation.to_partition.to_equivalence_relation (h : equivalence_relation α) :
has_coe.coe (equivalence_relation α) (has_coe.coe (partition α) h) = h:=
begin
  unfold has_coe.coe,
  cases h,
  congr,
  unfold partition.stage_1,
  apply funext,
  intro x,
  apply funext,
  intro y,
  unfold equivalence_relation.stage_2,
  unfold equivalence_relation.stage_1,
  apply iff_iff_eq.1,
  split,
  intro h,
    cases h with X h,
    cases h with h1 h2,
    cases h2 with h2 h3,
    unfold set.image at h1,
    cases h1 with z h1,
    dsimp at h1,
    apply h_transitive x z y,
    apply h_symmetric,
    rw h1.2,
    exact h2,
    rw h1.2,
    exact h3,
  intro h,
    existsi h_f x,
    split,
    existsi x,
    split,
    constructor,
    refl,
    split,
    exact h_reflexive x,
    exact h
end

theorem partition.to_equivalence_relation.to_partition (h : partition α) :
has_coe.coe (partition α) (has_coe.coe (equivalence_relation α) h) = h:=
begin
  unfold has_coe.coe,
  cases h,
  congr,
  unfold equivalence_relation.stage_2,
  unfold equivalence_relation.stage_1,
  unfold partition.stage_1,
  unfold set.image,
  apply set.ext,
  intro X,
  split,
  intro h,
    cases h with x h,
    dsimp at h,
    cases h with h1 h,
    clear h1,
    have h1 := h_prop x,
    cases h1 with Y h1,
    cases h1 with h1 h2,
    cases h1 with h1 h3,
    have h4 : X = Y,
    apply set.ext,
    intro z,
    split,
    intro hz,
      rw ←h at hz,
      cases hz with Z hz,
      specialize h2 Z ⟨hz.2.1, hz.1⟩,
      rw ←h2,
      exact hz.2.2,
    intro hz,
      rw ←h,
      existsi Y,
      exact ⟨h3,h1,hz⟩,
    rwa h4,
  intro h,
    dsimp,
    cases h_non_empty X h with x hx,
    existsi x,
    split,
    constructor,
    apply set.ext,
    intro z,
    split,
      intro hz,
        cases hz with Y h1,
        cases h1 with h1 h2,
        cases h_prop x with Z hz,
        have h3 := hz.2 X ⟨hx,h⟩,
        have h4 := hz.2 Y ⟨h2.1,h1⟩,
        rw h3,
        rw ←h4,
        exact h2.2,
      intro hz,
        existsi X,
        exact ⟨h,hx,hz⟩
end
