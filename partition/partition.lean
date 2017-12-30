import data.set.basic

universe u

structure equivalence_relation {α : Type u} (f : α → α → Prop) :=
(reflexive : ∀ x, f x x)
(symmetric : ∀ x y, f x y → f y x)
(transitive : ∀ x y z, f x y → f y z → f x z)

structure partition {α : Type u} (A : set (set α)) :=
(prop : ∀ x, ∃! t, x ∈ t ∧ t ∈ A)

open equivalence_relation
open partition

variables {α : Type u} (f : α → α → Prop) (A : set (set α))

def equivalence_relation.stage_1 : α → set α := λ x y, f x y
def equivalence_relation.stage_2 : set (set α) := set.image (equivalence_relation.stage_1 f) set.univ
instance equivalence_relation.to_partition : has_coe (equivalence_relation f) (partition $ equivalence_relation.stage_2 f) :=
begin
  constructor,
  intro h,
  constructor,
  intro x,
  existsi equivalence_relation.stage_1 f x,
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
  exact h4
end

def partition.stage_1 : α → α → Prop := λ x y, ∃ t, t ∈ A ∧ x ∈ t ∧ y ∈ t
instance partition.to_equivalence_relation : has_coe (partition A) (equivalence_relation $ partition.stage_1 A) :=
begin
  constructor,
  intro h,
  constructor,
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
