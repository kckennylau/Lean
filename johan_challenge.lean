import data.equiv

universes u v w

class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

local attribute [simp] transportable.on_refl transportable.on_trans

-- Our goal is an automagic proof of the following (level 20)
theorem group.transportable : transportable group := sorry

def transportable.trans (f : Type u → Type v) (g : Type v → Type w)
  [transportable f] [transportable g] : transportable (g ∘ f) :=
{ on_equiv := λ α β e, show g (f α) ≃ g (f β), from transportable.on_equiv g (transportable.on_equiv f e),
  on_refl  := λ α, by simp,
  on_trans := λ α β γ e₁ e₂, by simp }

-- These we might need to define and prove by hand
def Const : Type u → Type v := λ α, punit
def Fun : Type u → Type v → Type (max u v) := λ α β, α → β
def Prod : Type u → Type v → Type (max u v) := λ α β, α × β
def Swap : Type u → Type v → Type (max u v) := λ α β, β × α

-- level 1
lemma Const.transportable : (transportable Const) :=
{ on_equiv := λ α β e, equiv.punit_equiv_punit,
  on_refl  := λ α, equiv.ext _ _ $ λ ⟨⟩, rfl,
  on_trans := λ α β γ e1 e2, equiv.ext _ _ $ λ ⟨⟩, rfl }

lemma Fun.transportable (α : Type u) : (transportable (Fun α)) :=
{ on_equiv := λ β γ e, equiv.arrow_congr (equiv.refl α) e,
  on_refl  := λ β, equiv.ext _ _ $ λ f, rfl,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

theorem prod.ext' {α β : Type*} {p q : α × β} (H1 : p.1 = q.1) (H2 : p.2 = q.2) : p = q :=
prod.ext.2 ⟨H1, H2⟩

lemma Prod.transportable (α : Type u) : (transportable (Prod α)) :=
{ on_equiv := λ β γ e, equiv.prod_congr (equiv.refl α) e,
  on_refl  := λ β, equiv.ext _ _ $ λ ⟨x, y⟩, by simp,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ ⟨x, y⟩, by simp }

lemma Swap.transportable (α : Type u) : (transportable (Swap α)) :=
{ on_equiv := λ β γ e, equiv.prod_congr e (equiv.refl α),
  on_refl  := λ β, equiv.ext _ _ $ λ ⟨x, y⟩, by simp,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ ⟨x, y⟩, by simp }

-- And then we can define
def Hom1 (α : Type u) : Type v → Type (max u v) := λ β, α → β
def Hom2 (β : Type v) : Type u → Type (max u v) := λ α, α → β
def Aut : Type u → Type u := λ α, α → α

-- And hopefully automagically derive
lemma Hom1.transportable (α : Type u) : (transportable (Hom1 α)) :=
Fun.transportable α

lemma Hom2.transportable (β : Type v) : (transportable (Hom2 β)) :=
{ on_equiv := λ α γ e, equiv.arrow_congr e (equiv.refl β),
  on_refl  := λ β, equiv.ext _ _ $ λ f, rfl,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

lemma Aut.transportable : (transportable Aut) :=
{ on_equiv := λ α β e, equiv.arrow_congr e e,
  on_refl  := λ α, equiv.ext _ _ $ λ f, funext $ λ x, rfl,
  on_trans := λ α β γ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

-- If we have all these in place...
-- A bit of magic might actually be able to derive `group.transportable` on line 11.
-- After all, a group just is a type plus some functions... and we can now transport functions.
