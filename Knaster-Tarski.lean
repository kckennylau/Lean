import order.complete_lattice order.order_iso

open lattice

universe u

variables {α : Type u} [complete_lattice α]

class is_ord_hom (f : α → α) : Prop :=
(ord : ∀ x y, x ≤ y → f x ≤ f y)

namespace is_ord_hom

variables {f : α → α} [is_ord_hom f]
variables {x y : α}

theorem apply_le_apply_of_le (H : x ≤ y) : f x ≤ f y :=
is_ord_hom.ord f x y H

end is_ord_hom

variables (f : α → α) [is_ord_hom f]

def fixed_points : set α := { x | f x = x }

namespace fixed_points

def previous (x : α) (H : f x ≤ x) : α :=
Sup { z | z ≤ x ∧ z ≤ f z }

variable {f}

theorem previous.le {x : α} {H : f x ≤ x} : previous f x H ≤ x :=
Sup_le $ λ z hz, hz.1

theorem previous.le_apply {x : α} {H : f x ≤ x} : previous f x H ≤ f (previous f x H) :=
Sup_le $ λ z hz, le_trans hz.2 (is_ord_hom.apply_le_apply_of_le $ le_Sup hz)

theorem previous.fixed {x : α} {H : f x ≤ x} : f (previous f x H) = previous f x H :=
le_antisymm
  (le_Sup ⟨le_trans (is_ord_hom.apply_le_apply_of_le previous.le) H,
     is_ord_hom.apply_le_apply_of_le previous.le_apply⟩)
  previous.le_apply

variable f

def next (x : α) (H : x ≤ f x) : α :=
Inf { z | x ≤ z ∧ f z ≤ z }

variable {f}

theorem next.le {x : α} {H : x ≤ f x} : x ≤ next f x H :=
le_Inf $ λ z hz, hz.1

theorem next.apply_le {x : α} {H : x ≤ f x} : f (next f x H) ≤ next f x H :=
le_Inf $ λ z hz, le_trans (is_ord_hom.apply_le_apply_of_le $ Inf_le hz) hz.2

theorem next.fixed {x : α} {H : x ≤ f x} : f (next f x H) = next f x H :=
le_antisymm
  next.apply_le
  (Inf_le ⟨le_trans H (is_ord_hom.apply_le_apply_of_le next.le),
     is_ord_hom.apply_le_apply_of_le $ next.apply_le⟩)

variable f

theorem aux1 (x y : fixed_points f) : x.1 ⊔ y.1 ≤ f (x.1 ⊔ y.1) :=
sup_le
  (x.2 ▸ is_ord_hom.apply_le_apply_of_le (x.2.symm ▸ le_sup_left))
  (y.2 ▸ is_ord_hom.apply_le_apply_of_le (y.2.symm ▸ le_sup_right))

theorem aux2 (x y : fixed_points f) : f (x.1 ⊓ y.1) ≤ x.1 ⊓ y.1 :=
le_inf
  (x.2 ▸ is_ord_hom.apply_le_apply_of_le (x.2.symm ▸ inf_le_left))
  (y.2 ▸ is_ord_hom.apply_le_apply_of_le (y.2.symm ▸ inf_le_right))

theorem aux3 (A : set $ fixed_points f) : Sup (subtype.val '' A) ≤ f (Sup (subtype.val '' A)) :=
Sup_le $ λ z ⟨⟨x, hx⟩, hxA, hxz⟩, hxz ▸ show x ≤ f (Sup (subtype.val '' A)),
from hx ▸ (is_ord_hom.apply_le_apply_of_le $ le_Sup ⟨⟨x, hx⟩, hxA, rfl⟩)

theorem aux4 (A : set $ fixed_points f) : f (Inf (subtype.val '' A)) ≤ Inf (subtype.val '' A) :=
le_Inf $ λ z ⟨⟨x, hx⟩, hxA, hxz⟩, hxz ▸ show f (Inf (subtype.val '' A)) ≤ x,
from hx ▸ (is_ord_hom.apply_le_apply_of_le $ Inf_le ⟨⟨x, hx⟩, hxA, rfl⟩)

instance : complete_lattice (fixed_points f) :=
{ le           := subrel (≤) _,
  le_refl      := λ x, le_refl x,
  le_trans     := λ x y z, le_trans,
  le_antisymm  := λ x y hx hy, subtype.eq $ le_antisymm hx hy,

  sup          := λ x y, ⟨next f (x.1 ⊔ y.1) (aux1 f x y), next.fixed⟩,
  le_sup_left  := λ x y, show x.1 ≤ _, from le_trans le_sup_left (@next.le _ _ f _ _ (aux1 f x y)),
  le_sup_right := λ x y, show y.1 ≤ _, from le_trans le_sup_right (@next.le _ _ f _ _ (aux1 f x y)),
  sup_le       := λ x y z hxz hyz, Inf_le ⟨sup_le hxz hyz, z.2.symm ▸ le_refl _⟩,

  inf          := λ x y, ⟨previous f (x.1 ⊓ y.1) (aux2 f x y), previous.fixed⟩,
  inf_le_left  := λ x y, show _ ≤ x.1, from le_trans (@previous.le _ _ f _ _ (aux2 f x y)) inf_le_left,
  inf_le_right := λ x y, show _ ≤ y.1, from le_trans (@previous.le _ _ f _ _ (aux2 f x y)) inf_le_right,
  le_inf       := λ x y z hxy hxz, le_Sup ⟨le_inf hxy hxz, x.2.symm ▸ le_refl _⟩,

  top          := ⟨previous f ⊤ le_top, previous.fixed⟩,
  le_top       := λ ⟨x, H⟩, le_Sup ⟨le_top, H.symm ▸ le_refl x⟩,

  bot          := ⟨next f ⊥ bot_le, next.fixed⟩,
  bot_le       := λ ⟨x, H⟩, Inf_le ⟨bot_le, H.symm ▸ le_refl x⟩,

  Sup          := λ A, ⟨next f (Sup $ subtype.val '' A) (aux3 f A), next.fixed⟩,
  le_Sup       := λ A x hxA, show x.1 ≤ _, from le_trans
                    (le_Sup $ show _ ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩)
                    (@next.le _ _ f _ _ (aux3 f A)),
  Sup_le       := λ A x Hx, Inf_le ⟨Sup_le $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx _ hyA, x.2.symm ▸ le_refl _⟩,

  Inf          := λ A, ⟨previous f (Inf $ subtype.val '' A) (aux4 f A), previous.fixed⟩,
  le_Inf       := λ A x Hx, le_Sup ⟨le_Inf $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx _ hyA, x.2.symm ▸ le_refl _⟩,
  Inf_le       := λ A x hxA, show _ ≤ x.1, from le_trans
                    (@previous.le _ _ f _ _ (aux4 f A))
                    (Inf_le $ show _ ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩) }

end fixed_points
