import data.equiv

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w} [group α] [group β] [group γ]

variables (α β)

structure isomorphism extends equiv α β :=
(map_mul : is_group_hom to_fun)

namespace isomorphism

variables {α β} (f : isomorphism α β) (g : isomorphism β γ) {x y : α}

def comp : isomorphism α γ :=
{ equiv.trans f.to_equiv g.to_equiv with
  map_mul := λ x y, calc
          g.to_fun (f.to_fun (x * y))
        = g.to_fun (f.to_fun x * f.to_fun y) : congr_arg g.to_fun $ @isomorphism.map_mul _ _ _ _ f x y
    ... = g.to_fun (f.to_fun x) * g.to_fun (f.to_fun y) : @isomorphism.map_mul _ _ _ _ g _ _ }

def inv : isomorphism β α :=
{ equiv.symm f.to_equiv with
  map_mul := λ x y, calc
    f.inv_fun (x * y) = f.inv_fun (f.to_fun (f.inv_fun x) * y) : congr_arg f.inv_fun $ congr_arg (λ z, z * y) $ eq.symm $ f.right_inv x
    ... = f.inv_fun (f.to_fun (f.inv_fun x) * f.to_fun (f.inv_fun y)) : congr_arg f.inv_fun $ congr_arg (λ z, f.to_fun (f.inv_fun x) * z) $ eq.symm $ f.right_inv y
    ... = f.inv_fun (f.to_fun (f.inv_fun x * f.inv_fun y)) : congr_arg f.inv_fun $ eq.symm $ @isomorphism.map_mul _ _ _ _ f _ _
    ... = f.inv_fun x * f.inv_fun y : f.left_inv (f.inv_fun x * f.inv_fun y) }

def id : isomorphism α α :=
{ equiv.refl α with
  map_mul := λ x y, rfl }

end isomorphism


structure automorphism extends isomorphism α α

theorem automorphism.ext (f g : automorphism α) (H : ∀ x, f.to_isomorphism.to_equiv.to_fun x = g.to_isomorphism.to_equiv.to_fun x) : f = g :=
by cases f; cases f; cases g; cases g; congr; apply equiv.ext; exact H

namespace automorphism

instance : has_coe (automorphism α) (α → α) := ⟨λ f, f.to_isomorphism.to_equiv⟩

theorem map_mul (f : automorphism α) (x y : α) :
  (f : α → α) (x * y) = (f : α → α) x * (f : α → α) y :=
@isomorphism.map_mul _ _ _ _ f.to_isomorphism _ _

variable {α}

theorem is_group_hom (f : automorphism α) : is_group_hom (f : α → α) :=
map_mul α f

variable α

instance : group (automorphism α) :=
{ mul := λ f g, automorphism.mk $ g.to_isomorphism.comp f.to_isomorphism,
  mul_assoc := λ f g h, by unfold has_mul.mul; congr,
  one := automorphism.mk $ isomorphism.id,
  one_mul := λ f, by apply automorphism.ext; intro x; refl,
  mul_one := λ f, by apply automorphism.ext; intro x; refl,
  inv := λ f, automorphism.mk $ f.to_isomorphism.inv,
  mul_left_inv := λ f, by apply automorphism.ext; intro x; exact ((f.to_isomorphism).to_equiv).left_inv x}

@[simp] lemma mul_apply (f g : automorphism α) (x : α) :
  (((f * g) : automorphism α) : α → α) x = (f:α → α) ((g:α → α) x) :=
rfl

end automorphism


variables (α β)

def group_direct_product : group (α × β) :=
{ mul := λ x y, (x.fst * y.fst, x.snd * y.snd),
  mul_assoc := λ x y z, by simp [mul_assoc],
  one := (1, 1),
  one_mul := λ x, by simp,
  mul_one := λ x, by rw prod.ext; split; apply mul_one,
  inv := λ x, (x.fst⁻¹, x.snd⁻¹),
  mul_left_inv := λ x, by rw prod.ext; split; apply mul_left_inv }

def group_semidirect_product (f : β → automorphism α) (H : is_group_hom f) : group (α × β) :=
{ mul := λ x y, (x.fst * (f x.snd : α → α) y.fst, x.snd * y.snd),
  mul_assoc := λ x y z, by rw prod.ext; split;
    simp [H, H x.snd, automorphism.map_mul α (f x.snd), mul_assoc],
  one := (1, 1),
  one_mul := λ x, by rw prod.ext; split; simp [H.one]; refl,
  mul_one := λ x, by rw prod.ext; split;
    simp [(*), semigroup.mul, monoid.mul, group.mul, (f x.snd).is_group_hom.one]; apply mul_one,
  inv := λ x, ((f x.snd⁻¹ : α → α) (x.fst⁻¹), x.snd⁻¹),
  mul_left_inv := λ x, calc
      ((f x.snd⁻¹ : α → α) (x.fst⁻¹) * (f x.snd⁻¹ : α → α) x.fst, x.snd⁻¹ * x.snd)
    = (1, 1) : by rw ← (f x.snd⁻¹).is_group_hom; simp [(f x.snd⁻¹).is_group_hom.one] }
