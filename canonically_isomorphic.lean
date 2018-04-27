universe zfc_u

structure equiv' (α : Type zfc_u) (β : Type zfc_u) :=
(i  : α → β)
(j  : β → α)
(ij : ∀ x, j (i x) = x)
(ji : ∀ y, i (j y) = y)

namespace equiv'

variables {α β γ : Type zfc_u}

@[refl] protected def refl (α : Type zfc_u) : equiv' α α := ⟨id, id, λ x, rfl, λ x, rfl⟩

@[symm] protected def symm (e : equiv' α β) : equiv' β α := ⟨e.j, e.i, e.ji, e.ij⟩

@[trans] protected def trans (e₁ : equiv' α β) (e₂ : equiv' β γ) : equiv' α γ :=
⟨e₂.i ∘ e₁.i, e₁.j ∘ e₂.j,
 λ x, by simp [e₂.ij, e₁.ij],
 λ x, by simp [e₁.ji, e₂.ji]⟩

definition mul_is_add {α : Type zfc_u} : equiv' (has_mul α) (has_add α) :=
{ i := λ ⟨mul⟩, ⟨mul⟩,
  j := λ ⟨mul⟩, ⟨mul⟩, -- didn't I just write that?
  ij := λ ⟨x⟩, rfl,
  ji := λ ⟨x⟩, rfl,  -- didn't I just write that?
}

definition equiv_mul {α β : Type zfc_u} : equiv' α β → equiv' (has_mul α) (has_mul β) := λ E,
{ i := λ ⟨f⟩, ⟨λ b1 b2, E.i (f (E.j b1) (E.j b2))⟩,
  j := λ ⟨f⟩, ⟨λ a1 a2, E.j (f (E.i a1) (E.i a2))⟩,
  ij := λ ⟨f⟩, congr_arg has_mul.mk $ by funext; simp [E.ij],
  ji := λ ⟨f⟩, congr_arg has_mul.mk $ by funext; simp [E.ji]
}

definition mul_to_add {α β : Type} : equiv' α β → equiv' (has_add α) (has_add β) :=
λ H, mul_is_add.symm.trans $ (equiv_mul H).trans mul_is_add

end equiv'
