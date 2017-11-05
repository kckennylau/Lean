import algebra.module

instance field.to_vector_space {K : Type} [field K] :
vector_space K K := ⟨ring.to_module⟩

lemma eq_zero_of_add_self_eq {α : Type} [add_group α]
{a : α} (H : a + a = a) : a = 0 :=
add_left_cancel (by {rw add_zero, exact H})

lemma add_four {α : Type} [add_monoid α]
{a b c d : α} : (a + b) + (c + d) = a + (b + c) + d := by simp

lemma mul_four {α : Type} [monoid α]
{a b c d : α} : (a * b) * (c * d) = a * (b * c) * d := by simp

lemma smul_smul {K V : Type} [field K] [vector_space K V]
{a b : K} {v : V} : a • (b • v) = (a * b) • v := mul_smul.symm


structure subspace (K : Type) (V : Type) [field K] [v : vector_space K V] :=
    (p : V → Prop)
    (p_zero : p 0)
    (p_add : ∀ u v, p u → p v → p (u + v))
    (p_neg : ∀ v, p v → p (-v))
    (p_smul : ∀ c v, p v → p (c • v))

namespace subspace

variables {K V : Type} [field K] [vector_space K V] (s : subspace K V)

variables {c d : K} (u v : {x // s.p x})

def add (u v : {x // s.p x}) : {x // s.p x} :=
{
    val := u.val + v.val,
    property := s.p_add u.val v.val u.property v.property
}

def zero : {x // s.p x} :=
{
    val := 0,
    property := s.p_zero
}

def neg (v : {x // s.p x}) : {x // s.p x} :=
{
    val := -v.val,
    property := s.p_neg v.val v.property
}

def smul (c : K) (v : {x // s.p x}) : {x // s.p x} :=
{
    val := c • v.val,
    property := s.p_smul c v.val v.property
}

instance : has_add {x // s.p x} := ⟨add s⟩
instance : has_zero {x // s.p x} := ⟨zero s⟩
instance : has_neg {x // s.p x} := ⟨neg s⟩
instance : has_scalar K {x // s.p x} := ⟨smul s⟩

@[simp] lemma add_simp : (add s u v).val = u.val + v.val := rfl
@[simp] lemma zero_simp : (zero s : {x // s.p x}).val = 0 := rfl
@[simp] lemma neg_simp : (neg s v).val = -v.val := rfl
@[simp] lemma smul_simp : (smul s c v).val = c • v.val := rfl
@[simp] lemma add_simp' : (u + v).val = u.val + v.val := rfl
@[simp] lemma zero_simp' : (0 : {x // s.p x}).val = 0 := rfl
@[simp] lemma neg_simp' : (-v).val = -v.val := rfl
@[simp] lemma smul_simp' : (c • v).val = c • v.val := rfl


instance : vector_space K {x // s.p x} :=
{
    add                 := add s,
    add_assoc           := (λ u v w, subtype.eq (by simp [add_assoc])),
    zero                := zero s,
    zero_add            := (λ v, subtype.eq (by simp [zero_add])),
    add_zero            := (λ v, subtype.eq (by simp [add_zero])),
    neg                 := neg s,
    add_left_neg        := (λ v, subtype.eq (by simp [add_left_neg])),
    add_comm            := (λ u v, subtype.eq (by simp [add_comm])),
    smul                := smul s,
    smul_left_distrib   := (λ c u v, subtype.eq (by simp [smul_left_distrib])),
    smul_right_distrib  := (λ c u v, subtype.eq (by simp [smul_right_distrib])),
    mul_smul            := (λ c d v, subtype.eq (by simp [mul_smul])),
    one_smul            := (λ v, subtype.eq (by simp [one_smul]))
}

end subspace


structure linear_space (K V W : Type) [field K]
[vector_space K V] [vector_space K W] :=
    (T : V → W)
    (map_add : ∀ u v, T (u+v) = T u + T v)
    (map_mul : ∀ (c:K) v, T (c • v) = c • (T v))

namespace linear_space

variables {K V W : Type} [field K] [vector_space K V] [vector_space K W]
variables {c d : K}


section basic

variables {u v : V} {A B C : linear_space K V W}

@[simp] lemma map_add_simp : A.T (u+v) = A.T u + A.T v := map_add A u v
@[simp] lemma map_mul_simp : A.T (c•v) = c • (A.T v) := map_mul A c v

theorem ext (HAB : ∀ v, A.T v = B.T v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] lemma map_zero : A.T 0 = 0 :=
begin
    have := eq.symm (map_add A 0 0),
    rw [add_zero] at this,
    exact eq_zero_of_add_self_eq this
end

@[simp] lemma map_neg : A.T (-v) = -(A.T v) :=
eq_neg_of_add_eq_zero (by {rw [←map_add], simp})

@[simp] lemma map_sub : A.T (u-v) = A.T u - A.T v := by simp

end basic


@[simp] def ker (A : linear_space K V W) : V → Prop := (λ v, A.T v = 0)

namespace ker

variables {A : linear_space K V W}
variables (u v : V)

theorem ker_of_map_eq_map (Huv : A.T u = A.T v) : A.ker (u-v) :=
by {rw [ker,map_sub], exact sub_eq_zero_of_eq Huv}

theorem inj_of_trivial_ker (H: ∀ v, A.ker v → v = 0) (Huv: A.T u = A.T v) : u = v :=
eq_of_sub_eq_zero (H _ (ker_of_map_eq_map _ _ Huv))

theorem ker_add (HU : A.ker u) (HV : A.ker v) : A.ker (u + v) :=
by {unfold ker at *, simp [HU,HV]}

theorem ker_zero : A.ker 0 := map_zero

theorem ker_neg (HV : A.ker v) : A.ker (-v) :=
by {unfold ker at *, simp [HV]}

theorem ker_sub (HU : A.ker u) (HV : A.ker v) : A.ker (u - v) :=
by {unfold ker at *, simp [HU,HV]}

theorem ker_smul (c : K) (v : V) (HV : A.ker v) : A.ker (c • v) :=
by {unfold ker at *, simp [HV]}

def ker_subspace : subspace K V :=
{
    p := (λ x, A.ker x),
    p_add := ker_add,
    p_zero := ker_zero,
    p_neg := ker_neg,
    p_smul := ker_smul
}

end ker


section Hom

variables {u v : V} {A B C : linear_space K V W}

def add (A B : linear_space K V W) : (linear_space K V W) :=
{
    T       := (λ v, (A.T v) + (B.T v)),
    map_add := (λ u v, by simp),
    map_mul := (λ c v, by simp [smul_left_distrib])
}

def zero : linear_space K V W :=
{
    T       := (λ v, 0),
    map_add := (λ u v, by simp),
    map_mul := (λ c v, by simp)
}

def neg (A : linear_space K V W) : linear_space K V W :=
{
    T       := (λ v, -A.T v),
    map_add := (λ u v, by simp),
    map_mul := (λ c v, by simp)
}

instance : has_add (linear_space K V W) := ⟨add⟩
instance : has_zero (linear_space K V W) := ⟨zero⟩
instance : has_neg (linear_space K V W) := ⟨neg⟩

@[simp] lemma add_simp : (A + B).T v = A.T v + B.T v := rfl
@[simp] lemma zero_simp : (0:linear_space K V W).T v = 0 := rfl
@[simp] lemma neg_simp : (-A).T v = -(A.T v) := rfl

def smul (c : K) (A : linear_space K V W) : linear_space K V W :=
{
    T       := (λ v, c•(A.T v)),
    map_add := (λ u v, by simp [smul_left_distrib]),
    map_mul := (λ k v, by simp [smul_smul])
}

local infix `⬝` := smul

@[simp] lemma smul_simp : (c⬝A).T v = c•(A.T v) := rfl

variables (c d u v A B C)

theorem add_zero : A + 0 = A := ext (λ v, by simp [add_zero])
theorem zero_add : 0 + A = A := ext (λ v, by simp [zero_add])
theorem add_right_neg : A + (-A) = 0 := ext (λ v, by simp [add_right_neg])
theorem add_left_neg : (-A) + A = 0 := ext (λ v, by simp [add_left_neg])
theorem add_assoc : A + B + C = A + (B + C) := ext (λ v, by simp [add_assoc])
theorem add_comm : A + B = B + A := ext (λ v, by simp [add_comm])
theorem smul_left_distrib : c⬝(A+B) = c⬝A + c⬝B := ext (λ v, by simp [smul_left_distrib])
theorem smul_right_distrib : (c+d)⬝A = c⬝A + d⬝A := ext (λ v, by simp [smul_right_distrib])
theorem mul_smul : (c*d)⬝A = c⬝(d⬝A) := ext (λ v, by simp [mul_smul])
theorem one_smul : 1⬝A = A := ext (λ v, by simp [one_smul])

instance : vector_space K (linear_space K V W) :=
{
    add                 := add,
    add_assoc           := add_assoc,
    zero                := zero,
    zero_add            := zero_add,
    add_zero            := add_zero,
    neg                 := neg,
    add_left_neg        := add_left_neg,
    add_comm            := add_comm,
    smul                := smul,
    smul_left_distrib   := smul_left_distrib,
    smul_right_distrib  := smul_right_distrib,
    mul_smul            := mul_smul,
    one_smul            := one_smul
}

end Hom

def Hom {K : Type} (V W : Type) [field K] [vector_space K V] [vector_space K W] :=
vector_space K (linear_space K V W)

def vector_space.dual {K: Type} (V: Type) [field K] [vector_space K V] :=
@Hom K V K _ _ field.to_vector_space

-- \ast
postfix `∗`:100 := vector_space.dual


section matrix_ring

variables {v : V} {A B C : linear_space K V V}

def id : linear_space K V V :=
{
    T       := id,
    map_add := (λ u v, rfl),
    map_mul := (λ u v, rfl),
}

def comp (A B : linear_space K V V) : linear_space K V V :=
{
    T       := (λ v, A.T $ B.T v),
    map_add := (λ u v, by simp),
    map_mul := (λ c v, by simp)
}

instance : has_mul (linear_space K V V) := ⟨comp⟩

@[simp] lemma id_simp : (id : linear_space K V V).T v = v := rfl
@[simp] lemma comp_simp : (A * B).T v = A.T (B.T v) := rfl

variables (v A B C)

@[simp] lemma comp_id : A * id = A := ext (λ v, rfl)
@[simp] lemma id_comp : id * A = A := ext (λ v, rfl)
theorem comp_assoc : (A * B) * C = A * (B * C) := ext (λ v, rfl)
theorem comp_add : A * (B + C) = A * B + A * C := ext (λ v, by simp)
theorem add_comp : (A + B) * C = A * C + B * C := ext (λ v, rfl)

instance : ring (linear_space K V V) :=
{
    add             := add,
    add_assoc       := add_assoc,
    zero            := zero,
    zero_add        := zero_add,
    add_zero        := add_zero,
    neg             := neg,
    add_left_neg    := add_left_neg,
    add_comm        := add_comm,
    mul             := comp,
    mul_assoc       := comp_assoc,
    one             := id,
    one_mul         := id_comp,
    mul_one         := comp_id,
    left_distrib    := comp_add,
    right_distrib   := add_comp
}

end matrix_ring

variables (K V)


namespace general_linear

structure invertible :=
    (val : linear_space K V V)
    (inv : linear_space K V V)
    (property : val*inv = (id:linear_space K V V) ∧ inv*val = id)

variables {A B C : invertible K V}
variables {K V}

def ext (HAB : (∀ v:V, A.val.T v = B.val.T v)) : A = B :=
begin
    cases A,
    cases B,
    congr,
    apply ext HAB,
    have HAB : val = val_1 := ext HAB,
    exact calc
        inv = inv * (val_1 * inv_1) : by rw [property_1.1,comp_id]
        ... = (inv * val_1) * inv_1 : by rw [mul_assoc]
        ... = (inv * val) * inv_1   : by rw [HAB]
        ... = inv_1                 : by rw [property.2,id_comp]
end

def comp (A B : invertible K V) : invertible K V :=
{
    val := A.val * B.val,
    inv := B.inv * A.inv,
    property := ⟨by simp [mul_four,B.property.1,A.property.1],
                by simp [mul_four,A.property.2,B.property.2]⟩
}

def id : invertible K V :=
{
    val := id,
    inv := id,
    property := ⟨comp_id id, id_comp id⟩
}

def inv (A : invertible K V) : invertible K V :=
{
    val := A.inv,
    inv := A.val,
    property := ⟨A.property.2, A.property.1⟩
}

instance : has_mul (invertible K V) := ⟨comp⟩
instance : has_one (invertible K V) := ⟨id⟩
instance : has_inv (invertible K V) := ⟨inv⟩

variables (A B C) (u v : V)

@[simp] lemma comp_simp : (comp A B).val.T v = A.val.T (B.val.T v) := rfl
@[simp] lemma id_simp : (id : invertible K V).val.T v = v := rfl
@[simp] lemma inv_simp : (inv A).val.T v = A.inv.T v := rfl
@[simp] lemma comp_simp' : (A * B).val.T v = A.val.T (B.val.T v) := rfl
@[simp] lemma id_simp' : (1 : invertible K V).val.T v = v := rfl
@[simp] lemma inv_simp' : (A⁻¹).val.T v = A.inv.T v := rfl
@[simp] lemma comp_inv_simp' : (A*A⁻¹).val.T v = v :=
begin
    have := A.property.1,
    have : (A.val * A.inv).T v = linear_space.id.T v := by rw [this],
    simp at this,
    simp [this]
end
@[simp] lemma inv_comp_simp' : (A⁻¹*A).val.T v = v :=
begin
    have := A.property.2,
    have : (A.inv * A.val).T v = linear_space.id.T v := by rw [this],
    simp at this,
    simp [this]
end

theorem comp_assoc : (A * B) * C = A * (B * C) := ext (λ v, by simp)
theorem comp_id : A * id = A := ext (λ v, by simp)
theorem id_comp : id * A = A := ext (λ v, by simp)
theorem comp_right_inv : A * A⁻¹ = 1 := ext (λ v, by simp)
theorem comp_left_inv : A⁻¹ * A = 1 := ext (λ v, by simp)

instance : group (invertible K V) :=
{
    mul := comp,
    mul_assoc := comp_assoc,
    one := id,
    mul_one := comp_id,
    one_mul := id_comp,
    inv := inv,
    mul_left_inv := comp_left_inv
}

end general_linear

end linear_space
