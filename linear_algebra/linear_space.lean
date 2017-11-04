import algebra.module

instance field.to_vector_space {K : Type} [field K] :
vector_space K K := ⟨ring.to_module⟩

lemma eq_zero_of_add_self_eq {α : Type} [add_group α]
{a : α} (H : a + a = a) : a = 0 :=
add_left_cancel (by {rw add_zero, exact H})

lemma smul_smul {K V : Type} [field K] [vector_space K V]
{a b : K} {v : V} : a • (b • v) = (a * b) • v := mul_smul.symm

structure linear_space (K V W : Type) [field K]
[vector_space K V] [vector_space K W] :=
    (T : V → W)
    (map_add : ∀ u v, T (u+v) = T u + T v)
    (map_mul : ∀ (c:K) v, T (c • v) = c • (T v))

namespace linear_space

section Hom

variables {K V W : Type} [field K] [vector_space K V] [vector_space K W]
variables {c d : K} {u v : V} {A B C : linear_space K V W}

@[simp] lemma map_add_simp : A.T (u+v) = A.T u + A.T v := map_add A u v
@[simp] lemma map_mul_simp : A.T (c•v) = c • (A.T v) := map_mul A c v

theorem ext (HAB : ∀ v, A.T v = B.T v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] lemma map_zero : A.T 0 = 0 :=
let T := A.T in
begin
    have := eq.symm (map_add A 0 0),
    rw [add_zero] at this,
    exact eq_zero_of_add_self_eq this
end

@[simp] lemma map_neg : A.T (-v) = -(A.T v) :=
eq_neg_of_add_eq_zero (by {rw [←map_add], simp})

@[simp] lemma map_sub : A.T (u-v) = A.T u - A.T v := by simp

@[simp] def ker (A : linear_space K V W) : V → Prop := (λ v, A.T v = 0)

theorem ker_of_map_eq_map (Huv : A.T u = A.T v) : A.ker (u-v) :=
by {rw [ker,map_sub], exact sub_eq_zero_of_eq Huv}

theorem inj_of_trivial_ker (H: ∀ v, A.ker v → v = 0) (Huv: A.T u = A.T v) : u = v :=
eq_of_sub_eq_zero (H _ (ker_of_map_eq_map Huv))

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

section matrix_ring

variables {K V : Type} [field K] [vector_space K V]
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

local notation A ∘ B := comp A B

@[simp] lemma id_simp : (id : linear_space K V V).T v = v := rfl
@[simp] lemma comp_simp : (A ∘ B).T v = A.T (B.T v) := rfl

variables (v A B C)

theorem comp_id : A ∘ id = A := ext (λ v, rfl)
theorem id_comp : id ∘ A = A := ext (λ v, rfl)
theorem comp_assoc : (A ∘ B) ∘ C = A ∘ (B ∘ C) := ext (λ v, rfl)
theorem comp_add : A ∘ (B + C) = A ∘ B + A ∘ C := ext (λ v, by simp)
theorem add_comp : (A + B) ∘ C = A ∘ C + B ∘ C := ext (λ v, rfl)

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

end linear_space
