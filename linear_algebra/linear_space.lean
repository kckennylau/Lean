import algebra.module

def field.to_vector_space {K : Type} [field K] :
vector_space K K := ⟨ring.to_module⟩

structure linear_space (K V W : Type) [field K]
[vector_space K V] [vector_space K W] :=
    (T' : V → W)
    (map_add' : ∀ u v, T' (u+v) = T' u + T' v)
    (map_mul' : ∀ (c:K) v, T' (c • v) = c • (T' v))

namespace linear_space

section Hom

parameters {K V W : Type} [field K]
[vector_space K V] [vector_space K W]
(A:linear_space K V W)

include K V W

def T : V → W := (λ v, @T' K V W _ _ _ A v)

def map_add : ∀ (u v:V), T (u+v) = T u + T v :=
    map_add' A

def map_mul : ∀ (c:K) (v:V), T (c • v) = c • (T v) :=
    map_mul' A

theorem ext (A B : linear_space K V W) (HAB : ∀ v, A.T v = B.T v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] theorem map_zero : T 0 = 0 :=
let T := A.T in
begin
    have H : T 0 + T 0 = T 0 + 0,
        rw [←map_add,add_zero,add_zero],
    exact add_left_cancel H
end

theorem map_neg (v : V) : T (-v) = -(T v) :=
begin
    apply eq_neg_of_add_eq_zero,
    rw [←map_add,add_left_neg,map_zero]
end

theorem map_sub (u v : V) : T (u-v) = T u - T v :=
by rw [sub_eq_add_neg,sub_eq_add_neg,map_add,map_neg]

def ker : V → Prop := (λ v, T v = 0)

theorem inj_of_trivial_ker (H: ∀ v, ker v → v = 0)
{u v : V} (Huv: T u = T v) : u = v :=
begin
    apply eq_of_sub_eq_zero,
    apply H,
    unfold ker,
    rw map_sub,
    apply sub_eq_zero_of_eq,
    exact Huv
end

def add (A B : linear_space K V W) : (linear_space K V W) :=
{
    T'          := (λ v, (A.T v) + (B.T v)),
    map_add'    := (λ u v, by {rw [map_add,map_add], ac_refl}),
    map_mul'    := (λ c v, by rw [map_mul,map_mul,smul_left_distrib])
}

def zero : linear_space K V W :=
{
    T'          := (λ v, 0),
    map_add'    := (λ u v, by simp),
    map_mul'    := (λ c v, by simp)
}

def neg (A : linear_space K V W) : linear_space K V W :=
{
    T'          := (λ v, -A.T v),
    map_add'    := (λ u v, by rw [map_add,neg_add]),
    map_mul'    := (λ c v, by rw [map_mul,smul_neg])
}

instance : has_add (linear_space K V W) := ⟨add⟩
instance : has_zero (linear_space K V W) := ⟨zero⟩
instance : has_neg (linear_space K V W) := ⟨neg⟩

@[simp] lemma add_simp (A B : linear_space K V W) (v : V) :
(A + B).T v = A.T v + B.T v := rfl
@[simp] lemma zero_simp (v : V) :
(0:linear_space K V W).T v = 0 := rfl
@[simp] lemma neg_simp (A : linear_space K V W) (v : V) :
(-A).T v = -(A.T v) := rfl

theorem add_zero (A : linear_space K V W) : A + 0 = A :=
ext _ _ (λ v, by simp [add_zero])

theorem zero_add (A : linear_space K V W) : 0 + A = A :=
ext _ _ (λ v, by simp [zero_add])

theorem add_right_neg (A : linear_space K V W) : A + (-A) = 0 :=
ext _ _ (λ v, by simp [add_right_neg])

theorem add_left_neg (A : linear_space K V W) : (-A) + A = 0 :=
ext _ _ (λ v, by simp [add_left_neg])

theorem add_assoc (A B C : linear_space K V W) : A+B+C=A+(B+C) :=
ext _ _ (λ v, by simp [add_assoc])

theorem add_comm (A B : linear_space K V W) : A+B=B+A :=
ext _ _ (λ v, by simp [add_comm])

instance : add_comm_group (linear_space K V W) :=
{
    add             := add,
    add_assoc       := add_assoc,
    zero            := zero,
    zero_add        := zero_add,
    add_zero        := add_zero,
    neg             := neg,
    add_left_neg    := add_left_neg,
    add_comm        := add_comm
}

def smul (c : K) (A : linear_space K V W) : linear_space K V W :=
{
    T'          := (λ v, c•(A.T v)),
    map_add'    := (λ u v, by rw [map_add,smul_left_distrib]),
    map_mul'    := (λ k v, by rw [map_mul,←mul_smul,←mul_smul,mul_comm])
}

local infix `⬝` := smul

@[simp] lemma smul_simp (c : K) (A : linear_space K V W) (v : V) :
(c⬝A).T v = c•(A.T v) := rfl

theorem smul_left_distrib (k : K) (A B : linear_space K V W) : k⬝(A+B) = k⬝A + k⬝B :=
ext _ _ (λ v, by simp [smul_left_distrib])

theorem smul_right_distrib (k m: K) (A : linear_space K V W) : (k+m)⬝A = k⬝A + m⬝A :=
ext _ _ (λ v, by simp [smul_right_distrib])

theorem mul_smul (k m: K) (A : linear_space K V W) : (k*m)⬝A = k⬝(m⬝A) :=
ext _ _ (λ v, by simp [mul_smul])

theorem one_smul (A : linear_space K V W) : 1⬝A = A :=
ext _ _ (λ v, by simp [one_smul])

instance : vector_space K (linear_space K V W) :=
    ⟨⟨⟨smul⟩,_,smul_left_distrib,smul_right_distrib,mul_smul,one_smul⟩⟩

end Hom

def Hom (K V W : Type) [field K] [vector_space K V] [vector_space K W] :=
vector_space K (linear_space K V W)

def vector_space.dual {K V: Type} [field K] [vector_space K V] :=
@Hom K V K _ _ field.to_vector_space

section matrix_ring

parameters {K V: Type} [field K] [vector_space K V]
(A:linear_space K V V)

include K V

def id : linear_space K V V :=
{
    T'          := id,
    map_add'    := (λ u v, by simp),
    map_mul'    := (λ u v, by simp),
}

def comp (A B : linear_space K V V) : linear_space K V V :=
{
    T'          := (λ v, A.T $ B.T v),
    map_add'    := (λ u v, by rw [map_add,map_add]),
    map_mul'    := (λ c v, by rw [map_mul,map_mul])
}

instance : has_mul (linear_space K V V) := ⟨comp⟩

local notation A ∘ B := comp A B

@[simp] lemma id_simp (v : V) : id.T v = v := rfl
@[simp] lemma comp_simp (A B : linear_space K V V) (v : V) :
(A ∘ B).T v = A.T (B.T v) := rfl

theorem comp_id (A : linear_space K V V) : A ∘ id = A :=
ext _ _ (λ v, by simp)

theorem id_comp (A : linear_space K V V) : id ∘ A = A :=
ext _ _ (λ v, by simp)

theorem comp_assoc (A B C : linear_space K V V) : (A ∘ B) ∘ C = A ∘ (B ∘ C) :=
ext _ _ (λ v, by simp)

theorem comp_add (A B C : linear_space K V V) : A ∘ (B + C) = A ∘ B + A ∘ C :=
ext _ _ (λ v, by simp [map_add])

theorem add_comp (A B C : linear_space K V V) : (A + B) ∘ C = A ∘ C + B ∘ C :=
ext _ _ (λ v, rfl)

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
