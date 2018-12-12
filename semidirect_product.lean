import algebra.group data.zmod.basic

universes u v

variables (N : Type u) (K : Type v) [group N] [group K]

structure linear_group_action : Type (max u v) :=
(smul : K → N → N)
(one_smul' : ∀ n, smul 1 n = n)
(mul_smul' : ∀ k₁ k₂ n, smul (k₁ * k₂) n = smul k₁ (smul k₂ n))
(smul_mul' : ∀ k n₁ n₂, smul k (n₁ * n₂) = smul k n₁ * smul k n₂)

instance : has_coe_to_fun (linear_group_action N K) :=
⟨_, linear_group_action.smul⟩

variables {N K} (φ : linear_group_action N K)
include φ

namespace linear_group_action
theorem one_smul (n) : φ 1 n = n := φ.one_smul' n
theorem mul_smul (k₁ k₂ n) : φ (k₁ * k₂) n = φ k₁ (φ k₂ n) := φ.mul_smul' k₁ k₂ n
theorem smul_mul (k n₁ n₂) : φ k (n₁ * n₂) = φ k n₁ * φ k n₂ := φ.smul_mul' k n₁ n₂
theorem is_group_hom (k) : is_group_hom (φ k) := ⟨φ.smul_mul k⟩
theorem smul_one (k) : φ k 1 = 1 := @@is_group_hom.one _ _ _ (φ.is_group_hom k)
theorem smul_inv (k n) : φ k n⁻¹ = (φ k n)⁻¹ := @@is_group_hom.inv _ _ _ (φ.is_group_hom k) n
end linear_group_action

def semidirect_product : Type (max u v) :=
N × K

instance : group (semidirect_product φ) :=
{ mul := λ x1 x2, (x1.1 * φ x1.2 x2.1, x1.2 * x2.2),
  mul_assoc := λ x1 x2 x3,
    show (_ * _ * φ (_ * _) _, _ * _ * _) =
      (_ * φ _ (_ * _), _ * (_ * _)),
    by simp only [φ.smul_mul, φ.mul_smul, mul_assoc],
  one := (1, 1),
  one_mul := λ ⟨n, k⟩, show (1 * φ 1 n, 1 * k) = (n, k),
    by simp only [φ.one_smul, one_mul],
  mul_one := λ ⟨n, k⟩, show (n * φ k 1, k * 1) = (n, k),
    by simp only [φ.smul_one, mul_one],
  inv := λ x, (φ x.2⁻¹ x.1⁻¹, x.2⁻¹),
  mul_left_inv := λ x, show (φ _ _ * φ x.2⁻¹ _, x.2⁻¹ * x.2) = ((1:N), (1:K)),
    by rw [← φ.smul_mul, inv_mul_self, inv_mul_self, φ.smul_one] }

omit φ
variables (n : ℕ+)

def cyclic : Type :=
multiplicative $ zmod n

instance : comm_group (cyclic n) :=
multiplicative.comm_group

def cyclic.g : cyclic n :=
(1 : zmod n)

instance : fintype (cyclic n) :=
zmod.fintype n

def dihedral2.aux : linear_group_action (cyclic n) (cyclic 2) :=
{ smul := λ k n, has_inv.inv^[k.val] n,
  one_smul' := λ _, rfl,
  mul_smul' := λ k₁ k₂ n, match k₁, k₂ with
    | ⟨0, _⟩, ⟨0, _⟩ := rfl
    | ⟨0, _⟩, ⟨1, _⟩ := rfl
    | ⟨0, _⟩, ⟨k₂+2, hk₂⟩ := absurd hk₂ dec_trivial
    | ⟨1, _⟩, ⟨0, _⟩ := rfl
    | ⟨1, _⟩, ⟨1, _⟩ := (inv_inv n).symm
    | ⟨1, _⟩, ⟨k₂+2, hk₂⟩ := absurd hk₂ dec_trivial
    | ⟨k₁+2, hk₁⟩, ⟨_, _⟩ := absurd hk₁ dec_trivial
    end,
  smul_mul' := λ k n₁ n₂, match k with
    | ⟨0, _⟩ := rfl
    | ⟨1, _⟩ := mul_inv n₁ n₂
    | ⟨k+2, hk⟩ := absurd hk dec_trivial
    end }

@[reducible] def dihedral2 : Type :=
semidirect_product $ dihedral2.aux n

instance : fintype (dihedral2 n) := prod.fintype _ _
instance : decidable_eq (dihedral2 n) := prod.decidable_eq

variables {n}
def ρ : dihedral2 n := (cyclic.g n, 1)
def σ : dihedral2 n := ⟨1, cyclic.g 2⟩
variables (n)

theorem rho_mul_sigma : (ρ * σ : dihedral2 n) = σ * ρ⁻¹ :=
prod.ext (show cyclic.g n * 1 = 1 * (cyclic.g n)⁻¹⁻¹, by rw [mul_one, one_mul, inv_inv]) rfl

theorem sigma_mul_sigma : (σ * σ : dihedral2 n) = 1 :=
prod.ext (show (1 * 1⁻¹ : cyclic n) = 1, by rw [one_inv, mul_one]) rfl

instance dihedral2.comm_group_1 : comm_group (dihedral2 1) :=
{ mul_comm := dec_trivial,
  .. (infer_instance : group (dihedral2 1)) }

instance dihedral2.comm_group_2 : comm_group (dihedral2 2) :=
{ mul_comm := dec_trivial,
  .. (infer_instance : group (dihedral2 2)) }

lemma dihedral_non_abelian {n:ℕ+} (h: 3 ≤ ↑n) : ∃ (g h : dihedral2 n), ¬(g*h = h*g) :=
⟨ρ, σ, λ H, have (1 + 0 : zmod n) = 0 - 1 := (prod.ext_iff.1 H).1,
have ↑n ∣ 2, by rwa [zero_sub, add_zero, eq_neg_iff_add_eq_zero,
  ← nat.cast_one, ← nat.cast_add, zmod.eq_zero_iff_dvd_nat] at this,
not_le_of_lt (nat.lt_of_succ_le h) $ nat.le_of_dvd dec_trivial this⟩
