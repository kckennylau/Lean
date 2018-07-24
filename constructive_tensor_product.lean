import group_theory.coset
import group_theory.free_group
import linear_algebra.basic

universes u v w u₁
variable (α : Type u)

def is_add_group_hom {α : Type u} {β : Type v} [add_group α] [add_group β] (f : α → β) : Prop :=
@is_group_hom (multiplicative α) (multiplicative β) _ _ f

attribute [class] is_add_group_hom

namespace is_add_group_hom

variables {α} {β : Type v} [add_group α] [add_group β] (f : α → β) [hf : is_add_group_hom f]

theorem mk (H : ∀ x y, f (x + y) = f x + f y) : is_add_group_hom f :=
⟨H⟩

theorem add (x y) : f (x + y) = f x + f y :=
@is_group_hom.mul (multiplicative α) (multiplicative β) _ _ f hf x y

instance ring_hom_is_add_group_hom {α β : Type u} [ring α] [ring β] (f : α → β) [is_ring_hom f] : is_add_group_hom f :=
⟨λ _ _, is_ring_hom.map_add f⟩

theorem zero : f 0 = 0 :=
@is_group_hom.one (multiplicative α) (multiplicative β) _ _ f hf

theorem neg (x) : f (-x) = -f x :=
@is_group_hom.inv (multiplicative α) (multiplicative β) _ _ f hf x

end is_add_group_hom


section quotient

variables {α} [group α] {N : set α} [normal_subgroup N] (x y : left_cosets N)
variables {β : Type v} [group β] (f : α → β) [is_group_hom f]

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

def left_cosets.lift_on (H : ∀ x ∈ N, f x = 1) : β :=
quotient.lift_on x f $ λ m n h,
calc  f m
    = f m * f (m⁻¹ * n) : by rw [H _ h, mul_one]
... = f n : by rw [is_group_hom.mul f, is_group_hom.inv f, ← mul_assoc, mul_inv_self, one_mul]

def left_cosets.lift_on.is_group_hom (H : ∀ x ∈ N, f x = 1) :
  is_group_hom (λ x, left_cosets.lift_on x f H) :=
⟨λ x y, quotient.induction_on₂ x y $ λ m n,
  show f (m * n) = f m * f n, from is_group_hom.mul f m n⟩

def left_cosets.lift_on.mul (H : ∀ x ∈ N, f x = 1) :
  left_cosets.lift_on (x * y) f H = left_cosets.lift_on x f H * left_cosets.lift_on y f H :=
@is_group_hom.mul _ _ _ _ _ (left_cosets.lift_on.is_group_hom _ _) _ _

end quotient

section quotient

variables {α} [group α] {N : set α} [normal_subgroup N]
variables (x y : additive $ left_cosets N)
variables {β : Type v} [add_group β] (f : additive α → β) [is_add_group_hom f]

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

def left_cosets.add.lift_on (H : ∀ x ∈ N, f x = 0) : β :=
@left_cosets.lift_on _ _ _ _ x (multiplicative β) _ f ⟨λ _ _, is_add_group_hom.add f _ _⟩ H

def left_cosets.add.lift_on.is_add_group_hom (H : ∀ x ∈ N, f x = 0) :
  is_add_group_hom (λ x, left_cosets.add.lift_on x f H) :=
@left_cosets.lift_on.is_group_hom _ _ _ _ (multiplicative β) _ _ ⟨λ _ _, is_add_group_hom.add f _ _⟩ _

def left_cosets.add.lift_on.add (H : ∀ x ∈ N, f x = 0) :
  left_cosets.add.lift_on (x + y) f H = left_cosets.add.lift_on x f H + left_cosets.add.lift_on y f H :=
@left_cosets.lift_on.mul _ _ _ _ _ _ (multiplicative β) _ _ ⟨λ _ _, is_add_group_hom.add f _ _⟩ _

end quotient

section abelianization

variable [group α]

def commutator : set α :=
{ x | ∃ L : list α, (∀ z ∈ L, ∃ p q, p * q * p⁻¹ * q⁻¹ = z) ∧ L.prod = x }

instance : normal_subgroup (commutator α) :=
{ one_mem := ⟨[], by simp⟩,
  mul_mem := λ x y ⟨L1, HL1, HP1⟩ ⟨L2, HL2, HP2⟩,
    ⟨L1 ++ L2, list.forall_mem_append.2 ⟨HL1, HL2⟩, by simp*⟩,
  inv_mem := λ x ⟨L, HL, HP⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, q, h5⟩ := HL y (list.mem_reverse.1 h3) in
      ⟨q, p, by rw [← h4, ← h5]; simp [mul_assoc]⟩,
    by rw ← HP; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.reverse_cons, list.map_append, list.prod_append, ih]; simp)⟩,
  normal := λ x ⟨L, HL, HP⟩ g, ⟨L.map $ λ z, g * z * g⁻¹,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, q, h5⟩ := HL y h3 in
      ⟨g * p * g⁻¹, g * q * g⁻¹,
      by rw [← h4, ← h5]; simp [mul_assoc]⟩,
    by rw ← HP; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.map_cons, list.prod_cons, ih]; simp [mul_assoc])⟩, }

def abelianization : Type u :=
left_cosets $ commutator α

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

instance : comm_group (abelianization α) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ m n,
    quotient.sound $ ⟨[n⁻¹*m⁻¹*n*m],
      by simp; refine ⟨n⁻¹, m⁻¹, _⟩; simp,
      by simp [mul_assoc]⟩,
  .. left_cosets.group _ }

variable {α}

def abelianization.of (x : α) : abelianization α :=
quotient.mk x

instance abelianization.of.is_group_hom : is_group_hom (@abelianization.of α _) :=
⟨λ _ _, rfl⟩

section to_comm_group

variables {β : Type v} [comm_group β] (f : α → β) [is_group_hom f]

def abelianization.to_comm_group (x : abelianization α) : β :=
quotient.lift_on x f $ λ m n ⟨L, HL, HP⟩,
suffices f (list.prod L) = 1,
  by rw [HP, is_group_hom.mul f, is_group_hom.inv f, inv_mul_eq_iff_eq_mul] at this; simpa [this],
list.rec_on L (λ _, is_group_hom.one f) (λ hd tl HL ih,
  by rw [list.forall_mem_cons] at ih;
    rcases ih with ⟨⟨p, q, hpq⟩, ih⟩;
    specialize HL ih; rw [list.prod_cons, is_group_hom.mul f, ← hpq, HL];
    simp [is_group_hom.mul f, is_group_hom.inv f, mul_comm]) HL

def abelianization.to_comm_group.is_group_hom :
  is_group_hom (abelianization.to_comm_group f) :=
⟨λ x y, quotient.induction_on₂ x y $ λ m n,
  show f (m * n) = f m * f n, from is_group_hom.mul f m n⟩

@[simp] theorem abelianization.to_comm_group.of (x : α) :
  abelianization.to_comm_group f (abelianization.of x) = f x :=
rfl

theorem abelianization.to_comm_group.unique
  (g : abelianization α → β) [is_group_hom g]
  (hg : ∀ x, g (abelianization.of x) = f x) {x} :
  g x = abelianization.to_comm_group f x :=
quotient.induction_on x $ λ m, hg m

end to_comm_group

end abelianization


def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

variable {α}

def free_abelian_group.of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

instance : has_coe α (free_abelian_group α) :=
⟨free_abelian_group.of⟩

theorem coe_def (x : α) : (x : free_abelian_group α) = free_abelian_group.of x :=
rfl

section to_comm_group

variables {β : Type*} [add_comm_group β] (f : α → β)

def free_abelian_group.to_add_comm_group (x : free_abelian_group α) : β :=
@abelianization.to_comm_group _ _ (multiplicative β) _ (@free_group.to_group _ (multiplicative β) _ f) _ x

def free_abelian_group.to_add_comm_group.is_add_group_hom :
  is_add_group_hom (free_abelian_group.to_add_comm_group f) :=
abelianization.to_comm_group.is_group_hom _

local attribute [instance] free_abelian_group.to_add_comm_group.is_add_group_hom

@[simp] lemma free_abelian_group.to_add_comm_group.add (x y : free_abelian_group α) :
  free_abelian_group.to_add_comm_group f (x + y)
  = free_abelian_group.to_add_comm_group f x +
    free_abelian_group.to_add_comm_group f y :=
is_add_group_hom.add _ _ _

@[simp] lemma free_abelian_group.to_add_comm_group.neg (x : free_abelian_group α) :
  free_abelian_group.to_add_comm_group f (-x)
  = -free_abelian_group.to_add_comm_group f x :=
is_add_group_hom.neg _ _

@[simp] lemma free_abelian_group.to_add_comm_group.zero :
  free_abelian_group.to_add_comm_group f 0 = 0 :=
is_add_group_hom.zero _

@[simp] lemma free_abelian_group.to_add_comm_group.of (x : α) :
  free_abelian_group.to_add_comm_group f (free_abelian_group.of x) = f x :=
by unfold free_abelian_group.of; unfold free_abelian_group.to_add_comm_group; simp

theorem free_abelian_group.to_add_comm_group.unique
  (g : free_abelian_group α → β) [is_add_group_hom g]
  (hg : ∀ x, g (free_abelian_group.of x) = f x) {x} :
  g x = free_abelian_group.to_add_comm_group f x :=
@abelianization.to_comm_group.unique (free_group α) _ (multiplicative β) _ _ _ g _inst_2 (λ x,
@free_group.to_group.unique α (multiplicative β) _ _ (g ∘ abelianization.of)
  ⟨λ m n, is_add_group_hom.add g (abelianization.of m) (abelianization.of n)⟩ hg _) _

def free_abelian_group.UMP : (α → β) ≃ { f : free_abelian_group α → β // is_add_group_hom f } :=
{ to_fun := λ f, ⟨_, free_abelian_group.to_add_comm_group.is_add_group_hom f⟩,
  inv_fun := λ f, f.1 ∘ free_abelian_group.of,
  left_inv := λ f, funext $ λ x, free_abelian_group.to_add_comm_group.of f x,
  right_inv := λ f, subtype.eq $ funext $ λ x, eq.symm $ by letI := f.2; from
    free_abelian_group.to_add_comm_group.unique _ _ (λ _, rfl) }

end to_comm_group

section induction

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

@[elab_as_eliminator]
theorem free_abelian_group.induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ free_abelian_group.of x)
  (Cn : ∀ x, C (free_abelian_group.of x) → C (-free_abelian_group.of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

end induction

variables {R : Type u} (M : Type v) (N : Type w)
variables [comm_ring R] [module R M] [module R N]
include _inst_1

namespace tensor_product

def relators : set (free_abelian_group (M × N)) :=
@group.closure (multiplicative $ (free_abelian_group (M × N))) _
  { x : free_abelian_group (M × N) |
    (∃ (m1 m2 : M) (n : N), x = (m1, n) + (m2, n) - (m1 + m2, n)) ∨
    (∃ (m : M) (n1 n2 : N), x = (m, n1) + (m, n2) - (m, n1 + n2)) ∨
    (∃ (r : R) (m : M) (n : N), x = (r • m, n) - (m, r • n)) }

instance relators.normal_subgroup : @normal_subgroup (multiplicative $ (free_abelian_group (M × N))) _
  (relators M N) :=
{ normal := λ x hx g, by rw [@mul_right_comm (multiplicative $ (free_abelian_group (M × N))) _ g];
    rw [mul_inv_self, one_mul]; from hx,
  .. group.closure.is_subgroup _ }

end tensor_product

def tensor_product : Type (max v w) :=
additive $ @left_cosets (multiplicative $ (free_abelian_group (M × N))) _
  (tensor_product.relators M N) _

#print axioms tensor_product
-- propext
-- quot.sound

namespace tensor_product

section module

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

def of (m : M) (n : N) : tensor_product M N :=
⟦free_abelian_group.of (m, n)⟧

instance : add_comm_group (tensor_product M N) :=
{ add_comm := λ x y, quotient.induction_on₂ x y $
    λ m n, quotient.sound $ by simp [mul_comm],
  .. additive.add_group }

instance quotient.mk.is_add_group_hom :
  @is_add_group_hom (free_abelian_group (M × N)) (tensor_product M N) _ _
    quotient.mk :=
is_add_group_hom.mk _ $ λ _ _, rfl

def smul.aux (r : R) (x : free_abelian_group (M × N)) : tensor_product M N :=
free_abelian_group.to_add_comm_group (λ (y : M × N), of M N (r • y.1) (y.2)) x

def smul.aux.is_add_group_hom (r : R) : is_add_group_hom (smul.aux M N r) :=
free_abelian_group.to_add_comm_group.is_add_group_hom _

local attribute [instance] smul.aux.is_add_group_hom

def smul (r : R) (x : tensor_product M N) : tensor_product M N :=
left_cosets.add.lift_on x (smul.aux M N r) $ λ x hx,
begin
  induction hx with _ hx _ _ ih _ _ _ _ ih1 ih2,
  { rcases hx with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩;
    rw [hx, smul.aux]; symmetry; simp [coe_def];
    apply quotient.sound,
    { rw [smul_add],
      apply group.in_closure.basic, left,
      exact ⟨_, _, _, by simp; refl⟩ },
    { apply group.in_closure.basic, right, left,
      exact ⟨_, _, _, by simp; refl⟩ },
    { rw [smul_smul, mul_comm r, ← smul_smul],
      apply group.in_closure.basic, right, right,
      exact ⟨_, _, _, by simp; refl⟩ } },
  { refl },
  { change smul.aux M N r (-_) = 0,
    rw [is_add_group_hom.neg (smul.aux M N r), ih, neg_zero] },
  { change smul.aux M N r (_ + _) = 0,
    rw [is_add_group_hom.add (smul.aux M N r), ih1, ih2, zero_add] }
end

protected theorem smul_add (r : R) (x y : tensor_product M N) :
  smul M N r (x + y) = smul M N r x + smul M N r y :=
left_cosets.add.lift_on.add _ _ _ _

instance : module R (tensor_product M N) :=
{ smul := smul M N,
  smul_add := tensor_product.smul_add M N,
  add_smul := λ r s x, quotient.induction_on x $ λ z, free_abelian_group.induction_on z
    (by simp [smul, left_cosets.add.lift_on, left_cosets.lift_on, smul.aux])
    (λ ⟨p, q⟩, eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $ group.in_closure.basic $ or.inl
      ⟨_, _, _, by simp [add_smul]; refl⟩)
    (λ ⟨p, q⟩, by simp [smul, left_cosets.add.lift_on, left_cosets.lift_on, smul.aux];
      intro H; simp [H])
    (λ p q ih1 ih2, show smul M N (r + s) (⟦p⟧ + ⟦q⟧) = smul M N r (⟦p⟧ + ⟦q⟧) + smul M N s (⟦p⟧ + ⟦q⟧),
      by dsimp at ih1 ih2; rw [tensor_product.smul_add, ih1, ih2];
      rw [tensor_product.smul_add, tensor_product.smul_add]; ac_refl),
  mul_smul := λ r s x, quotient.induction_on x $ λ z, free_abelian_group.induction_on z
    (by simp [smul, left_cosets.add.lift_on, left_cosets.lift_on, smul.aux, free_abelian_group.to_add_comm_group.zero]; refl)
    (λ ⟨p, q⟩, by simp [smul, left_cosets.add.lift_on, left_cosets.lift_on, smul.aux, mul_smul]; refl)
    (λ ⟨p, q⟩ _, by simp [smul, left_cosets.add.lift_on, left_cosets.lift_on, smul.aux, mul_smul]; refl)
    (λ p q ih1 ih2, show smul M N (r * s) (⟦p⟧ + ⟦q⟧) = _,
      by dsimp at ih1 ih2; rw [tensor_product.smul_add, ih1, ih2];
      rw [← tensor_product.smul_add, ← tensor_product.smul_add]; refl),
  one_smul := λ x, quotient.induction_on x $ λ _,
    eq.symm $ free_abelian_group.to_add_comm_group.unique _ _ $ λ ⟨p, q⟩,
    by rw [one_smul]; refl,
  .. tensor_product.add_comm_group M N }

end module

end tensor_product

#print axioms tensor_product.module
-- propext
-- quot.sound
