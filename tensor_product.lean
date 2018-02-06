import algebra.group_power algebra.module data.finsupp data.set.basic tactic.ring
noncomputable theory

universes u u₁ v v₁ w

open classical set function
local attribute [instance] decidable_inhabited prop_decidable

class type_singleton (α : Type u) : Type u :=
(default : α)
(unique : ∀ x : α, x = default)

namespace type_singleton

variables (α : Type u) [type_singleton α]
variables (β : Type v) [type_singleton β]

def equiv_unit : equiv α unit :=
{ to_fun    := λ x, unit.star,
  inv_fun   := λ x, type_singleton.default α,
  left_inv  := λ x, by rw type_singleton.unique x,
  right_inv := λ x, unit.cases_on x rfl }

def equiv_singleton : equiv α β :=
{ to_fun    := λ x, type_singleton.default β,
  inv_fun   := λ x, type_singleton.default α,
  left_inv  := λ x, by rw type_singleton.unique x,
  right_inv := λ x, by rw type_singleton.unique x }

end type_singleton

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

section bilinear

variables {α : Type u} [comm_ring α]
include α

variables {β : Type v} {γ : Type w} {α₁ : Type u₁} {β₁ : Type v₁}
variables [module α β] [module α γ] [module α α₁] [module α β₁]
--TODO: change definition
structure is_bilinear_map
  {β γ α₁}
  [module α β] [module α γ] [module α α₁]
  (f : β → γ → α₁) : Prop :=
(add_pair : ∀ x y z, f (x + y) z = f x z + f y z)
(pair_add : ∀ x y z, f x (y + z) = f x y + f x z)
(smul_trans : ∀ r₁ r₂ x y, f (r₁ • x) (r₂ • y) = (r₁ * r₂) • f x y)

variables {f : β → γ → α₁} (hf : is_bilinear_map f)
include hf

theorem is_bilinear_map.smul_pair :
  ∀ r x y, f (r • x) y = r • f x y :=
λ r x y, by simpa using hf.smul_trans r 1 x y

theorem is_bilinear_map.pair_smul :
  ∀ r x y, f x (r • y) = r • f x y :=
λ r x y, by simpa using hf.smul_trans 1 r x y

variables {g : α₁ → β₁} (hg : is_linear_map g)
include hg

theorem is_bilinear_map.comp : is_bilinear_map (λ x y, g (f x y)) :=
{ add_pair   := λ x y z, by rw [hf.add_pair, hg.add],
  pair_add   := λ x y z, by rw [hf.pair_add, hg.add],
  smul_trans := λ r₁ r₂ x y, by rw [hf.smul_trans, hg.smul] }

omit hf hg

variables (β γ)

structure module_iso (β γ) [module α β] [module α γ] extends equiv β γ :=
( linear : is_linear_map to_fun )

end bilinear

infix ` ≃ₘ `:50 := module_iso

namespace module_iso

variables (α : Type u) [comm_ring α]
variables (β : Type v) (γ : Type w) (α₁ : Type u₁) [module α β] [module α γ] [module α α₁]

variables {α β γ α₁}
include α

protected def refl : β ≃ₘ β :=
{ linear := is_linear_map.id
  ..equiv.refl β }

protected def symm (hbc : β ≃ₘ γ) : γ ≃ₘ β :=
{ linear := is_linear_map.inverse hbc.linear hbc.left_inv hbc.right_inv
  ..equiv.symm hbc.to_equiv }

protected def trans : β ≃ₘ γ → γ ≃ₘ α₁ → β ≃ₘ α₁ :=
λ hbc hca,
{ linear := is_linear_map.comp hca.linear hbc.linear
  ..equiv.trans hbc.to_equiv hca.to_equiv }

end module_iso

theorem gsmul_sub (α : Type u) [add_group α] (a : α) :
  ∀ i j : int, gsmul a (i - j) = gsmul a i - gsmul a j :=
begin
  intros i j,
  rw sub_eq_add_neg,
  rw sub_eq_add_neg,
  rw gsmul_add,
  rw gsmul_neg
end

theorem add_gsmul (α : Type u) [add_comm_group α] (a b : α) : ∀ n, gsmul (a + b) n = gsmul a n + gsmul b n :=
begin
  intro n,
  induction n,
  { rw ← int.coe_nat_eq,
    rw smul_coe_nat,
    rw smul_coe_nat,
    rw smul_coe_nat,
    rw add_monoid.add_smul },
  { rw int.neg_succ_of_nat_eq,
    rw gsmul_neg,
    rw gsmul_neg,
    rw gsmul_neg,
    rw gsmul_add,
    rw gsmul_add,
    rw gsmul_add,
    rw smul_coe_nat,
    rw smul_coe_nat,
    rw smul_coe_nat,
    rw add_monoid.add_smul,
    simp }
end

theorem sub_gsmul (α : Type u) [add_comm_group α] (a b : α) : ∀ n, gsmul (a - b) n = gsmul a n - gsmul b n :=
begin
  intro n,
  rw sub_eq_add_neg,
  rw sub_eq_add_neg,
  rw add_gsmul,
  rw neg_gsmul
end

theorem gsmul_smul (α : Type u) (β : Type v) [ring α] [module α β] (r : α) (x : β) :
  ∀ n:ℤ, gsmul (r • x) n = r • gsmul x n :=
begin
  intro n,
  cases n,
  { induction n with n ih,
    { simp },
    { rw nat.succ_eq_add_one,
      rw int.of_nat_add,
      simp [gsmul_add] at ih ⊢,
      rw ih,
      rw smul_add } },
  { rw int.neg_succ_of_nat_eq,
    rw gsmul_neg,
    rw gsmul_neg,
    rw gsmul_add,
    induction n with n ih,
    { simp [gsmul_one] },
    { simpa [gsmul_add, ih, smul_add] using ih } }
end

namespace multiset

variable {α : Type u}

@[simp] theorem map_id (s : multiset α) : map id s = s :=
quot.induction_on s $ λ l, congr_arg coe $ list.map_id _

end multiset

namespace list

theorem map_neg {α : Type u} [add_comm_group α] :
  ∀ L:list α, (L.map (λ x, -x)).sum = -L.sum
| []     := by simp
| (h::t) := by simp [map_neg t]

theorem sum_singleton {α : Type u} [add_group α] {x : α} :
  list.sum [x] = x :=
calc list.sum [x] = x + list.sum [] : list.sum_cons
              ... = x + 0 : congr_arg _ list.sum_nil
              ... = x : add_zero x

end list

namespace finsupp

variables {α : Type u} {β : Type v} [add_comm_group β] {a : α} {b b₁ b₂ : β}

variables {α₁ : Type u₁}

variables {γ : Type w} [add_comm_group γ]

@[simp] lemma single_neg : single a (-b) = -single a b :=
ext $ assume a',
begin
  by_cases h : a = a',
  { rw [h, neg_apply, single_eq_same, single_eq_same] },
  { rw [neg_apply, single_eq_of_ne h, single_eq_of_ne h, neg_zero] }
end

@[simp] lemma single_sub : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
by simp

theorem sum_neg_index' {g : α →₀ β} {h : α → β → γ}:
  (∀ (a : α) (b₁ b₂ : β), h a (b₁ - b₂) = h a b₁ - h a b₂) → finsupp.sum (-g) h = -finsupp.sum g h :=
begin
  intro H,
  rw ← zero_sub,
  rw sum_sub_index H,
  rw sum_zero_index,
  rw zero_sub
end

@[simp] theorem finsum_apply {S : finset α₁} {f : α₁ → α →₀ β} {z : α} :
  (S.sum f) z = S.sum (λ x, f x z) :=
eq.symm $ finset.sum_hom (λ g : α →₀ β, g z) rfl (λ x y, rfl)

end finsupp

variables (α : Type u) [comm_ring α]
variables (β : Type v) (γ : Type w) (α₁ : Type u₁) [module α β] [module α γ] [module α α₁]

namespace tensor_product

def free_abelian_group : Type (max v w) := β × γ →₀ ℤ

instance free_abelian_group.has_coe_to_fun : has_coe_to_fun (free_abelian_group β γ) :=
finsupp.has_coe_to_fun

instance free_abelian_group.add_comm_monoid : add_comm_monoid (free_abelian_group β γ) :=
finsupp.add_comm_monoid

instance free_abelian_group.add_comm_group : add_comm_group (free_abelian_group β γ) :=
finsupp.add_comm_group

theorem structural_theorem (f : free_abelian_group β γ) :
  ∃ S : finset (free_abelian_group β γ), (∀ g ∈ S, ∃ (x : β) (y : γ) (n : ℤ) (H : n ≠ 0), g = finsupp.single (x, y) n) ∧ S.sum id = f :=
begin
  rcases f with ⟨f, ⟨hf⟩⟩,
  cases hf with S hs,
  existsi S.image (λ z, finsupp.single z.val $ f z.val : {a : β × γ | f a ≠ 0} → free_abelian_group β γ),
  split,
  { intros g hg,
    rw finset.mem_image at hg,
    rcases hg with ⟨z, hzs, hg⟩,
    cases z with z hz,
    cases z with x y,
    exact ⟨x, y, f (x, y), hz, by simp [hg]⟩ },
  { rw finset.sum_image,
    { apply finsupp.ext,
      intro z,
      by_cases hz : f z = 0,
      { simp,
        rw ← finset.sum_subset (finset.empty_subset S),
        simpa using hz.symm,
        intros x hx hnx,
        rw id,
        rw finsupp.single_apply,
        have h2 : ¬x.val = z := λ hxz, x.property (by rwa hxz),
        rw if_neg h2 },
      { simp,
        have h1 : finset.singleton (⟨z, hz⟩ : {a : β × γ | f a ≠ 0}) ⊆ S := λ x hx, hs x,
        rw ← finset.sum_subset h1,
        rw finset.sum_singleton,
        rw id,
        rw finsupp.single_apply,
        rw if_pos rfl,
        refl,
        intros x hx hnxz,
        rw finset.mem_singleton at hnxz,
        rw id,
        rw finsupp.single_apply,
        have h2 : ¬x.val = z := λ hxz, hnxz (subtype.eq hxz),
        rw if_neg h2 } },
    { intros x hx y hy hxy,
      by_contradiction hnxy,
      have hxyx : @@coe_fn (free_abelian_group.has_coe_to_fun β γ) (finsupp.single (x.val) (f (x.val))) x.val
        = @@coe_fn (free_abelian_group.has_coe_to_fun β γ) (finsupp.single (y.val) (f (y.val))) x.val := by rw hxy,
      rw finsupp.single_apply at hxyx,
      rw finsupp.single_apply at hxyx,
      rw if_pos rfl at hxyx,
      have h1 : ¬y.val = x.val := λ hyx, hnxy (subtype.eq hyx.symm),
      rw if_neg h1 at hxyx,
      exact x.property hxyx } }
end

variables α {β γ}
include α

namespace relators

def pair_add : β → γ → γ → ℤ → free_abelian_group β γ :=
λ x y₁ y₂ n, finsupp.single (x, y₁) n + finsupp.single (x, y₂) n - finsupp.single (x, y₁ + y₂) n

def add_pair : β → β → γ → ℤ → free_abelian_group β γ :=
λ x₁ x₂ y n, finsupp.single (x₁, y) n + finsupp.single (x₂, y) n - finsupp.single (x₁ + x₂, y) n

def smul_trans : α → β → γ → ℤ → free_abelian_group β γ :=
λ r x y n, finsupp.single (r • x, y) n - finsupp.single (x, r • y) n

variables α β γ

def smul_aux : α → β × γ → ℤ → free_abelian_group β γ :=
λ r f y, finsupp.single (r • f.fst, f.snd) y

variables {α β γ}

theorem pair_add.neg (x : β) (y₁ y₂ : γ) (n : ℤ) :
  -pair_add α x y₁ y₂ n = pair_add α x y₁ y₂ (-n) :=
begin
  unfold pair_add,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp,
  repeat { rw add_comm, rw add_assoc }
end

theorem pair_add.smul (r : α) (x : β) (y₁ y₂ : γ) (n : ℤ) :
  finsupp.sum (pair_add α x y₁ y₂ n) (smul_aux α β γ r) = relators.pair_add α (r • x) y₁ y₂ n :=
begin
  unfold pair_add,
  rw finsupp.sum_sub_index,
  rw finsupp.sum_add_index,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux] },
  repeat { refl }
end

theorem add_pair.neg (x₁ x₂ : β) (y : γ) (n : ℤ) :
  -add_pair α x₁ x₂ y n = add_pair α x₁ x₂ y (-n) :=
begin
  unfold add_pair,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp,
  repeat { rw add_comm, rw add_assoc }
end

theorem add_pair.smul (r : α) (x₁ x₂ : β) (y : γ) (n : ℤ) :
  finsupp.sum (add_pair α x₁ x₂ y n) (smul_aux α β γ r) = relators.add_pair α (r • x₁) (r • x₂) y n :=
begin
  unfold add_pair,
  rw finsupp.sum_sub_index,
  rw finsupp.sum_add_index,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux, smul_add] },
  repeat { refl }
end

theorem smul_trans.neg (r : α) (x : β) (y : γ) (n : ℤ) :
  -smul_trans α r x y n = smul_trans α r x y (-n) :=
begin
  unfold smul_trans,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp
end

theorem smul_trans.smul (r r' : α) (x : β) (y : γ) (n : ℤ) :
  finsupp.sum (smul_trans α r' x y n) (smul_aux α β γ r) = relators.smul_trans α r' (r • x) y n :=
begin
  unfold smul_trans,
  rw finsupp.sum_sub_index,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux, smul_add, smul_smul, mul_comm] },
  repeat { refl },
end

end relators

variables (α β γ)

def relators : set (free_abelian_group β γ) :=
{f | (∃ x y₁ y₂ n, f = relators.pair_add α x y₁ y₂ n) ∨
  (∃ x₁ x₂ y n, f = relators.add_pair α x₁ x₂ y n) ∨
  (∃ r x y n, f = relators.smul_trans α r x y n)}

theorem relators.zero_mem : (0 : free_abelian_group β γ ) ∈ relators α β γ :=
or.inl ⟨0, 0, 0, 0, by simpa [relators.pair_add, finsupp.single_zero]⟩

theorem relators.neg_mem : ∀ f, f ∈ relators α β γ → -f ∈ relators α β γ :=
begin
  intros f hf,
  rcases hf with hf | hf | hf;
  rcases hf with ⟨a, b, c, d, hf⟩,
  { from or.inl ⟨a, b, c, -d, by rw [hf, relators.pair_add.neg]⟩ },
  { from or.inr (or.inl ⟨a, b, c, -d, by rw [hf, relators.add_pair.neg]⟩) },
  { from or.inr (or.inr ⟨a, b, c, -d, by rw [hf, relators.smul_trans.neg]⟩) }
end

def closure : set (free_abelian_group β γ) :=
{f | ∃ (L : list (free_abelian_group β γ)),
  (∀ x ∈ L, x ∈ relators α β γ) ∧ L.sum = f}

def r : free_abelian_group β γ → free_abelian_group β γ → Prop :=
λ f g, f - g ∈ closure α β γ

local infix ≈ := r α β γ

theorem refl (f : free_abelian_group β γ) : f ≈ f :=
⟨[], by simp⟩

theorem symm (f g : free_abelian_group β γ) : f ≈ g → g ≈ f :=
λ ⟨L, hL, hLfg⟩, ⟨L.map (λ x, -x),
  λ x hx, let ⟨y, hyL, hyx⟩ := list.exists_of_mem_map hx in
    by rw ← hyx; exact relators.neg_mem α β γ y (hL y hyL),
  by simp [list.map_neg, hLfg]⟩

theorem trans (f g h : free_abelian_group β γ) : f ≈ g → g ≈ h → f ≈ h :=
λ ⟨L₁, hL₁, hLfg₁⟩ ⟨L₂, hL₂, hLfg₂⟩,
⟨L₁ ++ L₂,
 λ x hx, by rw [list.mem_append] at hx; from or.cases_on hx (hL₁ x) (hL₂ x),
 by simp [hLfg₁, hLfg₂]⟩

instance : setoid (free_abelian_group β γ) :=
⟨r α β γ, refl α β γ, symm α β γ, trans α β γ⟩

end tensor_product

def tensor_product {α} (β γ) [comm_ring α] [module α β] [module α γ] : Type (max v w) :=
quotient (tensor_product.setoid α β γ)

local infix ` ⊗ `:100 := tensor_product

namespace tensor_product

include α

def add : β ⊗ γ → β ⊗ γ → β ⊗ γ :=
quotient.lift₂ (λ f g, ⟦f + g⟧ : free_abelian_group β γ → free_abelian_group β γ → β ⊗ γ) $
λ f₁ f₂ g₁ g₂ ⟨L₁, hL₁, hLfg₁⟩ ⟨L₂, hL₂, hLfg₂⟩, quotient.sound
⟨L₁ ++ L₂,
 λ x hx, by rw [list.mem_append] at hx; from or.cases_on hx (hL₁ x) (hL₂ x),
 by rw [list.sum_append, hLfg₁, hLfg₂]; simp⟩

theorem add_assoc (f g h : β ⊗ γ) : add α β γ (add α β γ f g) h = add α β γ f (add α β γ g h) :=
quotient.induction_on₃ f g h $ λ m n k, quotient.sound $ by simp

def zero : β ⊗ γ := ⟦0⟧

theorem zero_add (f : β ⊗ γ) : add α β γ (zero α β γ) f = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

theorem add_zero (f : β ⊗ γ) : add α β γ f (zero α β γ) = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

def neg : β ⊗ γ → β ⊗ γ :=
quotient.lift (λ f, ⟦-f⟧ : free_abelian_group β γ → β ⊗ γ) $
λ f g ⟨L, hL, hLfg⟩, quotient.sound ⟨L.map (λ x, -x),
  λ x hx, let ⟨y, hyL, hyx⟩ := list.exists_of_mem_map hx in
    by rw ← hyx; exact relators.neg_mem α β γ y (hL y hyL),
  by simp [list.map_neg, hLfg]⟩

theorem add_left_neg (f : β ⊗ γ) : add α β γ (neg α β γ f) f = zero α β γ :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

theorem add_comm (f g : β ⊗ γ) : add α β γ f g = add α β γ g f :=
quotient.induction_on₂ f g $ λ m n, quotient.sound $ by simp

instance : add_comm_group (β ⊗ γ) :=
{ add          := add α β γ,
  add_assoc    := add_assoc α β γ,
  zero         := zero α β γ,
  zero_add     := zero_add α β γ,
  add_zero     := add_zero α β γ,
  neg          := neg α β γ,
  add_left_neg := add_left_neg α β γ,
  add_comm     := add_comm α β γ }

theorem mem_closure_of_finset {f : free_abelian_group β γ} :
  (∃ (S : finset (free_abelian_group β γ)) g,
     S.sum g = f ∧ ∀ x ∈ S, g x ∈ relators α β γ) →
  f ∈ closure α β γ :=
λ ⟨S, g, hSf, hSr⟩, begin
  cases S with ms hms,
  cases quot.exists_rep ms with L hL,
  existsi L.map g,
  split,
  { intros x hxL,
    rcases list.exists_of_mem_map hxL with ⟨y, hyL, hyx⟩,
    have hyms : y ∈ ms,
    { unfold has_mem.mem,
      unfold multiset.mem,
      rw ← hL,
      rw quot.lift_on,
      rwa @quot.lift_beta _ (list.perm.setoid (free_abelian_group β γ)).r,
      exact multiset.mem._proof_1 y },
    rw ← hyx,
    exact hSr y hyms },
  { change multiset.sum (multiset.map g ms) = f at hSf,
    rw ← hL at hSf,
    rw ← multiset.coe_sum,
    exact hSf }
end

private lemma zero_eq_zero : (0 : free_abelian_group β γ) = (0 : β × γ →₀ ℤ) := rfl

private lemma sum_zero_index (f : β × γ → ℤ → free_abelian_group β γ) :
  @finsupp.sum (β × γ) ℤ (free_abelian_group β γ) int.has_zero _ (0 : free_abelian_group β γ) f = 0 :=
begin
  rw zero_eq_zero,
  simp [finsupp.sum],
  refl
end

private lemma sum_zero_index' [add_comm_group α₁] (f : β × γ → ℤ → α₁) :
  @finsupp.sum (β × γ) ℤ α₁ int.has_zero _ (0 : free_abelian_group β γ) f = 0 :=
begin
  rw zero_eq_zero,
  simp [finsupp.sum]
end

def smul : α → β ⊗ γ → β ⊗ γ :=
λ r, quotient.lift (λ f, ⟦f.sum (relators.smul_aux α β γ r)⟧ : free_abelian_group β γ → β ⊗ γ) $
λ f g ⟨L, hL, hLfg⟩, quotient.sound
begin
  clear _fun_match,
  induction L generalizing f g,
  { existsi ([]),
    have : f = g,
      by simpa [add_neg_eq_zero] using hLfg.symm,
    simp [this] },
  { specialize L_ih (λ z hzt, hL z (or.inr hzt)) (L_tl.sum) (0:free_abelian_group β γ),
    specialize L_ih ⟨L_tl,
      λ z hzt, hL z (or.inr hzt),
      eq.symm (sub_zero _)⟩,
    specialize L_ih (eq.symm $ sub_zero _),
    rcases L_ih with ⟨L', hL', hLfg'⟩,
    rw [sum_zero_index] at hLfg',
    simp at hLfg',
    rcases hL L_hd (or.inl rfl) with h | h | h,
    { rcases h with ⟨x, y₁, y₂, n, h⟩,
      existsi list.cons (relators.pair_add α (r • x) y₁ y₂ n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inl ⟨r • x, y₁, y₂, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw list.sum_cons,
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.pair_add.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } },
    { rcases h with ⟨x₁, x₂, y, n, h⟩,
      existsi list.cons (relators.add_pair α (r • x₁) (r • x₂) y n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inr $ or.inl ⟨r • x₁, r • x₂, y, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw list.sum_cons,
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.add_pair.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } },
    { rcases h with ⟨r', x, y, n, h⟩,
      existsi list.cons (relators.smul_trans α r' (r • x) y n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inr $ or.inr ⟨r', r • x, y, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw list.sum_cons,
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.smul_trans.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } } }
end

protected theorem smul_add (r : α) (f g : β ⊗ γ) : smul α β γ r (add α β γ f g) = add α β γ (smul α β γ r f) (smul α β γ r g) :=
quotient.induction_on₂ f g $ λ m n, quotient.sound $ by rw [finsupp.sum_add_index]; all_goals { intros, simp [relators.smul_aux], try {refl} }

protected theorem add_smul (r₁ r₂ : α) (f : β ⊗ γ) : smul α β γ (r₁ + r₂) f = add α β γ (smul α β γ r₁ f) (smul α β γ r₂ f) :=
quotient.induction_on f $ λ m, quotient.sound $
begin
  unfold relators.smul_aux,
  simp [add_smul],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  apply symm,
  apply mem_closure_of_finset,
  existsi S,
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    existsi id,
    split,
    { simp,
      rw sum_zero_index,
      rw sum_zero_index,
      rw sum_zero_index,
      simp },
    { intros x hx,
      exfalso,
      exact hx } },
  { intros g T hgT ih m hS hSm,
    rcases hS g (finset.mem_insert_self g T) with ⟨x, y, n, H, h⟩,
    rcases ih (T.sum id) (λ g' hg', hS g' $
      finset.mem_insert_of_mem hg') rfl with ⟨φ', hst', hss'⟩,
    existsi (λ f, if f = g then finsupp.single (r₁ • x, y) n +
      finsupp.single (r₂ • x, y) n -
      finsupp.single (r₁ • x + r₂ • x, y) n else φ' f),
    split,
    { rw finset.sum_insert,
      rw finset.sum_insert,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw if_pos rfl,
      rw h,
      rw id.def,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      have h1 : finset.sum T
        (λ (f : free_abelian_group β γ),
           ite (f = finsupp.single (x, y) n)
             (finsupp.single (r₁ • x, y) n + finsupp.single (r₂ • x, y) n -
                finsupp.single (r₁ • x + r₂ • x, y) n)
             (φ' f)) = finset.sum T φ',
      { apply finset.sum_congr,
        { refl },
        { intros g' hg',
          have h1 : g' ≠ g,
          { intro hgg',
            rw hgg' at hg',
            exact hgT hg' },
          rw h at h1,
          rw if_neg h1 } },
      rw h1,
      rw hst',
      unfold prod.fst,
      unfold prod.snd,
      simp,
      all_goals { intros,
        try {rw finsupp.single_zero},
        try {rw finsupp.single_zero},
        try {rw finsupp.single_add},
        try {refl},
        try {refl},
        try {exact hgT} } },
    { intros f' hf',
      rw finset.mem_insert at hf',
      cases hf',
      { dsimp,
        rw if_pos hf',
        from or.inr (or.inl ⟨r₁ • x, r₂ • x, y, n, rfl⟩) },
      { have h1 : f' ≠ g,
        { intro hfg',
          rw hfg' at hf',
          exact hgT hf' },
        dsimp,
        rw if_neg h1,
        from hss' f' hf' } } }
end

protected theorem mul_smul (r₁ r₂ : α) (f : β ⊗ γ) : smul α β γ (r₁ * r₂) f = smul α β γ r₁ (smul α β γ r₂ f) :=
quotient.induction_on f $ λ m, quotient.sound $
begin
  unfold relators.smul_aux,
  simp [mul_smul],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  apply symm,
  apply mem_closure_of_finset,
  existsi S,
  existsi (λ f, 0 : free_abelian_group β γ → free_abelian_group β γ),
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    split,
    { simp,
      rw sum_zero_index,
      rw sum_zero_index,
      rw sum_zero_index,
      simp },
    { intros x hx,
      exfalso,
      exact hx } },
  { intros g T hgT ih m hS hSm,
    rcases hS g (finset.mem_insert_self g T) with ⟨x, y, n, H, h⟩,
    rcases ih (T.sum id) (λ g' hg', hS g' $
      finset.mem_insert_of_mem hg') rfl with ⟨hst', hss'⟩,
    split,
    { rw finset.sum_insert,
      rw finset.sum_insert,
      rw finset.sum_const_zero,
      rw finset.sum_const_zero at hst',
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw h,
      rw id.def,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      unfold prod.fst,
      unfold prod.snd,
      rw add_comm_group.zero_add,
      rw hst',
      simp,
      all_goals { intros,
        try {rw finsupp.single_zero},
        try {rw finsupp.single_zero},
        try {rw finsupp.single_add},
        try {refl},
        try {refl},
        try {exact hgT} } },
    { intros f' hf',
      dsimp,
      exact relators.zero_mem α β γ } }
end

protected theorem one_smul (f : β ⊗ γ) : smul α β γ 1 f = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp [relators.smul_aux]

instance : module α (β ⊗ γ) :=
{ smul     := smul α β γ,
  smul_add := tensor_product.smul_add α β γ,
  add_smul := tensor_product.add_smul α β γ,
  mul_smul := tensor_product.mul_smul α β γ,
  one_smul := tensor_product.one_smul α β γ }

@[simp] lemma add_quot (f g : free_abelian_group β γ) : @has_add.add (β ⊗ γ) _ (⟦f⟧ : β ⊗ γ) ⟦g⟧ = ⟦f + g⟧ := rfl
@[simp] lemma neg_quot (f : free_abelian_group β γ) : @has_neg.neg (β ⊗ γ) _ (⟦f⟧ : β ⊗ γ) = ⟦-f⟧ := rfl

variables {α} (β γ)

def proj : β → γ → β ⊗ γ :=
λ x y, ⟦finsupp.single (x, y) 1⟧

def proj.is_bilinear_map : is_bilinear_map (proj β γ) :=
{ add_pair   := λ x y z, quotient.sound $ setoid.symm $
    ⟨[(finsupp.single (x, z) 1 +
         finsupp.single (y, z) 1 -
         finsupp.single (x + y, z) 1 : free_abelian_group β γ)],
     λ u hu, or.inr $ or.inl ⟨x, y, z, 1, list.eq_of_mem_singleton hu⟩,
     list.sum_singleton⟩,
  pair_add   := λ x y z, quotient.sound $ setoid.symm $
    ⟨[(finsupp.single (x, y) 1 +
         finsupp.single (x, z) 1 -
         finsupp.single (x, y + z) 1 : free_abelian_group β γ)],
     λ u hu, or.inl ⟨x, y, z, 1, list.eq_of_mem_singleton hu⟩,
     list.sum_singleton⟩,
  smul_trans := λ r₁ r₂ x y, quotient.sound $ setoid.symm $
    begin
      simp [relators.smul_aux],
      rw finsupp.sum_single_index,
      unfold prod.fst,
      unfold prod.snd,
      existsi ([(finsupp.single (r₂ • (r₁ • x), y) 1 -
        finsupp.single (r₁ • x, r₂ • y) 1 : free_abelian_group β γ)]),
      split,
      { intros z hz,
        rw list.mem_singleton at hz,
        rw hz,
        from or.inr (or.inr ⟨r₂, r₁ • x, y, 1, by simp [relators.smul_trans]⟩) },
      simp [list.sum_singleton],
      { rw ← mul_smul,
        simp [mul_comm] },
      { rw finsupp.single_zero,
        refl }
    end }

namespace universal_property

variables {β γ α₁}
variables {f : β → γ → α₁} (hf : is_bilinear_map f)
include hf

def factor_aux : free_abelian_group β γ → α₁ :=
λ g : free_abelian_group β γ, (g.sum (λ z n, gsmul (f z.fst z.snd) n))

theorem factor_equiv : ∀ g₁ g₂ : free_abelian_group β γ, g₁ ≈ g₂ → factor_aux hf g₁ = factor_aux hf g₂ :=
λ g₁ g₂ ⟨L, hL, hgL⟩,
begin
  clear _fun_match _x,
  induction L generalizing hgL hL g₂ g₁,
  { simp at hgL,
    replace hgL := hgL.symm,
    rw add_neg_eq_zero at hgL,
    rw hgL },
  { specialize L_ih (L_tl.sum) 0,
    specialize L_ih (λ x hx, hL x (list.mem_cons_of_mem L_hd hx)),
    specialize L_ih (sub_zero _).symm,
    dsimp at *,
    rw ← add_neg_eq_zero,
    rw ← sub_eq_add_neg at hgL ⊢,
    unfold factor_aux at L_ih ⊢,
    rw ← finsupp.sum_sub_index,
    rw ← hgL,
    rw list.sum_cons,
    rw finsupp.sum_add_index,
    rw L_ih,
    rw sum_zero_index',
    specialize hL L_hd,
    specialize hL (or.inl rfl),
    rcases hL with h | h | h,
    { rcases h with ⟨x, y₁, y₂, n, h⟩,
      rw h,
      unfold relators.pair_add,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← add_gsmul,
      rw ← sub_gsmul,
      rw hf.pair_add,
      simp,
      { rw gsmul_zero },
      { rw gsmul_zero },
      { rw gsmul_zero },
      { intros, rw gsmul_zero },
      { intros, rw gsmul_add },
      { intros, rw gsmul_sub } },
    { rcases h with ⟨x₁, x₂, y, n, h⟩,
      rw h,
      unfold relators.add_pair,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← add_gsmul,
      rw ← sub_gsmul,
      rw hf.add_pair,
      simp,
      { rw gsmul_zero },
      { rw gsmul_zero },
      { rw gsmul_zero },
      { intros, rw gsmul_zero },
      { intros, rw gsmul_add },
      { intros, rw gsmul_sub } },
    { rcases h with ⟨r, x, y, n, h⟩,
      rw h,
      unfold relators.smul_trans,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← sub_gsmul,
      rw hf.smul_pair,
      rw hf.pair_smul,
      simp,
      { rw gsmul_zero },
      { rw gsmul_zero },
      { intros, rw gsmul_sub } },
    { intros, rw gsmul_zero },
    { intros, rw gsmul_add },
    { intros, rw gsmul_sub } }
end

def factor : β ⊗ γ → α₁ :=
quotient.lift (factor_aux hf) (factor_equiv hf)

theorem factor_add : ∀ g₁ g₂ : β ⊗ γ, factor hf (g₁ + g₂) = factor hf g₁ + factor hf g₂ :=
λ x y, quotient.induction_on₂ x y
begin
  intros m n,
  simp [universal_property.factor],
  simp [universal_property.factor_aux],
  rw finsupp.sum_add_index,
  { intros, rw gsmul_zero },
  { intros, rw gsmul_add }
end

theorem factor_smul : ∀ (r : α) (g : β ⊗ γ), factor hf (r • g) = r • factor hf g :=
λ r x, quotient.induction_on x
begin
  intros m,
  simp [has_scalar.smul, smul, relators.smul_aux],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    unfold universal_property.factor,
    unfold universal_property.factor_aux,
    simp [finsupp.sum_zero_index],
    rw sum_zero_index,
    rw sum_zero_index',
    simp },
  { intros n T hnT ih m hS hSm,
    unfold universal_property.factor,
    unfold universal_property.factor_aux,
    simp,
    specialize ih (finset.sum T id),
    specialize ih (λ g hg, hS g (finset.mem_insert_of_mem hg)),
    specialize ih rfl,
    unfold universal_property.factor at ih,
    unfold universal_property.factor_aux at ih,
    simp at ih,
    rw finset.sum_insert,
    rw finsupp.sum_add_index,
    rw finsupp.sum_add_index,
    rw finsupp.sum_add_index,
    rw ih,
    specialize hS n (finset.mem_insert_self n T),
    rcases hS with ⟨x', y', n', H', hn'⟩,
    rw hn',
    rw finsupp.sum_single_index,
    rw finsupp.sum_single_index,
    rw finsupp.sum_single_index,
    rw hf.smul_pair,
    rw gsmul_smul,
    rw smul_add,
    { rw gsmul_zero },
    { rw gsmul_zero },
    { rw finsupp.single_zero, refl },
    { intros, rw gsmul_zero },
    { intros, rw gsmul_add },
    { intros, rw gsmul_zero },
    { intros, rw gsmul_add },
    { intros, rw finsupp.single_zero, refl },
    { intros, rw finsupp.single_add },
    { exact hnT } }
end

theorem factor_linear : is_linear_map (factor hf) :=
{ add  := factor_add hf,
  smul := factor_smul hf }

theorem factor_commutes : ∀ x y, factor hf (proj β γ x y) = f x y :=
begin
  funext,
  simp [function.comp, proj, factor, factor_aux],
  simp [finsupp.sum_single_index]
end

theorem factor_unique (h : β ⊗ γ → α₁) (H : is_linear_map h)
  (hh : ∀ x y, h (proj β γ x y) = f x y) :
  h = factor hf :=
begin
  apply funext,
  intro x,
  apply quotient.induction_on x,
  intro y,
  unfold universal_property.factor,
  unfold universal_property.factor_aux,
  simp,
  rcases structural_theorem β γ y with ⟨S, hS, hSy⟩,
  revert hSy hS y,
  apply finset.induction_on S,
  { intros y hS hSy,
    rw ← hSy,
    rw finset.sum_empty,
    rw sum_zero_index',
    exact is_linear_map.zero H },
  { intros n T hnT ih y hS hSy,
    rw ← hSy,
    rw finset.sum_insert,
    rw ← add_quot,
    rw H.add,
    rw finsupp.sum_add_index,
    rw id.def,
    specialize ih (T.sum id),
    specialize ih (λ z hz, hS z (finset.mem_insert_of_mem hz)),
    specialize ih rfl,
    rw ih,
    specialize hS n,
    specialize hS (finset.mem_insert_self n T),
    rcases hS with ⟨x', y', n', H', hn'⟩,
    rw hn',
    rw finsupp.sum_single_index,
    specialize hh x' y',
    simp [function.comp, proj] at hh,
    clear H' hn',
    suffices : h ⟦finsupp.single (x', y') n'⟧ = gsmul (f x' y') n',
    { rw this },
    cases n',
    { induction n' with n' ih',
      { rw int.of_nat_zero,
        rw finsupp.single_zero,
        rw gsmul_zero,
        exact H.zero },
      { rw int.of_nat_succ,
        rw finsupp.single_add,
        rw ← add_quot,
        rw H.add,
        rw [ih', hh],
        rw gsmul_add,
        rw gsmul_one } },
    { induction n' with n' ih',
      { rw int.neg_succ_of_nat_eq,
        rw finsupp.single_neg,
        rw gsmul_neg,
        rw finsupp.single_add,
        simp,
        rw ← neg_quot,
        rw H.neg,
        rw hh },
      { rw int.neg_succ_of_nat_coe,
        rw int.neg_succ_of_nat_eq at ih',
        rw int.coe_nat_add,
        rw finsupp.single_neg at ih' ⊢,
        rw ← neg_quot at ih' ⊢,
        rw H.neg at ih' ⊢,
        rw nat.succ_eq_add_one,
        rw finsupp.single_add,
        rw ← add_quot,
        rw H.add,
        rw neg_add,
        rw int.coe_nat_add,
        rw int.coe_nat_eq 1,
        rw int.of_nat_one,
        rw ih',
        rw hh,
        simp [gsmul_add, gsmul_neg] } },
    { rw gsmul_zero },
    { intros, rw gsmul_zero },
    { intros, rw gsmul_add },
    { exact hnT } }
end

end universal_property

instance universal_property {f : β → γ → α₁} (hf : is_bilinear_map f) :
  type_singleton { h : β ⊗ γ → α₁ // ∃ (H : is_linear_map h), ∀ x y, h (proj β γ x y) = f x y } :=
{ default := ⟨universal_property.factor hf,
    universal_property.factor_linear hf,
    universal_property.factor_commutes hf⟩,
  unique  := λ ⟨h, H, hh⟩, subtype.eq $
    universal_property.factor_unique hf h H hh }

variables {β γ α₁}
protected theorem ext {f g : β ⊗ γ → α₁} (hf : is_linear_map f) (hg : is_linear_map g)
  (h : ∀ x y, f (proj β γ x y) = g (proj β γ x y)) (z : β ⊗ γ) : f z = g z :=
have h1 : _ := universal_property.factor_unique
  (is_bilinear_map.comp (proj.is_bilinear_map β γ) hg)
  f hf h,
have h2 : _ := universal_property.factor_unique
  (is_bilinear_map.comp (proj.is_bilinear_map β γ) hg)
  g hg (λ x y, rfl),
(congr_fun h1 z).trans (congr_fun h2 z).symm

variables (β γ)

protected def id : β ⊗ α ≃ₘ β :=
let hba1 : β → α → β := λ x y, y • x in
have hba2 : is_bilinear_map hba1,
by refine {..}; intros; simp [hba1, smul_add, add_smul, smul_smul, mul_comm, mul_left_comm],
let hba3 : β ⊗ α → β := universal_property.factor hba2 in
have hba4 : _ := universal_property.factor_linear hba2,
have hba5 : _ := universal_property.factor_commutes hba2,
let hb1 : β → β ⊗ α := λ x, proj β α x 1 in
have hb2 : is_linear_map hb1, from
{ add  := λ x y, (proj.is_bilinear_map β α).add_pair x y 1,
  smul := λ r x, by simpa using (proj.is_bilinear_map β α).smul_trans r 1 x 1 },
have hbb1 : ∀ (x : β) (y : α), hb1 (hba3 (proj β α x y)) = proj β α x y,
from λ x y, calc
        hb1 (hba3 (proj β α x y))
      = proj β α (y • x) 1 : congr_arg hb1 (hba5 _ _)
  ... = proj β α (y • x) (1 • 1) : by simp
  ... = (y * 1) • proj β α x 1 : (proj.is_bilinear_map β α).smul_trans y 1 x 1
  ... = (1 * y) • proj β α x 1 : by simp
  ... = proj β α (1 • x) (y • 1) : eq.symm $ (proj.is_bilinear_map β α).smul_trans 1 y x 1
  ... = proj β α x y : by simp,
{ to_fun    := hba3,
  inv_fun   := hb1,
  left_inv  := tensor_product.ext (hb2.comp hba4) is_linear_map.id hbb1,
  right_inv := λ x, by simp *,
  linear    := hba4 }

protected def comm : β ⊗ γ ≃ₘ γ ⊗ β :=
let hbg1 : β → γ → γ ⊗ β := λ x y, proj γ β y x in
have hbg2 : is_bilinear_map hbg1, from
{ add_pair   := λ x y z, (proj.is_bilinear_map γ β).pair_add z x y,
  pair_add   := λ x y z, (proj.is_bilinear_map γ β).add_pair y z x,
  smul_trans := λ r₁ r₂ x y, by simpa [mul_comm] using (proj.is_bilinear_map γ β).smul_trans r₂ r₁ y x },
let hbg3 : β ⊗ γ → γ ⊗ β := universal_property.factor hbg2 in
have hbg4 : _ := universal_property.factor_linear hbg2,
have hbg5 : _ := universal_property.factor_commutes hbg2,
let hgb1 : γ → β → β ⊗ γ := λ x y, proj β γ y x in
have hgb2 : is_bilinear_map hgb1, from
{ add_pair   := λ x y z, (proj.is_bilinear_map β γ).pair_add z x y,
  pair_add   := λ x y z, (proj.is_bilinear_map β γ).add_pair y z x,
  smul_trans := λ r₁ r₂ x y, by simpa [mul_comm] using (proj.is_bilinear_map β γ).smul_trans r₂ r₁ y x },
let hgb3 : γ ⊗ β → β ⊗ γ := universal_property.factor hgb2 in
have hgb4 : _ := universal_property.factor_linear hgb2,
have hgb5 : _ := universal_property.factor_commutes hgb2,
have hbb1 : ∀ x y, (hgb3 ∘ hbg3) (proj β γ x y) = proj β γ x y,
from λ x y, by simp [function.comp, *],
have hbb2 : is_linear_map (hgb3 ∘ hbg3) := hgb4.comp hbg4,
have hbb3 : _ := tensor_product.ext hbb2 is_linear_map.id hbb1,
have hgg1 : ∀ x y, (hbg3 ∘ hgb3) (proj γ β x y) = proj γ β x y,
from λ x y, by simp [function.comp, *],
have hgg2 : is_linear_map (hbg3 ∘ hgb3) := hbg4.comp hgb4,
have hgg3 : _ := tensor_product.ext hgg2 is_linear_map.id hgg1,
{ to_fun    := hbg3,
  inv_fun   := hgb3,
  left_inv  := hbb3,
  right_inv := hgg3,
  linear    := hbg4 }

end tensor_product
