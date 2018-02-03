import algebra.ring data.set.basic tactic.ring data.equiv data.quot

-- remove "data.equiv" in PR version
-- needs hom and prime ideals

universes u v

-- <move to algebra.ring>

class is_hom {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_hom f] {x y : α}

attribute [simp] map_add
attribute [simp] map_mul
attribute [simp] map_one

@[simp] lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

@[simp] lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

@[simp] lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

end is_hom

class is_ideal (α : Type u) [comm_ring α] (S : set α) : Prop :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

namespace is_ideal

variables {α : Type u} [comm_ring α] {S : set α} [is_ideal α S] {x y z : α}
include S

attribute [simp] zero_mem

lemma neg_mem : x ∈ S → -x ∈ S :=
λ hx, have h : x * -1 ∈ S, from is_ideal.mul_mem hx, by simpa using h

lemma sub_mem : x ∈ S → y ∈ S → x - y ∈ S :=
λ hx hy, have h : x + -y ∈ S, from add_mem hx $ neg_mem hy, by simpa using h

lemma mul_mem' : y ∈ S → x * y ∈ S :=
λ hy, have h : y * x ∈ S, from mul_mem hy, by rwa [mul_comm]

end is_ideal

-- </move>

-- <move to data.quot>

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

-- </move>

namespace loc

variables (α : Type u) [comm_ring α] (S : set α)

class is_submonoid : Prop :=
(one_mem : (1:α) ∈ S)
(mul_mem : ∀ {s t}, s ∈ S → t ∈ S → s*t ∈ S)

variable [is_submonoid α S]

def r : α × S → α × S → Prop :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ∃ t ∈ S, t * (r₁ * s₂ - r₂ * s₁) = 0

local infix ≈ := r α S

theorem refl : ∀ (x : α × S), x ≈ x :=
λ ⟨r₁, s₁, hs₁⟩, ⟨1, is_submonoid.one_mem S, by simp⟩

theorem symm : ∀ (x y : α × S), x ≈ y → y ≈ x :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩, ⟨t, hts, calc
        t * (r₂ * s₁ - r₁ * s₂)
      = -(t * (r₁ * s₂ - r₂ * s₁)) : by simp [mul_add]
  ... = 0 : by rw ht; simp⟩

theorem trans : ∀ (x y z : α × S), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
⟨t * t' * s₂, is_submonoid.mul_mem (is_submonoid.mul_mem hts hts') hs₂, calc
         t * t' * s₂ * (r₁ * s₃ - r₃ * s₁)
       = t' * s₃ * (t * (r₁ * s₂ - r₂ * s₁)) + t * s₁ * (t' * (r₂ * s₃ - r₃ * s₂)) : by simp [mul_left_comm, mul_add, mul_comm]
   ... = 0 : by rw [ht, ht']; simp⟩

instance : setoid (α × S) :=
⟨r α S, refl α S, symm α S, trans α S⟩

def loc := quotient $ loc.setoid α S

def add_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def add : loc α S → loc α S → loc α S :=
quotient.lift₂ (add_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * s₂ + r₂ * s₁) * (s₃ * s₄) - (r₃ * s₄ + r₄ * s₃) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * s₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * s₁ * s₃ : by ring
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

def neg_aux : α × S → loc α S :=
λ ⟨r, s, hs⟩, ⟦⟨-r, s, hs⟩⟧

def neg : loc α S → loc α S :=
quotient.lift (neg_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
quotient.sound ⟨t, hts, calc
        t * (-r₁ * s₂ - -r₂ * s₁)
      = -(t * (r₁ * s₂ - r₂ * s₁)) : by ring
  ... = 0 : by rw ht; simp⟩

def mul_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * r₂, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def mul : loc α S → loc α S → loc α S :=
quotient.lift₂ (mul_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * r₂) * (s₃ * s₄) - (r₃ * r₄) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * r₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * r₃ * s₁ : by simp [mul_left_comm, mul_add, mul_comm]
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

instance : comm_ring (loc α S) :=
by refine
{ add            := add α S,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := ⟦⟨0, 1, is_submonoid.one_mem S⟩⟧,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := neg α S,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := mul α S,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦⟨1, 1, is_submonoid.one_mem S⟩⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {cases a with r₁ s₁, cases s₁ with s₁ hs₁},
  try {cases b with r₂ s₂, cases s₂ with s₂ hs₂},
  try {cases c with r₃ s₃, cases s₃ with s₃ hs₃},
  apply quotient.sound,
  existsi (1:α),
  existsi is_submonoid.one_mem S,
  simp [mul_left_comm, mul_add, mul_comm] }

def of_comm_ring : α → loc α S :=
λ r, ⟦⟨r, 1, is_submonoid.one_mem S⟩⟧

instance : is_hom (of_comm_ring α S) :=
{ map_add := λ x y, quotient.sound $ by simp,
  map_mul := λ x y, quotient.sound $ by simp,
  map_one := rfl }

local infix ^ := monoid.pow

variable {α}

def powers (x : α) : set α := {y | ∃ n, x^n = y}

instance powers.is_submonoid (x : α) : is_submonoid α (powers x) :=
{ one_mem := ⟨0, by simp⟩,
  mul_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [pow_add, *]⟩ }

def away (x : α) := loc α (powers x)

def closure (S : set α) : set α := {y | ∃ (L:list α) (H:∀ x ∈ L, x ∈ S), L.prod = y }

instance closure.is_submonoid (S : set α) : is_submonoid α (closure S) :=
{ one_mem := ⟨[], by simp⟩,
  mul_mem := λ x₁ x₂ ⟨L₁, hLS₁, hL₁⟩ ⟨L₂, hLS₂, hL₂⟩,
    ⟨L₁ ++ L₂,
     λ x hx, or.cases_on (list.mem_append.1 hx) (hLS₁ x) (hLS₂ x),
     by simp [list.prod_append, *]⟩ }

variable α

def non_zero_divisors : set α := {x | ∀ z, x * z = 0 → z = 0}

instance non_zero_divisors.is_submonoid : is_submonoid α (non_zero_divisors α) :=
{ one_mem := λ z hz, by simpa using hz,
  mul_mem := λ x₁ x₂ hx₁ hx₂ z hz,
    have x₁ * (x₂ * z) = 0,
    by rwa mul_assoc at hz,
    hx₂ z $ hx₁ (x₂ * z) this }

def quotient_ring := loc α (non_zero_divisors α)

section quotient_ring

variables {β : Type u} [integral_domain β] [decidable_eq β]

lemma ne_zero_of_mem_non_zero_divisors {x : β} :
  x ∈ loc.non_zero_divisors β → x ≠ 0 :=
λ hm hz, have x * 1 = 0, by simp [hz], zero_ne_one (hm 1 this).symm

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} : x ≠ 0 → x * y = 0 → y = 0 :=
λ hnx hxy, match eq_zero_or_eq_zero_of_mul_eq_zero hxy with
| or.inl hx := false.elim $ hnx hx
| or.inr hy := hy
end

lemma mem_non_zero_divisors_of_ne_zero {x : β} :
  x ≠ 0 → x ∈ loc.non_zero_divisors β :=
λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx

variable β

def inv_aux : β × (non_zero_divisors β) → quotient_ring β :=
λ ⟨r, s, hs⟩, if h : r = 0 then
  ⟦⟨0, 1, is_submonoid.one_mem _⟩⟧
else ⟦⟨s, r, mem_non_zero_divisors_of_ne_zero h⟩⟧

def inv : quotient_ring β → quotient_ring β :=
quotient.lift (inv_aux β) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
begin
  have hrs : r₁ * s₂ - r₂ * s₁ = 0,
  { from hts _ ht },
  by_cases hr₁ : r₁ = 0;
  by_cases hr₂ : r₂ = 0;
  simp [inv_aux, hr₁, hr₂],
  { exfalso,
    simp [hr₁] at hrs,
    exact ne_zero_of_mem_non_zero_divisors hs₁
      (eq_zero_of_ne_zero_of_mul_eq_zero hr₂ hrs) },
  { exfalso,
    simp [hr₂] at hrs,
    exact ne_zero_of_mem_non_zero_divisors hs₂
      (eq_zero_of_ne_zero_of_mul_eq_zero hr₁ hrs) },
  { exact ⟨1, is_submonoid.one_mem _,
    by simpa [mul_comm] using congr_arg (λ x, -x) hrs⟩ }
end

instance quotient_ring.field.of_integral_domain : field (quotient_ring β) :=
by refine
{ loc.comm_ring β _ with
  inv := inv β,
  zero_ne_one := λ hzo, let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_mul_cancel := quotient.ind _ };
{ intros x hnx,
  cases x with x hx,
  cases hx with z hz,
  have : x ≠ 0,
    intro hx,
    apply hnx,
    apply quotient.sound,
    existsi (1:β),
    existsi is_submonoid.one_mem _,
    simp [hx],
    exact non_zero_divisors.is_submonoid β,
  simp [inv, inv_aux, inv_aux._match_1],
  rw dif_neg this,
  apply quotient.sound,
  existsi (1:β),
  existsi is_submonoid.one_mem _,
  ring,
  exact non_zero_divisors.is_submonoid β }

end quotient_ring

end loc

/- TODO:
1. Define localization at a prime ideal.
3. Prove that loc is a local ring if localizing at a prime ideal.
-/

-- Factoids (not to go to mathlib):

def frac_int_to_rat : loc.quotient_ring ℤ → ℚ :=
λ f, quotient.lift_on f (λ ⟨r, s, hs⟩, rat.mk r s) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
begin
  have hsnz₁ : s₁ ≠ 0,
  { from loc.ne_zero_of_mem_non_zero_divisors hs₁ },
  have hsnz₂ : s₂ ≠ 0,
  { from loc.ne_zero_of_mem_non_zero_divisors hs₂ },
  have htnz : t ≠ 0,
  { from loc.ne_zero_of_mem_non_zero_divisors hts },
  cases eq_zero_or_eq_zero_of_mul_eq_zero ht with htz hrs,
  {  exfalso,
     exact htnz htz },
  { change rat.mk r₁ s₁ = rat.mk r₂ s₂,
    rw sub_eq_zero at hrs,
    rwa rat.mk_eq hsnz₁ hsnz₂ }
end

lemma coe_denom_ne_zero (r : ℚ) : (↑r.denom:ℤ) ≠ 0 :=
λ hn, ne_of_gt r.pos $ int.of_nat_inj hn

def frac_int_of_rat : ℚ → loc.quotient_ring ℤ :=
λ r, ⟦⟨r.num, r.denom, λ z hz,
or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero hz)
  (λ hz, false.elim $ coe_denom_ne_zero r hz)
  id⟩⟧

theorem frac_int_to_rat_to_frac_int : ∀ f, frac_int_of_rat (frac_int_to_rat f) = f :=
λ f, quotient.induction_on f $ λ ⟨r, s, hs⟩, quotient.sound
⟨1, loc.is_submonoid.one_mem _,
   suffices (rat.mk r s).num * s = r * ↑(rat.mk r s).denom,
   from show 1 * ((rat.mk r s).num * s - r * ↑(rat.mk r s).denom) = 0,
     by simp [this],
   have hnd : (↑(rat.mk r s).denom:ℤ) ≠ 0,
     from coe_denom_ne_zero $ rat.mk r s,
   have hns : s ≠ 0,
     from loc.ne_zero_of_mem_non_zero_divisors hs,
   have _, from eq.symm $ rat.num_denom $ rat.mk r s,
   by rwa ← rat.mk_eq hnd hns ⟩

theorem rat_to_frac_int_to_rat : ∀ r, frac_int_to_rat (frac_int_of_rat r) = r :=
λ ⟨n, d, h, c⟩, eq.symm $ rat.num_denom _

def canonical : equiv (loc.quotient_ring ℤ) (ℚ) :=
⟨frac_int_to_rat, frac_int_of_rat,
   frac_int_to_rat_to_frac_int,
   rat_to_frac_int_to_rat⟩
