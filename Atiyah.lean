import algebra.ring algebra.field data.set.basic order.zorn tactic.norm_num

universes u v w

section set_rewrite

variable {α : Type u}

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
or.cases_on h id false.elim

@[simp] theorem mem_singleton (a : α) : a ∈ ({a} : set α) :=
or.inl rfl

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
or.inl H

@[simp] theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
⟨ eq_of_mem_singleton, mem_singleton_of_eq ⟩

end set_rewrite

-- page 1

class zero_ring (α : Type u) [comm_ring α] : Prop :=
(eq_zero : ∀ x:α, x = 0)

instance zero_ring_of_zero_eq_one {α : Type u} [comm_ring α] : (0:α)=1 → zero_ring α
| h := {_inst_1 with eq_zero := λ x, calc
  x = x * 1 : eq.symm $ mul_one x
  ... = x * 0 : congr_arg _ h.symm
  ... = 0 : mul_zero x}


-- page 2

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

@[simp] lemma map_zero : f 0 = 0 := calc
f 0 = f 0 + f 0 - f 0 : eq.symm $ add_sub_cancel (f 0) (f 0)
... = f (0 + 0) - f 0 : congr_arg (λ x, x - f 0) $ eq.symm $ map_add f
... = f 0 - f 0 : congr_arg (λ x, f x - f 0) $ zero_add 0
... = 0 : sub_self $ f 0

@[simp] lemma map_neg : f (-x) = -f x := calc
f (-x) = f (-x) + f x - f x : eq.symm $ add_sub_cancel (f (-x)) (f x)
... = f (-x + x) - f x : congr_arg (λ y, y - f x) $ eq.symm $ map_add f
... = f 0 - f x : congr_arg (λ y, f y - f x) $ neg_add_self x
... = 0 - f x : congr_arg (λ y, y - f x) $ map_zero f
... = -f x : zero_sub $ f x

@[simp] lemma map_sub : f (x - y) = f x - f y := calc
f (x - y) = f (x + -y) : congr_arg f $ sub_eq_add_neg x y
... = f x + f (-y) : map_add f
... = f x + -f y : congr_arg (λ z, f x + z) $ map_neg f
... = f x - f y : eq.symm $ sub_eq_add_neg (f x) (f y)

end is_hom

class subring (α : Type u) [comm_ring α] (S : set α) : Prop :=
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ {x}, x ∈ S → -x ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

namespace subring

variables (α : Type u) [comm_ring α] (S : set α) [subring α S]

instance : comm_ring S :=
{ add := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, add_mem hx hy⟩,
  add_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ add_assoc x y z,
  zero := ⟨0, eq.subst (add_neg_self (1:α)) $ add_mem (one_mem S) $ neg_mem $ one_mem S⟩,
  zero_add := λ ⟨x, hx⟩, subtype.eq $ zero_add x,
  add_zero := λ ⟨x, hx⟩, subtype.eq $ add_zero x,
  neg := λ ⟨x, hx⟩, ⟨-x, neg_mem hx⟩,
  add_left_neg := λ ⟨x, hx⟩, subtype.eq $ add_left_neg x,
  add_comm := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ add_comm x y,
  mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
  one := ⟨1, one_mem S⟩,
  one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
  mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
  left_distrib := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ left_distrib x y z,
  right_distrib := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ right_distrib x y z,
  mul_comm := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ mul_comm x y }

@[simp] lemma add (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ := rfl

@[simp] lemma mul (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ := rfl

instance is_hom : is_hom ((λ x, x) : S → α) :=
{ map_add := λ x y, by cases x; cases y; refl,
  map_mul := λ x y, by cases x; cases y; refl,
  map_one := rfl }

end subring

instance is_hom.comp (α : Type u) (β : Type v) (γ : Type w)
[comm_ring α] [comm_ring β] [comm_ring γ]
(g : β → γ) (f : α → β) [is_hom g] [is_hom f] : is_hom (g ∘ f) :=
{ map_add := λ x y, calc
    g (f (x + y)) = g (f x + f y) : congr_arg g $ is_hom.map_add f
    ... = g (f x) + g (f y) : is_hom.map_add g,
  map_mul := λ x y, calc
    g (f (x * y)) = g (f x * f y) : congr_arg g $ is_hom.map_mul f
    ... = g (f x) * g (f y) : is_hom.map_mul g,
  map_one := calc
    g (f 1) = g 1 : congr_arg g $ is_hom.map_one f
    ... = 1 : is_hom.map_one g }

class is_ideal (α : Type u) [comm_ring α] (S : set α) : Prop :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

namespace is_ideal

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]
include S

variable {S}
attribute [simp] zero_mem
attribute [simp] add_mem
attribute [simp] mul_mem
@[simp] lemma neg_mem : ∀ {x}, x ∈ S → -x ∈ S :=
λ x hx, set.mem_of_eq_of_mem (by norm_num : -x = x * -1) (mul_mem hx)
@[simp] lemma sub_mem : ∀ {x y}, x ∈ S → y ∈ S → x - y ∈ S :=
λ x y hx hy, set.mem_of_eq_of_mem (sub_eq_add_neg x y) (add_mem hx $ neg_mem hy)
variable S

instance : setoid α :=
{ r     := λ x y, x - y ∈ S,
  iseqv :=
    ⟨λ x, calc
      x - x = 0 : sub_self x
        ... ∈ S : zero_mem S,
    λ x y hxy, calc
      y - x = -(x - y)     : eq.symm (neg_sub x y)
        ... ∈ S            : neg_mem hxy,
    λ x y z hxy hyz, calc
      x - z = (x - y) + (y - z) : eq.symm (sub_add_sub_cancel x y z)
        ... ∈ S                 : add_mem hxy hyz ⟩ }

variables (α)

@[reducible] def coset := quotient (is_ideal.setoid S)

variables {α}

instance : comm_ring (quotient (is_ideal.setoid S)) :=
{
  add := quotient.lift₂ (λ m n, ⟦m + n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ + m₂) - (n₁ + n₂) = (m₁ - n₁) + (m₂ - n₂) : by norm_num
                      ... ∈ S                     : add_mem h₁ h₂ ),
  add_assoc := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) + c) - (a + (b + c)) = 0 : by norm_num
                              ... ∈ S : zero_mem S end),
  zero := ⟦0⟧,
  zero_add := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (0 + a) - (a) = 0 : by norm_num
              ... ∈ S : zero_mem S end),
  add_zero := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (a + 0) - (a) = 0 : by norm_num
              ... ∈ S : zero_mem S end),
  neg := quotient.lift (λ m, ⟦-m⟧) (λ m n h, quot.sound $ calc
    (-m) - (-n) = (m - n)*-1 : by norm_num
            ... ∈ S          : mul_mem h ),
  add_left_neg := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (-a + a) - (0) = 0 : by norm_num
               ... ∈ S : zero_mem S end),
  add_comm := quotient.ind₂ (begin intros a b, apply quotient.sound, exact calc
    (a + b) - (b + a) = 0 : by rw [add_comm, sub_self]
                  ... ∈ S : zero_mem S end),
  mul := quotient.lift₂ (λ m n, ⟦m * n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ * m₂) - (n₁ * n₂) = (m₁ * m₂ - m₁ * n₂) + (m₁ * n₂ - n₁ * n₂) : by norm_num
                      ... = m₁ * (m₂ - n₂) + (m₁ - n₁) * n₂ : by rw [mul_sub, sub_mul]
                      ... = (m₂ - n₂) * m₁ + (m₁ - n₁) * n₂ : by ac_refl
                      ... ∈ S : add_mem (mul_mem h₂) (mul_mem h₁) ),
  mul_assoc := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a * b) * c) - (a * (b * c)) = 0 : by rw [mul_assoc, sub_self]
                              ... ∈ S : zero_mem S end),
  one := ⟦1⟧,
  one_mul := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (1 * a) - (a) = 0 : by norm_num
              ... ∈ S : zero_mem S end),
  mul_one := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (a * 1) - (a) = 0 : by norm_num
              ... ∈ S : zero_mem S end),
  left_distrib := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    (a * (b + c)) - ((a * b) + (a * c)) = 0 : by rw [left_distrib, sub_self]
                                    ... ∈ S : zero_mem S end),
  right_distrib := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) * c) - ((a * c) + (b * c)) = 0 : by rw [right_distrib, sub_self]
                                    ... ∈ S : zero_mem S end),
  mul_comm := quotient.ind₂ (begin intros a b, apply quotient.sound, exact calc
    (a * b) - (b * a) = 0 : by rw [mul_comm, sub_self]
                  ... ∈ S : zero_mem S end),
}

@[reducible] def to_coset (x : α) : coset α S := quotient.mk x

instance to_quotient : is_hom (to_coset S) :=
{ map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

infix / := coset

@[simp] lemma add_coset (x y : α) : ⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl
@[simp] lemma sub_coset (x y : α) : ⟦x⟧ - ⟦y⟧ = ⟦x - y⟧ := rfl
@[simp] lemma mul_coset (x y : α) : ⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl
@[simp] lemma neg_coset (x : α) : -⟦x⟧ = ⟦-x⟧ := rfl
@[simp] lemma one_coset : (1:coset α S) = ⟦(1:α)⟧ := rfl
@[simp] lemma zero (x : α) : x ∈ S ↔ ⟦x⟧ = 0 :=
⟨ λ hx, quotient.sound (calc x - 0 = x : sub_zero x ... ∈ S : hx),
  λ hx, calc x = x - 0 : (sub_zero x).symm ... ∈ S : quotient.exact hx ⟩

variable {S}

theorem coset_rep (x : α/S) : ∃ y, ⟦y⟧ = x := quotient.exists_rep x

end is_ideal


@[reducible] def zero_ideal (α : Type u) [comm_ring α] : set α := {(0:α)}
instance zero_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ zero_ideal α :=
{ zero_mem := mem_singleton 0,
  add_mem  := λ x y hx hy, begin simp [mem_singleton_iff] at *, simp [hx, hy] end,
  mul_mem  := λ x y hx, begin simp [mem_singleton_iff] at *, simp [hx] end }

@[reducible] def univ_ideal (α : Type u) [comm_ring α] : set α := set.univ
instance univ_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ univ_ideal α :=
{ zero_mem := ⟨⟩,
  add_mem  := λ x y hx hy, ⟨⟩,
  mul_mem  := λ x y hx, ⟨⟩ }

instance is_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] : is_ideal α ((f)⁻¹' S) :=
{ zero_mem := by simp [is_hom.map_zero f],
  add_mem  := λ x y (hx : f x ∈ S) hy, by simp [is_hom.map_add f, is_ideal.add_mem hx hy],
  mul_mem  := λ x y (hx : f x ∈ S), by simp [is_hom.map_mul f, is_ideal.mul_mem hx] }

-- Proposition 1.1 start

section prop_1_1

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]

@[reducible] def ideal_to_quotient (T : set α) [is_ideal α T] : set (α/S) := is_ideal.to_coset S '' T
@[reducible] def quotient_to_ideal (T : set (α/S)) [is_ideal (α/S) T] : set α := is_ideal.to_coset S ⁻¹' T

instance ideal_to_quotient.is_ideal (T : set α) [is_ideal α T] : is_ideal (α/S) (ideal_to_quotient S T) :=
{ zero_mem := ⟨0, is_ideal.zero_mem T, rfl⟩,
  add_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩ ⟨n, ⟨hn1, hn2⟩⟩, ⟨m + n, is_ideal.add_mem hm1 hn1, by rw [←hm2, ←hn2]; refl⟩,
  mul_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩,
    begin
      cases is_ideal.coset_rep y with n hn,
      exact ⟨m * n, by exact is_ideal.mul_mem hm1, by rw [←hm2, ←hn]; refl⟩
    end }

def quotient_to_ideal.is_ideal (T : set (α/S)) [is_ideal (α/S) T] : is_ideal α (quotient_to_ideal S T) :=
@is_ideal.hom_preimage _ _ _ _ _ (is_ideal.to_quotient S) T _

theorem quotient_to_ideal.contains (T : set (α/S)) [is_ideal (α/S) T] : S ⊆ quotient_to_ideal S T :=
λ x hx, calc
  ⟦x⟧ = 0 : (is_ideal.zero S x).1 hx
  ... ∈ T : is_ideal.zero_mem T

theorem contains_to_quotient_to_contains (T : set α) [is_ideal α T] (h : S ⊆ T) :
quotient_to_ideal S (ideal_to_quotient S T) = T :=
begin
  apply set.ext,
  intros x,
  split,
  intro hx,
  cases hx with z hz,
  cases hz with hz1 hz2,
  rw ←sub_eq_zero at hz2,
  simp only [is_ideal.sub_coset] at hz2,
  rw ←is_ideal.zero at hz2,
  exact calc
      x = z - (z - x) : by norm_num
    ... ∈ T           : is_ideal.sub_mem hz1 (h hz2),
  exact λ hx, ⟨ x, hx, rfl ⟩
end

theorem quotient_to_contains_to_quotient (T : set (α/S)) [is_ideal (α/S) T] :
@ideal_to_quotient _ _ S _ (quotient_to_ideal S T) (quotient_to_ideal.is_ideal S T) = T :=
begin
  apply set.ext,
  intros x,
  split,
  intro hx,
  cases hx with z hz,
  cases hz with hz1 hz2,
  rwa ←hz2,
  intro hx,
  cases is_ideal.coset_rep x with z hz,
  change ∃ (y : α), ⟦y⟧ ∈ T ∧ ⟦y⟧ = x,
  exact ⟨ z, by rwa hz, hz ⟩
end

theorem ideal_to_quotient.subset (T₁ : set α) [is_ideal α T₁] (T₂ : set α) [is_ideal α T₂] : T₁ ⊆ T₂ → ideal_to_quotient S T₁ ⊆ ideal_to_quotient S T₂ :=
λ h z ⟨ w, ⟨ hw1, hw2 ⟩ ⟩, ⟨ w, h hw1, hw2 ⟩

theorem quotient_to_ideal.subset (T₁ : set (α/S)) [is_ideal (α/S) T₁] (T₂ : set (α/S)) [is_ideal (α/S) T₂] : T₁ ⊆ T₂ → quotient_to_ideal S T₁ ⊆ quotient_to_ideal S T₂ :=
λ h z hz, h hz

end prop_1_1

-- Proposition 1.1 end

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) [is_hom f]

@[reducible] def ker : set α := f⁻¹' (zero_ideal β)
instance ker.is_ideal : is_ideal α (ker f) := is_ideal.hom_preimage f $ zero_ideal β

@[reducible] def im : set β := { y | ∃ x, f x = y }
instance im.subring : subring β (im f) :=
{ add_mem := λ x y ⟨ m, hm ⟩ ⟨ n, hn ⟩, ⟨ m + n, by simp [map_add f, hm, hn] ⟩,
  neg_mem := λ x ⟨ m, hm ⟩, ⟨-m, by simp [map_neg f, hm]⟩,
  mul_mem := λ x y ⟨ m, hm ⟩ ⟨ n, hn ⟩, ⟨ m * n, by simp [map_mul f, hm, hn] ⟩,
  one_mem := ⟨ (1:α), map_one f ⟩ }

instance im.comm_ring : comm_ring (im f) := subring.comm_ring β (im f)

end is_hom

structure isomorphism (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : α → β) (hf : is_hom f)
(g : β → α) (hg : is_hom g)
(hfg : ∀ x, f (g x) = x)
(hgf : ∀ x, g (f x) = x)

infix `≅`:70 := isomorphism

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

noncomputable def first_isom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] (f : α → β) [is_hom f] :
(α / (is_hom.ker f)) ≅ (is_hom.im f) :=
{ f := λ x, quotient.lift_on x (λ x, ⟨ f x, x, rfl ⟩ : α → is_hom.im f) (λ x y hxy, subtype.eq $ calc
    f x = f (y + (x - y)) : by norm_num
    ... = f y + f (x - y) : is_hom.map_add f
    ... = f y             : begin simp [has_equiv.equiv, setoid.r] at hxy, simp [hxy] end ),
  hf :=
    { map_add := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_add f]; refl),
      map_mul := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_mul f]; refl),
      map_one := by simp [is_hom.map_one f]; refl },
  g := λ ⟨y, hy⟩, ⟦classical.some hy⟧,
  hg :=
    { map_add :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          change classical.some _ - (classical.some _ + classical.some _) ∈ is_hom.ker f,
          have hm := classical.some_spec hx,
          have hn := classical.some_spec hy,
          have hmn := classical.some_spec (subring.add_mem hx hy),
          simp [is_hom.map_add f, is_hom.map_neg f, hm, hn, hmn]
        end,
      map_mul :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          change classical.some _ - (classical.some _ * classical.some _) ∈ is_hom.ker f,
          have hm := classical.some_spec hx,
          have hn := classical.some_spec hy,
          have hmn := classical.some_spec (subring.mul_mem hx hy),
          simp [is_hom.map_add f, is_hom.map_neg f, is_hom.map_mul f, hm, hn, hmn]
        end,
      map_one :=
        begin
          apply quotient.sound,
          change classical.some _ - (1 : α) ∈ is_hom.ker f,
          have h := classical.some_spec (subring.one_mem $ is_hom.im f),
          simp [is_hom.map_add f, is_hom.map_neg f, h, is_hom.map_one f, add_left_neg]
        end },
  hfg := λ ⟨x, hx⟩, subtype.eq (by simp [first_isom._match_1]; simpa using classical.some_spec hx),
  hgf :=
    begin
      intro x,
      cases is_ideal.coset_rep x with y hy,
      rw ←hy,
      simp [first_isom._match_1],
      change classical.some _ - y ∈ is_hom.ker f,
      have hz := @classical.some_spec _ (λ z, f z = f y) ⟨ y, rfl ⟩,
      simp [is_hom.map_add f, hz, is_hom.map_neg f]
    end
}

local infix `^` := monoid.pow

def nilpotent {α : Type u} [comm_ring α] (x : α) := ∃ n, x^(nat.succ n) = 0


-- page 3

section principal_ideal

variables {α : Type u} [comm_ring α] (x y : α)

def principal_ideal : set α := { y | ∃ z, x * z = y }

instance principal_ideal.is_ideal : is_ideal α $ principal_ideal x :=
{ zero_mem := ⟨0, mul_zero x⟩,
  add_mem  := λ y₁ y₂ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩, ⟨z₁ + z₂, calc
    x * (z₁ + z₂) = x * z₁ + x * z₂ : left_distrib x z₁ z₂
              ... = y₁ + x * z₂ : congr_arg (λ m, m + x * z₂) hz₁
              ... = y₁ + y₂ : congr_arg _ hz₂ ⟩,
  mul_mem  := λ y₁ y₂ ⟨z₁, hz₁⟩, ⟨z₁ * y₂, calc
    x * (z₁ * y₂) = (x * z₁) * y₂ : eq.symm $ mul_assoc x z₁ y₂
              ... = y₁ * y₂ : congr_arg (λ m, m * y₂) hz₁ ⟩ }

variable (α)

theorem principal_ideal_one_eq_univ : principal_ideal (1:α) = set.univ :=
set.ext $ λ x, ⟨ λ hx, ⟨⟩, λ hx, ⟨ x, one_mul x ⟩ ⟩

variable {α}

theorem unit_iff_principal_ideal_eq_one : (∃ y, x * y = 1) ↔ principal_ideal x = principal_ideal 1 :=
⟨ λ ⟨ y, hy⟩, set.ext $ λ z, ⟨ λ hz, ⟨ z, one_mul z ⟩, λ hz, ⟨ y * z, by rw [←mul_assoc, hy, one_mul] ⟩ ⟩, λ hx,
  begin
    have : (1:α) ∈ principal_ideal (1:α) := ⟨ 1, mul_one 1 ⟩,
    rw ←hx at this,
    exact this
  end ⟩

theorem mem_principal_ideal : x ∈ principal_ideal x :=
⟨ 1, mul_one x ⟩

theorem principal_ideal.subset_of_mem : x ∈ principal_ideal y → principal_ideal x ⊆ principal_ideal y :=
λ ⟨ n, hn ⟩ z ⟨ w, hw ⟩ , ⟨ n * w, by rw [←hw, ←hn]; ac_refl ⟩

variable (α)

theorem principal_ideal_zero_eq_zero_ideal : principal_ideal (0:α) = zero_ideal α :=
set.ext $ λ x, ⟨ λ ⟨y, hy⟩, by rw [←hy]; simp [zero_mul], λ hx, ⟨0, by rw [eq_of_mem_singleton hx, zero_mul] ⟩ ⟩

end principal_ideal

theorem is_ideal.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(∃ x:α, x ∈ S ∧ (∃ y, x * y = 1)) → S = set.univ :=
λ ⟨ x, ⟨ hx, ⟨ y, hy ⟩ ⟩ ⟩, set.ext $ λ z, ⟨ λ hz, ⟨ ⟩ , λ hz, calc
   z = 1 * z : eq.symm $ one_mul z
 ... = (x * y) * z : congr_arg (λ m, m * z) $ eq.symm hy
 ... = x * (y * z) : mul_assoc x y z
 ... ∈ S : is_ideal.mul_mem hx ⟩

theorem is_ideal.eq_univ_of_contains_one {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨ λ hz, ⟨ ⟩ , λ hz, calc
   z = 1 * z : eq.symm $ one_mul z
 ... ∈ S : is_ideal.mul_mem h ⟩


-- Proposition 1.2 start

section prop_1_2

variables (α : Type u) [comm_ring α] (zero_ne_one : (0:α) ≠ 1)

class is_field : Prop :=
(h : ∀ {x:α}, x ≠ 0 → ∃ y, x * y = 1)
(zero_ne_one : (0:α) ≠ 1)

class ideal_eq_zero_or_univ : Prop :=
(h : ∀ (S : set α) [is_ideal α S], S = zero_ideal α ∨ S = univ_ideal α)

class hom_inj : Prop :=
(h : ∀ (β : Type u) [comm_ring β] (zero_ne_one₂ : (0:β) ≠ 1) (f : α → β) [is_hom f] (x y : α), f x = f y → x = y)

include zero_ne_one

theorem is_field.to_ideal_eq_zero_or_univ : is_field α → ideal_eq_zero_or_univ α :=
begin
  intro hf,
  cases hf,
  constructor,
  intros S _,
  cases classical.em (∃ x, x ≠ (0:α) ∧ x ∈ S),
  right,
  cases h with x hx,
  apply is_ideal.eq_univ_of_contains_unit S,
  exact ⟨ x, hx.2, hf_h hx.1 ⟩,
  left,
  apply set.ext,
  intro x,
  split,
  intro hx,
  unfold zero_ideal,
  apply mem_singleton_of_eq,
  apply @of_not_not _ (classical.prop_decidable _),
  intro hnx,
  exact h ⟨ x, hnx, hx ⟩,
  intro hx,
  unfold zero_ideal at hx,
  rw mem_singleton_iff at hx,
  rw hx,
  exact is_ideal.zero_mem S
end

theorem ideal_eq_zero_or_univ.to_hom_inj : ideal_eq_zero_or_univ α → hom_inj α :=
begin
  intro h,
  cases h,
  constructor,
  intros,
  specialize h (is_hom.ker f),
  cases h,
  have : x - y ∈ is_hom.ker f,
  simp [is_hom.ker,is_hom.map_add f,a,zero_ideal,is_hom.map_neg f],
  rw h at this,
  simpa [zero_ideal,add_neg_eq_zero] using this,
  exfalso,
  apply zero_ne_one₂,
  rw ←is_hom.map_one f,
  suffices : (1:α) ∈ is_hom.ker f,
  simp [is_hom.ker, zero_ideal] at this, rw this,
  rw h,
  trivial
end

theorem hom_inj.to_is_field : hom_inj α → is_field α :=
begin
  intro h,
  cases h,
  constructor,
  intros x hx,
  specialize h (α / principal_ideal x),
  cases classical.em ((0 : α / principal_ideal x) = 1) with h1 h1,
  have := @quotient.exact _ (is_ideal.setoid $ principal_ideal x) _ _ h1,
  change (0:α) - 1 ∈ principal_ideal x at this,
  have : (1:α) ∈ principal_ideal x := calc
    (1:α) = (0 - 1) * (-1) : by norm_num
      ... ∈ principal_ideal x : is_ideal.mul_mem this,
  exact this,
  specialize @h h1 _ (is_ideal.to_quotient $ principal_ideal x) x 0,
  exfalso,
  apply hx,
  apply h,
  apply (is_ideal.zero _ _).1,
  exact mem_principal_ideal x,
  exact zero_ne_one
end

end prop_1_2

-- Proposition 1.2 end


section prime_ideals_and_maximal_ideals

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]

class is_prime_ideal : Prop :=
(not_univ_ideal : S ≠ univ_ideal α)
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

class is_maximal_ideal : Prop :=
(not_univ_ideal : S ≠ univ_ideal α)
(no_between : ∀ (T : set α) [is_ideal α T], S ⊆ T → T = S ∨ T = univ_ideal α)

variable α

class is_integral_domain : Prop :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)
(zero_ne_one : 0 ≠ (1:α))

variable {α}

theorem prime_iff_quotient_integral_domain : is_prime_ideal S ↔ is_integral_domain (α/S) :=
begin
  split,
  intro h,
  cases h,
  constructor,
  intros x y hxy,
  cases is_ideal.coset_rep x with m hm,
  cases is_ideal.coset_rep y with n hn,
  rw ←hm at *,
  rw ←hn at *,
  simp only [is_ideal.mul_coset] at hxy,
  rw ←is_ideal.zero at hxy,
  rw [←is_ideal.zero, ←is_ideal.zero],
  exact h_mem_or_mem_of_mul_mem hxy,
  intro h,
  have h2 := (is_ideal.zero S 1).2 h.symm,
  apply h_not_univ_ideal,
  exact is_ideal.eq_univ_of_contains_one S h2,
  intro h,
  cases h,
  constructor,
  intro h, apply h_zero_ne_one,
  apply eq.symm,
  apply (is_ideal.zero S 1).1,
  rw h,
  constructor,
  intros x y hxy,
  rw is_ideal.zero S,
  rw is_ideal.zero S,
  rw is_ideal.zero S at hxy,
  exact h_eq_zero_or_eq_zero_of_mul_eq_zero ⟦x⟧ ⟦y⟧ hxy
end

theorem maximal_iff_quotient_field : is_maximal_ideal S ↔ is_field (α/S) :=
begin
  split,
  intro h,
  cases h,
  have zero_ne_one : (0:α/S) ≠ 1,
    intro hz,
    apply h_not_univ_ideal,
    apply is_ideal.eq_univ_of_contains_one S,
    exact (is_ideal.zero S 1).2 hz.symm,
  apply hom_inj.to_is_field _ zero_ne_one,
  apply ideal_eq_zero_or_univ.to_hom_inj _ zero_ne_one,
  constructor,
  intros T _,
  specialize h_no_between (quotient_to_ideal S T) (quotient_to_ideal.contains S T),
  cases h_no_between with h h;
    rw [set.set_eq_def, quotient_to_ideal, set.preimage, set_of] at h,
  left,
    apply set.ext,
    intro x,
    rw mem_singleton_iff,
    cases is_ideal.coset_rep x with y hy,
    rw ←hy at *,
    specialize h y,
    rw is_ideal.zero S at h,
    exact h,
  right,
    apply set.ext,
    intro x,
    cases is_ideal.coset_rep x with y hy,
    rw ←hy at *,
    specialize h y,
    simpa using h,
  intro h,
  have h2 := is_field.to_ideal_eq_zero_or_univ (α/S) h.2 h,
  cases h2,
  constructor,
  intro h3,
  apply h.2.symm,
  apply (is_ideal.zero _ _).1,
  rw h3,
  constructor,
  intros T _ hs,
  specialize h2 (ideal_to_quotient S T),
  cases h2;
    unfold ideal_to_quotient at h2,
  left,
    apply set.ext,
    rw set.set_eq_def at h2,
    simp at h2,
    intro x,
    specialize h2 (is_ideal.to_coset S x),
    simp [is_ideal.to_coset] at h2,
    rw ←is_ideal.zero at h2,
    split,
    intro hx,
    rw ←h2,
    exact ⟨ x, hx, @setoid.refl _ _ (is_ideal.setoid S) x ⟩,
    exact λ hx, hs hx,
  right,
    apply set.ext,
    intro x,
    rw set.set_eq_def at h2,
    simp at *,
    specialize h2 (is_ideal.to_coset S x),
    cases h2 with y hy,
    cases hy with hy1 hy2,
    rw ←sub_eq_zero at hy2,
    simp at hy2,
    calc x = y - (y + -x) : by norm_num
       ... ∈ T : is_ideal.sub_mem hy1 (hs $ (is_ideal.zero _ _).2 hy2)
end

variable α

def quotient_zero_isomorphism : α/(zero_ideal α) ≅ α :=
{ f := @quotient.lift α α (is_ideal.setoid $ zero_ideal α) id
    begin
      intros x y hxy,
      change x - y ∈ {(0:α)} at hxy,
      rw mem_singleton_iff at hxy,
      exact sub_eq_zero.1 hxy
    end,
  g := is_ideal.to_coset (zero_ideal α),
  hf :=
    { map_add := λ x y,
        begin
          cases is_ideal.coset_rep x with m hm,
          cases is_ideal.coset_rep y with n hn,
          rw [←hm,←hn],
          simp,
        end,
      map_mul := λ x y,
        begin
          cases is_ideal.coset_rep x with m hm,
          cases is_ideal.coset_rep y with n hn,
          rw [←hm,←hn],
          simp,
        end,
      map_one := rfl },
  hg := is_ideal.to_quotient (zero_ideal α),
  hfg := λ x, rfl,
  hgf :=
    begin
      intro x,
      cases is_ideal.coset_rep x with m hm,
      rw ←hm,
      refl
    end }

def zero_prime_iff_integral_domain : is_prime_ideal (zero_ideal α) ↔ is_integral_domain α :=
begin
  split; intro h; cases h; constructor,
  simp at h_mem_or_mem_of_mul_mem,
  assumption,
  intro h,
  apply h_not_univ_ideal,
  have h1 := zero_ring_of_zero_eq_one h,
  apply set.ext,
  simpa using h1.eq_zero,
  intro h, apply h_zero_ne_one,
  simp [set.set_eq_def] at h,
  exact (h 1).symm,
  simpa using h_eq_zero_or_eq_zero_of_mul_eq_zero
end

instance is_prime_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] [is_prime_ideal S] : @is_prime_ideal α _ ((f)⁻¹' S) (is_ideal.hom_preimage f S) :=
begin
  constructor,
  intro h,
  apply is_prime_ideal.not_univ_ideal S,
  apply is_ideal.eq_univ_of_contains_one S,
  have h1 : (1:α) ∈ univ_ideal α := ⟨⟩,
  rw ←h at h1,
  simp [is_hom.map_one f] at h1,
  exact h1,
  intros x y,
  simpa [is_hom.map_mul f] using @is_prime_ideal.mem_or_mem_of_mul_mem _ _ S _ _ _ _
end

theorem is_field.to_is_integral_domain : is_field α → is_integral_domain α :=
begin
  intro h,
  cases h,
  constructor,
  intros x y hxy,
  rw @@or_iff_not_and_not (classical.prop_decidable _) (classical.prop_decidable _),
  intro h,
  cases h with hx hy,
  apply hx,
  specialize h_h hy,
  cases h_h with z hz,
  exact calc
      x = x * 1 : eq.symm (mul_one x)
    ... = x * (y * z) : congr_arg _ hz.symm
    ... = (x * y) * z : eq.symm (mul_assoc x y z)
    ... = 0 * z : congr_arg (λ m, m * z) hxy
    ... = 0 : zero_mul z,
  exact h_zero_ne_one
end

variable {α}

theorem is_maximal_ideal.to_is_prime_ideal : is_maximal_ideal S → is_prime_ideal S :=
by rw [maximal_iff_quotient_field, prime_iff_quotient_integral_domain]; exact is_field.to_is_integral_domain (α/S)

end prime_ideals_and_maximal_ideals

-- Proposition 1.3 start

section prop_1_3

variables (α : Type u) [comm_ring α]

def ideals : set (set α) := { S | is_ideal α S }

instance ideals.sUnion (A : set (set α)) (h : A ⊆ ideals α) (S : set α) (hs : S ∈ A)
(total : ∀ {T₁ T₂ : set α}, T₁ ∈ A → T₂ ∈ A → T₁ ⊆ T₂ ∨ T₂ ⊆ T₁) : ⋃₀ A ∈ ideals α :=
{ zero_mem := ⟨ S, hs, @@is_ideal.zero_mem _ S (h hs) ⟩ ,
  add_mem  := λ x y ⟨ T₁, ht₁, hx ⟩ ⟨ T₂, ht₂, hy ⟩ ,
    or.cases_on (total ht₁ ht₂)
    (λ ht12, ⟨ T₂, ht₂, @is_ideal.add_mem _ _ T₂ (h ht₂) x y (ht12 hx) hy ⟩ )
    (λ ht21, ⟨ T₁, ht₁, @is_ideal.add_mem _ _ T₁ (h ht₁) x y hx (ht21 hy) ⟩ ) ,
  mul_mem  := λ x y ⟨ T₁, ht₁, hx ⟩,
    ⟨ T₁, ht₁, @is_ideal.mul_mem _ _ T₁ (h ht₁) x y hx ⟩ }

def ideals_not_univ : set (set α) := { S | is_ideal α S ∧ (1:α) ∉ S }

theorem ideals_not_univ.sUnion (A : set (set α)) (h : A ⊆ ideals_not_univ α) (S : set α) (hs : S ∈ A)
(total : ∀ {T₁ T₂ : set α}, T₁ ∈ A → T₂ ∈ A → T₁ ⊆ T₂ ∨ T₂ ⊆ T₁) : ⋃₀ A ∈ ideals_not_univ α :=
⟨ ideals.sUnion α A (λ i hi, and.elim_left $ h hi) S hs (λ T₁ T₂ ht₁ ht₂, total ht₁ ht₂) ,
  λ ⟨ T, ht, ht2 ⟩ , (h ht).2 ht2 ⟩

theorem zero_ne_one.to_maximal_ideal : (0:α) ≠ 1 → ∃ (S : set α) (hs : is_ideal α S), @is_maximal_ideal _ _ S hs :=
begin
  intro hz,
  have z := @zorn.zorn,
  specialize @z (ideals_not_univ α),
  specialize @z (λ T₁ T₂, T₁.1 ⊆ T₂.1),
  specialize z (λ c hc,
    begin
      simp [zorn.chain, set.pairwise_on] at hc,
      let U : set (set α) := { S | ∃ T : ideals_not_univ α, T ∈ c ∧ T.1 = S },
      have hu := ideals_not_univ.sUnion α U,
      specialize hu (λ S ⟨ ⟨ T, ht ⟩ , _, hts ⟩ , by rwa ←hts ),
      cases classical.em (∃ S, S ∈ c) with h h,
      cases h with S h,
      cases S with S hs,
      specialize hu S ⟨ ⟨ S, hs ⟩ , h, rfl ⟩ ,
      specialize hu (λ T₁ T₂ ⟨ ⟨ t₁, ht1 ⟩ , htc1, hts1 ⟩ ⟨ ⟨ t₂, ht2 ⟩ , htc2, hts2 ⟩,
        begin
          specialize hc t₁ ht1 htc1 t₂ ht2 htc2,
          rw [←hts1, ←hts2] at *,
          cases classical.em (subtype.mk t₁ ht1 = subtype.mk t₂ ht2) with ht12 ht12,
          have := subtype.mk.inj ht12,
          rw set.set_eq_def at this,
          left, exact (λ x hx, (this x).1 hx),
          specialize hc ht12,
          exact hc
        end),
      let ub : ↥(ideals_not_univ α) := ⟨ ⋃₀ U, hu ⟩,
      existsi ub,
      intros T htc x hx,
      cases T with T ht,
      exact ⟨ T, ⟨ ⟨ T, ht ⟩, htc, rfl ⟩ , hx ⟩,
      let ub : ↥(ideals_not_univ α) := ⟨ zero_ideal α , zero_ideal.is_ideal α, by simpa using hz.symm ⟩,
      existsi ub,
      intros T htc,
      exfalso,
      exact h ⟨ T , htc ⟩
    end),
  specialize z (λ A B C hab hbc x hx, hbc $ hab hx),
  cases z with m z,
  cases m with m hm1,
  cases hm1 with h1 h2,
  existsi m,
  existsi h1,
  constructor,
  intro h, apply h2, rw h, trivial,
  intros T _ ht,
  cases classical.em ((1:α) ∈ T),
  right, exact is_ideal.eq_univ_of_contains_one T h,
  specialize z ⟨ T, _inst_3, h ⟩ ,
  specialize z ht,
  left, exact set.eq_of_subset_of_subset z ht
end

end prop_1_3

-- Proposition 1.3 end


-- Corollary 1.4 start

theorem ideals_not_univ.to_maximal_ideal {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
S ∈ ideals_not_univ α → ∃ (m : set α) (hm : is_ideal α m), @is_maximal_ideal _ _ m hm ∧ S ⊆ m :=
begin
  intro h,
  cases h with h1 h2,
  have z := zero_ne_one.to_maximal_ideal (α/S),
  specialize z (λ h, h2 $ (is_ideal.zero S 1).2 h.symm),
  cases z with m hm,
  cases hm with h1 h2,
  existsi quotient_to_ideal S m,
  existsi quotient_to_ideal.is_ideal S m,
  have hsm : S ⊆ quotient_to_ideal S m,
    intro x,
    simp [is_ideal.zero S,is_ideal.to_coset],
    intro hx,
    rw hx,
    apply is_ideal.zero_mem,
  split,
  cases h2,
  constructor,
  intro h,
  apply h2_not_univ_ideal,
  rw [set.set_eq_def] at h,
  apply set.ext,
  intro x,
  cases is_ideal.coset_rep x with y hy,
  rw ←hy,
  specialize h y,
  simp at *,
  exact h,
  intros T _ ht,
  have hst : S ⊆ T := set.subset.trans hsm ht,
  specialize h2_no_between (ideal_to_quotient S T),
  have ht2 := ideal_to_quotient.subset S _ _ ht,
  rw quotient_to_contains_to_quotient at ht2,
  specialize h2_no_between ht2,
  cases h2_no_between with h h,
  left,
  apply set.eq_of_subset_of_subset,
  rw set.subset.antisymm_iff at h,
  have h3 := quotient_to_ideal.subset S _ _ h.1,
  rw contains_to_quotient_to_contains at h3,
  exact h3,
  exact hst,
  exact ht,
  right,
  apply set.ext,
  rw set.set_eq_def at h,
  intro x,
  specialize h (is_ideal.to_coset S x),
  simp at *,
  cases h with y hy,
  cases hy with hy1 hy2,
  calc x = y - (y - x) : by norm_num
     ... ∈ T : is_ideal.sub_mem hy1 (hst hy2),
  exact hsm
end

-- Corollary 1.4 end


-- Corollary 1.5 start

theorem not_unit.to_maximal_ideal {α : Type u} [comm_ring α] (x : α) (h : ¬∃ y, x * y = 1) :
∃ (m : set α) (hm : is_ideal α m), @is_maximal_ideal _ _ m hm ∧ x ∈ m :=
begin
  have z := ideals_not_univ.to_maximal_ideal (principal_ideal x),
  specialize z
    (begin
      split,
      exact principal_ideal.is_ideal x,
      intro hx,
      have := is_ideal.eq_univ_of_contains_one _ hx,
      apply h,
      apply (unit_iff_principal_ideal_eq_one x).2,
      rw this,
      rw principal_ideal_one_eq_univ
    end),
  cases z with m z,
  cases z with hm z,
  existsi m,
  existsi hm,
  split, exact z.1,
  apply set.mem_of_mem_of_subset _ z.2,
  exact mem_principal_ideal x
end

-- Corollary 1.5 end


class is_local (α : Type u) [comm_ring α] : Prop :=
(h : ∀ S T [is_ideal α S] [is_ideal α T] [is_maximal_ideal S] [is_maximal_ideal T], S = T)

def generate {α : Type u} [comm_ring α] (S : set α) : set α :=
{ x | ∀ (T : set α) [is_ideal α T], S ⊆ T → x ∈ T }

instance generate.is_ideal (α : Type u) [comm_ring α] (S : set α) : is_ideal α (generate S) :=
{ zero_mem := λ T ht hst, @@is_ideal.zero_mem _ T ht,
  add_mem  := λ x y hx hy T ht hst, @@is_ideal.add_mem _ ht (@hx T ht hst) (@hy T ht hst),
  mul_mem  := λ x y hx T ht hst, @@is_ideal.mul_mem _ ht (@hx T ht hst) }

theorem singleton_generate_principal (α : Type u) [comm_ring α] (x : α) :
generate {x} = principal_ideal x :=
begin
  apply set.ext,
  intro y,
  split,
  intro hy,
  specialize hy (principal_ideal x),
  specialize hy (λ z hz, begin simp at hz, rw hz, exact mem_principal_ideal x end),
  exact hy,
  intros h T ht hst,
  simp at hst,
  cases h with z hz,
  rw ←hz,
  exact is_ideal.mul_mem hst
end

theorem subset_generate {α : Type u} [comm_ring α] (S : set α) : S ⊆ generate S :=
λ x hx T ht hst, hst hx

theorem generate_subset_ideal {α : Type u} [comm_ring α] {S : set α} {T : set α} [is_ideal α T] : S ⊆ T → generate S ⊆ T :=
λ h x hx, hx T h

-- Proposition 1.6 start

theorem nonunits_ideal_to_local {α : Type u} [comm_ring α] :
is_ideal α { x | ¬∃ y, x * y = 1 } → is_local α :=
begin
  intro h,
  constructor,
  intros S T _ _ _ _,
  let U := { x : α | ¬∃ y, x * y = 1 },
  have h1 : S ⊆ U,
    intros x hx h,
    apply is_maximal_ideal.not_univ_ideal S,
    apply is_ideal.eq_univ_of_contains_unit S,
    exact ⟨ x, hx, h ⟩,
  have h2 := is_maximal_ideal.no_between U h1,
  cases h2,
  have h3 : T ⊆ U,
    intros x hx h,
    apply is_maximal_ideal.not_univ_ideal T,
    apply is_ideal.eq_univ_of_contains_unit T,
    exact ⟨ x, hx, h ⟩,
  have h4 := is_maximal_ideal.no_between U h3,
  cases h4,
  rwa [←h2, ←h4],
  exfalso,
  have : (1:α) ∈ U, rw h4, trivial,
  simp at this,
  apply this 1,
  trivial,
  exfalso,
  have : (1:α) ∈ U, rw h2, trivial,
  simp at this,
  apply this 1,
  trivial,
end

theorem maximal_ideal_one_add_unit_to_local {α : Type u} [comm_ring α]
(m : set α) [is_ideal α m] [is_maximal_ideal m] :
(∀ x:α, x ∈ m → ∃ y, (1 + x) * y = 1) → is_local α :=
begin
  intro h,
  have z := nonunits_ideal_to_local,
  have : m = { x | ¬∃ y, x * y = 1 },
  apply set.ext,
  intro x,
  split,
  intros hx h,
  apply is_maximal_ideal.not_univ_ideal m,
  apply is_ideal.eq_univ_of_contains_unit m,
  exact ⟨ x, hx, h ⟩ ,
  intro hx,
  let β := α/m,
  let y := ⟦x⟧,
  have : is_field β,
  rwa ←maximal_iff_quotient_field,
  cases classical.em (y = 0) with h1 h1,
  rwa ←is_ideal.zero at h1,
  cases is_field.h h1 with n hn,
  cases (quotient.exists_rep n) with w hw,
  rw ←hw at hn,
  have := quotient.exact hn,
  specialize h _ this,
  clear h1, clear hn, clear y,
  cases h with y hy,
  exfalso,
  apply hx,
  existsi w * y,
  rwa [add_comm,sub_add_cancel,mul_assoc] at hy,
  rw this at _inst_2,
  exact z _inst_2
end

-- Proposition 1.6 end


class is_pid (α : Type u) [comm_ring α] extends is_integral_domain α : Prop :=
(h : ∀ S [is_ideal α S], ∃ x, S = principal_ideal x)

instance maximal_of_pid_of_prime_of_nonzero (α : Type u) [comm_ring α] [is_pid α]
(S : set α) [is_ideal α S] [is_prime_ideal S] : S ≠ zero_ideal α → is_maximal_ideal S :=
begin
  intro h,
  constructor,
  apply is_prime_ideal.not_univ_ideal,
  intros T _ hst,
  have p := is_pid.h,
  cases p S with s hs,
  cases p T with t ht,
  have h1 : s ∈ T,
    apply set.mem_of_mem_of_subset _ hst,
    simp [hs, mem_principal_ideal],
  rw ht at h1,
  cases h1 with z hz,
  clear p,
  have p := is_prime_ideal.mem_or_mem_of_mul_mem,
  have h1 : s ∈ S,
    simp [hs, mem_principal_ideal],
  rw ←hz at h1,
  specialize p h1,
  cases p,
  left,
    apply set.eq_of_subset_of_subset,
    rw [hs, ht],
    apply principal_ideal.subset_of_mem,
    rwa hs at p,
    exact hst,
  right,
    rw [univ_ideal, ←principal_ideal_one_eq_univ],
    rw [ht, ←unit_iff_principal_ideal_eq_one],
    rw hs at p,
    cases p with n hn,
    have p := is_integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero z (t * n - 1),
    have : z * (t * n - 1) = 0 := calc
      z * (t * n - 1) = z * (t * n) - z * 1 : mul_sub z (t * n) 1
                  ... = (t * z) * n - z : by norm_num; ac_refl
                  ... = s * n - z : congr_arg (λ b, b * n - z) hz
                  ... = z - z : congr_arg (λ b, b - z) hn
                  ... = 0 : sub_self z,
    specialize p this,
    cases p,
    rw [p, mul_zero] at hz,
    exfalso,
    apply h,
    rw [hs, ←hz],
    apply principal_ideal_zero_eq_zero_ideal,
    rw sub_eq_zero at p,
    exact ⟨ n, p ⟩,
    repeat {assumption}
end
