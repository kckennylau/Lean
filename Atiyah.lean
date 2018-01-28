import algebra.ring algebra.field data.set.basic tactic.norm_num

universes u v w

-- page 1

class zero_ring (α : Type u) extends comm_ring α :=
(eq_zero : ∀ x:α, x = 0)

def zero_ring_of_zero_eq_one (α : Type u) [comm_ring α] : (0:α)=1 → zero_ring α
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

instance : setoid α :=
{ r     := λ x y, x - y ∈ S,
  iseqv :=
    ⟨λ x, calc
      x - x = 0 : sub_self x
        ... ∈ S : zero_mem S,
    λ x y hxy, calc
      y - x = -(x - y)     : eq.symm (neg_sub x y)
        ... = -1 * (x - y) : eq.symm (neg_one_mul _)
        ... = (x - y) * -1 : mul_comm _ _
        ... ∈ S            : mul_mem hxy,
    λ x y z hxy hyz, calc
      x - z = (x - y) + (y - z) : eq.symm (sub_add_sub_cancel x y z)
        ... ∈ S                 : add_mem hxy hyz ⟩ }

variables (α)

def coset := quotient (is_ideal.setoid S)

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

instance coset.comm_ring : comm_ring (coset α S) :=
(by apply_instance : comm_ring (quotient $ is_ideal.setoid S))

def to_quotient : is_hom (quotient.mk : α → coset α S) :=
{ map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

@[simp] lemma add_coset (x y : α) : ⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl
@[simp] lemma sub_coset (x y : α) : ⟦x⟧ - ⟦y⟧ = ⟦x - y⟧ := rfl
@[simp] lemma mul_coset (x y : α) : ⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl
@[simp] lemma neg_coset (x : α) : -⟦x⟧ = ⟦-x⟧ := rfl
@[simp] lemma one_coset : (1:coset α S) = ⟦(1:α)⟧ := rfl
@[simp] lemma zero (x : α) : x ∈ S ↔ ⟦x⟧ = 0 :=
⟨ λ hx, quotient.sound (calc x - 0 = x : sub_zero x ... ∈ S : hx),
  λ hx, calc x = x - 0 : (sub_zero x).symm ... ∈ S : quotient.exact hx ⟩

end is_ideal

local infix / := is_ideal.coset

def zero_ideal (α : Type u) [comm_ring α] : set α := {(0:α)}
instance zero_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ zero_ideal α :=
{ zero_mem := set.mem_singleton 0,
  add_mem  := λ x y hx hy, begin unfold zero_ideal at *; rw set.mem_singleton_iff at *, rw [hx, hy], simp end,
  mul_mem  := λ x y hx, begin unfold zero_ideal at *; rw set.mem_singleton_iff at *, rw hx, simp end }

def univ_ideal (α : Type u) [comm_ring α] : set α := set.univ
instance univ_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ univ_ideal α :=
{ zero_mem := ⟨⟩,
  add_mem  := λ x y hx hy, ⟨⟩,
  mul_mem  := λ x y hx, ⟨⟩ }

def is_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] : is_ideal α ((f)⁻¹' S) :=
{ zero_mem := by simp [is_hom.map_zero f, is_ideal.zero_mem],
  add_mem  := λ x y (hx : f x ∈ S) hy, by simp [is_hom.map_add f, is_ideal.add_mem hx hy],
  mul_mem  := λ x y (hx : f x ∈ S), by simp [is_hom.map_mul f, is_ideal.mul_mem hx] }

-- Proposition 1.1 start

section prop_1_1

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]

def contains_ideal := {i : {T : set α // is_ideal α T} // S ⊆ i.1}
def ideal_quotient := {i : set $ α/S // is_ideal (α/S) i}

theorem contains_ideal.ext : ∀ x y : contains_ideal S, x.1.1 = y.1.1 → x = y :=
λ x y hxy, subtype.eq $ subtype.eq hxy

theorem ideal_quotient.ext : ∀ x y : ideal_quotient S, x.1 = y.1 → x = y :=
λ x y hxy, subtype.eq hxy

def contains_to_quotient : contains_ideal S → ideal_quotient S :=
λ ⟨⟨T, ht⟩, h⟩,
{ val := quotient.mk '' T,
  property :=
  { zero_mem := ⟨0, ht.zero_mem, rfl⟩,
    add_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩ ⟨n, ⟨hn1, hn2⟩⟩, ⟨m + n, by exact is_ideal.add_mem hm1 hn1, by rw [←hm2, ←hn2]; refl⟩,
    mul_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩,
      begin
        cases @quotient.exists_rep _ (is_ideal.setoid S) y with n hn,
        existsi m * n,
        split,
        exact is_ideal.mul_mem hm1,
        rw [←hm2, ←hn],
        refl
      end } }

def quotient_to_contains : ideal_quotient S → contains_ideal S :=
λ ⟨T, ht⟩,
{ val :=
  { val      := quotient.mk ⁻¹' T,
    property := @is_ideal.hom_preimage _ _ _ _ _ (is_ideal.to_quotient S) T ht },
  property := λ x hx, by simpa [(is_ideal.zero _ _).1 hx] using is_ideal.zero_mem T }

theorem contains_to_quotient_to_contains : (quotient_to_contains S) ∘ (contains_to_quotient S) = id :=
begin
  apply funext,
  intros x,
  cases x with x hx,
  cases x with T ht,
  simp [function.comp, contains_to_quotient, quotient_to_contains, is_ideal.to_quotient],
  apply contains_ideal.ext,
  apply set.ext,
  intros y,
  split,
  intro hy,
  cases hy with z hz,
  have : z - y ∈ T := hx (@quotient.exact _ (is_ideal.setoid S) _ _ hz.2),
  exact calc
      y = z + (z - y) * -1 : by norm_num
    ... ∈ T                : is_ideal.add_mem hz.1 (is_ideal.mul_mem this),
  intro hy,
  existsi y,
  split,
  exact hy,
  refl
end

theorem quotient_to_contains_to_quotient : (contains_to_quotient S) ∘ (quotient_to_contains S) = id :=
begin
  apply funext,
  intros x,
  cases x with x hx,
  simp only [function.comp, contains_to_quotient, quotient_to_contains],
  apply ideal_quotient.ext,
  apply set.ext,
  intros y,
  simp,
  split,
  intro hy,
  cases hy with z hz,
  cases hz with hz1 hz2,
  rwa ←hz2,
  intro hy,
  cases quotient.exists_rep y with z hz,
  existsi z,
  split,
  rwa hz,
  exact hz
end

theorem contains_to_quotient_of_subset : ∀ x y : contains_ideal S, x.val.1 ⊆ y.val.1 → (contains_to_quotient S x).1 ⊆ (contains_to_quotient S y).1 :=
λ ⟨⟨m, hm⟩, hx⟩ ⟨⟨n, hn⟩, hy⟩ h z ⟨w, ⟨hw1, hw2⟩⟩, ⟨w, h hw1, hw2⟩

theorem quotient_to_contains_of_subset : ∀ x y : ideal_quotient S, x.1 ⊆ y.1 → (quotient_to_contains S x).val.1 ⊆ (quotient_to_contains S y).val.1 :=
λ ⟨m, hm⟩ ⟨n, hn⟩ h z hz, h hz

end prop_1_1

-- Proposition 1.1 end

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) [is_hom f]

def ker : set α := f⁻¹' (zero_ideal β)
instance ker.is_ideal : is_ideal α (ker f) := is_ideal.hom_preimage f $ zero_ideal β

def im : set β := f '' set.univ
instance im.subring : subring β (im f) :=
{ add_mem := λ x y ⟨m, ⟨hm1, hm2⟩⟩ ⟨n, ⟨hn1, hn2⟩⟩, ⟨m + n, by simp [map_add f, hm2, hn2]⟩,
  neg_mem := λ x ⟨m, ⟨hm1, hm2⟩⟩, ⟨-m, by simp [map_neg f, hm2]⟩,
  mul_mem := λ x y ⟨m, ⟨hm1, hm2⟩⟩ ⟨n, ⟨hn1, hn2⟩⟩, ⟨m * n, by simp [map_mul f, hm2, hn2]⟩,
  one_mem := ⟨(1:α), ⟨⟩, map_one f⟩ }

instance im.comm_ring : comm_ring (im f) :=
@subring.comm_ring β _ (f '' set.univ) (im.subring f)

end is_hom

structure isomorphism (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : α → β) (hf : is_hom f)
(g : β → α) (hg : is_hom g)
(hfg : ∀ x, f (g x) = x)
(hgf : ∀ x, g (f x) = x)

infix `≅`:70 := isomorphism

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

noncomputable def first_isom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] (f : α → β) [is_hom f] :
(α / (is_hom.ker f)) ≅ (is_hom.im f) :=
{ f := @quotient.lift α (is_hom.im f) (is_ideal.setoid $ is_hom.ker f) (λ x, ⟨f x, x, ⟨⟩, rfl⟩) (λ x y hxy, subtype.eq $ calc
    f x = f (y + (x - y))   : by norm_num
      ... = f y + f (x - y) : is_hom.map_add f
      ... = f y : begin simp [has_equiv.equiv, setoid.r, is_hom.ker, zero_ideal] at hxy, simp [hxy] end ),
  hf :=
    { map_add := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_add f]; refl),
      map_mul := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_mul f]; refl),
      map_one := by simp [is_hom.map_one f]; refl },
  g := λ ⟨y, hy⟩, @quotient.mk α (is_ideal.setoid $ is_hom.ker f) (classical.some hy),
  hg :=
    { map_add :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          change classical.some _ - (classical.some _ + classical.some _) ∈ is_hom.ker f,
          unfold is_hom.ker,
          unfold set.preimage,
          have hm := (classical.some_spec hx).2,
          have hn := (classical.some_spec hy).2,
          have hmn := (classical.some_spec (subring.add_mem hx hy)).2,
          simp at hm,
          simp at hn,
          simp at hmn,
          simp [is_hom.map_add f,is_hom.map_neg f,hm,hn,hmn,zero_ideal]
        end,
      map_mul :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          change classical.some _ - (classical.some _ * classical.some _) ∈ is_hom.ker f,
          unfold is_hom.ker,
          unfold set.preimage,
          have hm := (classical.some_spec hx).2,
          have hn := (classical.some_spec hy).2,
          have hmn := (classical.some_spec $ subring.mul_mem hx hy).2,
          simp at hm,
          simp at hn,
          simp at hmn,
          simp [is_hom.map_add f,is_hom.map_neg f,is_hom.map_mul f,hm,hn,hmn,zero_ideal]
        end,
      map_one :=
        begin
          apply quotient.sound,
          change classical.some _ - (1 : α) ∈ is_hom.ker f,
          unfold is_hom.ker,
          unfold set.preimage,
          simp [is_hom.map_add f],
          have h := (classical.some_spec $ subring.one_mem $ is_hom.im f).2,
          simp at h,
          simp [is_hom.map_neg f,h,is_hom.map_one f,add_left_neg,zero_ideal]
        end },
  hfg := λ ⟨x, hx⟩, subtype.eq (by simp [first_isom._match_1]; simpa using classical.some_spec hx),
  hgf :=
    begin
      intro x,
      cases quotient.exists_rep x with y hy,
      rw ←hy,
      simp [first_isom._match_1],
      change classical.some _ - y ∈ is_hom.ker f,
      unfold is_hom.ker,
      unfold set.preimage,
      have hz := @classical.some_spec _ (λ z, f z = f y) ⟨y, rfl⟩,
      simp [is_hom.map_add f,hz,is_hom.map_neg f,zero_ideal]
    end
}

local infix `^` := monoid.pow

def nilpotent {α : Type u} [comm_ring α] (x : α) := ∃ n, x^(nat.succ n) = 0


-- page 3

section principal_ideal

variables {α : Type u} [comm_ring α] (x : α)

def principal_ideal := {y | ∃ z, x * z = y}

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

variable (α)

theorem principal_ideal_zero_eq_zero_ideal : principal_ideal (0:α) = zero_ideal α :=
set.ext $ λ x, ⟨ λ ⟨y, hy⟩, by rw [←hy]; simp [zero_mul, zero_ideal], λ hx, ⟨0, by rw [set.eq_of_mem_singleton hx, zero_mul] ⟩ ⟩

end principal_ideal

theorem is_ideal.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(∃ x:α, x ∈ S ∧ (∃ y, x * y = 1)) → S = set.univ :=
λ ⟨ x, ⟨ hx, ⟨ y, hy ⟩ ⟩ ⟩, set.ext $ λ z, ⟨ λ hz, ⟨ ⟩ , λ hz, calc
   z = 1 * z : eq.symm $ one_mul z
 ... = (x * y) * z : congr_arg (λ m, m * z) $ eq.symm hy
 ... = x * (y * z) : mul_assoc x y z
 ... ∈ S : is_ideal.mul_mem hx ⟩


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
  apply set.mem_singleton_of_eq,
  apply @of_not_not _ (classical.prop_decidable _),
  intro hnx,
  exact h ⟨ x, hnx, hx ⟩,
  intro hx,
  unfold zero_ideal at hx,
  rw set.mem_singleton_iff at hx,
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
  existsi (1:α),
  simp,
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
  cases quotient.exists_rep x with m hm,
  cases quotient.exists_rep y with n hn,
  rw ←hm at *,
  rw ←hn at *,
  simp only [is_ideal.mul_coset] at hxy,
  have hxy2 := quotient.exact hxy,
  change m * n - 0 ∈ S at hxy2,
  simp only [sub_zero (m * n)] at hxy2,
  cases h_mem_or_mem_of_mul_mem hxy2 with h h,
  left, apply quotient.sound, change m - 0 ∈ S, simpa,
  right, apply quotient.sound, change n - 0 ∈ S, simpa,
  intro h,
  have h2 := quotient.exact h.symm,
  change (1:α) - 0 ∈ S at h2,
  simp only [sub_zero] at h2,
  apply h_not_univ_ideal,
  unfold univ_ideal,
  apply is_ideal.eq_univ_of_contains_unit S,
  existsi (1:α),
  split, exact h2, existsi (1:α), simp,
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
  apply h_eq_zero_or_eq_zero_of_mul_eq_zero,
  simpa
end

theorem maximal_iff_quotient_field : is_maximal_ideal S ↔ is_field (α/S) :=
begin
  split,
  intro h,
  cases h,
  have zero_ne_one : (0:α/S) ≠ 1,
    intro hz,
    apply h_not_univ_ideal,
    unfold univ_ideal,
    apply is_ideal.eq_univ_of_contains_unit S,
    existsi (1:α),
    split,
    exact (is_ideal.zero S 1).2 hz.symm,
    existsi (1:α),
    simp,
  apply hom_inj.to_is_field _ zero_ne_one,
  apply ideal_eq_zero_or_univ.to_hom_inj _ zero_ne_one,
  constructor,
  intros T _,
  let U := quotient.mk ⁻¹' T,
  have hu1 := @is_ideal.hom_preimage _ _ _ _ _ (is_ideal.to_quotient S) T _inst_2_1,
  have hu2 : S ⊆ U := λ x hx, by simpa [(is_ideal.zero _ _).1 hx] using is_ideal.zero_mem T,
  specialize h_no_between U hu2,
  have hu : U = (@quotient.mk α (is_ideal.setoid S)) ⁻¹' T := rfl,
  rw hu at *,
  cases h_no_between with h h; unfold set.preimage at h,
  unfold zero_ideal,
  left,
    apply set.ext,
    intro x,
    rw set.mem_singleton_iff,
    cases @quotient.exists_rep _ (is_ideal.setoid S) x with y hy,
    rw ←hy at *,
    have := congr_fun h y, rw [←iff_iff_eq, set_of] at this,
    rw this,
    exact is_ideal.zero S y,
  right,
    apply set.ext,
    intro x,
    cases @quotient.exists_rep _ (is_ideal.setoid S) x with y hy,
    rw ←hy at *,
    have := congr_fun h y, rw [←iff_iff_eq, set_of] at this,
    rw this,
    exact ⟨ λ h, true.intro, λ h, true.intro ⟩,
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
  let U := @quotient.mk α (is_ideal.setoid S) '' T,
  have hu : U = @quotient.mk α (is_ideal.setoid S) '' T := rfl,
  have : is_ideal (α/S) U :=
  { zero_mem := ⟨0, is_ideal.zero_mem T, rfl⟩,
    add_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩ ⟨n, ⟨hn1, hn2⟩⟩, ⟨m + n, by exact is_ideal.add_mem hm1 hn1, by rw [←hm2, ←hn2]; refl⟩,
    mul_mem  := λ x y ⟨m, ⟨hm1, hm2⟩⟩,
      begin
        cases @quotient.exists_rep _ (is_ideal.setoid S) y with n hn,
        existsi m * n,
        split,
        exact is_ideal.mul_mem hm1,
        rw [←hm2, ←hn],
        refl
      end },
  specialize h2 U,
  rw hu at *,
  cases h2,
  left,
    apply set.ext,
    intro x,
    split,
    intro hx,
    have : (@quotient.mk α (is_ideal.setoid S) x) ∈ @quotient.mk α (is_ideal.setoid S) '' T := ⟨ x, hx, rfl ⟩,
    rw h2 at this,
    unfold zero_ideal at this,
    rw set.mem_singleton_iff at this,
    exact (is_ideal.zero _ _).2 this,
    exact λ hx, hs hx,
  right,
    apply set.ext,
    intro x,
    split,
    intro hx,
    constructor,
    intro hx,
    have := congr_fun h2 (@quotient.mk α (is_ideal.setoid S) x), rw [←iff_iff_eq, univ_ideal, set.univ, iff_true] at this,
    cases this with y hy,
    cases hy with hy1 hy2,
    rw ←sub_eq_zero at hy2,
    simp at hy2,
    calc x = y + (y + -x) * -1 : by norm_num
       ... ∈ T : is_ideal.add_mem hy1 (is_ideal.mul_mem $ hs $ (is_ideal.zero _ _).2 hy2)
end

end prime_ideals_and_maximal_ideals
