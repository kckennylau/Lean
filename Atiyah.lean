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

structure hom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : α → β)
(map_add : ∀ x y, f (x + y) = f x + f y)
(map_mul : ∀ x y, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables {x y : α} {f : hom α β}

theorem map_zero : f.f 0 = 0 := calc
f.f 0 = f.f 0 + f.f 0 - f.f 0 : eq.symm $ add_sub_cancel (f.f 0) (f.f 0)
... = f.f (0 + 0) - f.f 0 : congr_arg (λ x, x - f.f 0) $ eq.symm $ f.map_add 0 0
... = f.f 0 - f.f 0 : congr_arg (λ x, f.f x - f.f 0) $ zero_add 0
... = 0 : sub_self $ f.f 0

theorem map_neg : f.f (-x) = -f.f x := calc
f.f (-x) = f.f (-x) + f.f x - f.f x : eq.symm $ add_sub_cancel (f.f (-x)) (f.f x)
... = f.f (-x + x) - f.f x : congr_arg (λ y, y - f.f x) $ eq.symm $ f.map_add (-x) x
... = f.f 0 - f.f x : congr_arg (λ y, f.f y - f.f x) $ neg_add_self x
... = 0 - f.f x : congr_arg (λ y, y - f.f x) $ map_zero
... = -f.f x : zero_sub $ f.f x

theorem map_sub : f.f (x - y) = f.f x - f.f y := calc
f.f (x - y) = f.f (x + -y) : congr_arg f.f $ sub_eq_add_neg x y
... = f.f x + f.f (-y) : f.map_add x (-y)
... = f.f x + -f.f y : congr_arg (λ z, f.f x + z) $ map_neg
... = f.f x - f.f y : eq.symm $ sub_eq_add_neg (f.f x) (f.f y)

end hom

class subring (α : Type u) [comm_ring α] (S : set α) :=
(add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ x, x ∈ S → -x ∈ S)
(mul_mem : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

namespace subring

variables (α : Type u) [comm_ring α] (S : set α) [subring α S]

instance : comm_ring S :=
{ add := λ x y, ⟨x + y, subring.add_mem x y x.property y.property⟩,
  add_assoc := λ x y z, subtype.eq $ add_assoc x y z,
  zero := ⟨0, eq.subst (add_neg_self (1:α)) $ subring.add_mem 1 (-1) (subring.one_mem S) $ subring.neg_mem 1 $ subring.one_mem S⟩,
  zero_add := λ x, subtype.eq $ zero_add x,
  add_zero := λ x, subtype.eq $ add_zero x,
  neg := λ x, ⟨-x, subring.neg_mem x x.property⟩,
  add_left_neg := λ x, subtype.eq $ add_left_neg x,
  add_comm := λ x y, subtype.eq $ add_comm x y,
  mul := λ x y, ⟨x * y, subring.mul_mem x y x.property y.property⟩,
  mul_assoc := λ x y z, subtype.eq $ mul_assoc x y z,
  one := ⟨1, subring.one_mem S⟩,
  one_mul := λ x, subtype.eq $ one_mul x,
  mul_one := λ x, subtype.eq $ mul_one x,
  left_distrib := λ x y z, subtype.eq $ left_distrib x y z,
  right_distrib := λ x y z, subtype.eq $ right_distrib x y z,
  mul_comm := λ x y, subtype.eq $ mul_comm x y }

@[simp] lemma add (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) + ⟨y, hy⟩ = ⟨x + y, subring.add_mem x y hx hy⟩ := rfl

@[simp] lemma mul (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, subring.mul_mem x y hx hy⟩ := rfl

def hom : @hom S α (subring.comm_ring α S) _ :=
{ f := λ x, x,
  map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

end subring

def hom.comp (α : Type u) (β : Type v) (γ : Type w)
[comm_ring α] [comm_ring β] [comm_ring γ]
(g : hom β γ) (f : hom α β) : hom α γ :=
{ f := g.f ∘ f.f,
  map_add := λ x y, calc
    g.f (f.f (x + y)) = g.f (f.f x + f.f y) : congr_arg g.f $ f.map_add x y
    ... = g.f (f.f x) + g.f (f.f y) : g.map_add (f.f x) (f.f y),
  map_mul := λ x y, calc
    g.f (f.f (x * y)) = g.f (f.f x * f.f y) : congr_arg g.f $ f.map_mul x y
    ... = g.f (f.f x) * g.f (f.f y) : g.map_mul (f.f x) (f.f y),
  map_one := calc
    g.f (f.f 1) = g.f 1 : congr_arg g.f $ f.map_one
    ... = 1 : g.map_one }

class is_ideal {α : Type u} [comm_ring α] (S : set α) :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

namespace is_ideal

variables {α : Type u} [comm_ring α] (S : set α) [hs : is_ideal S]
include hs

instance : setoid α :=
{ r     := λ x y, x - y ∈ S,
  iseqv :=
    ⟨λ x, calc
      x - x = 0 : sub_self x
        ... ∈ S : hs.zero_mem,
    λ x y hxy, calc
      y - x = -(x - y)     : eq.symm (neg_sub x y)
        ... = -1 * (x - y) : eq.symm (neg_one_mul _)
        ... = (x - y) * -1 : mul_comm _ _
        ... ∈ S            : is_ideal.mul_mem hxy,
    λ x y z hxy hyz, calc
      x - z = (x - y) + (y - z) : eq.symm (sub_add_sub_cancel x y z)
        ... ∈ S                 : is_ideal.add_mem hxy hyz ⟩ }

def coset := quotient (is_ideal.setoid S)

instance : comm_ring (quotient (is_ideal.setoid S)) :=
{
  add := quotient.lift₂ (λ m n, ⟦m + n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ + m₂) - (n₁ + n₂) = (m₁ - n₁) + (m₂ - n₂) : by norm_num
                      ... ∈ S                     : is_ideal.add_mem h₁ h₂ ),
  add_assoc := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) + c) - (a + (b + c)) = 0   : by norm_num
                              ... ∈ S   : hs.zero_mem end),
  zero := ⟦0⟧,
  zero_add := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (0 + a) - (a) = 0 : by norm_num
              ... ∈ S : hs.zero_mem end),
  add_zero := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (a + 0) - (a) = 0 : by norm_num
              ... ∈ S : hs.zero_mem end),
  neg := quotient.lift (λ m, ⟦-m⟧) (λ m n h, quot.sound $ calc
    (-m) - (-n) = (m - n)*-1 : by norm_num
            ... ∈ S          : is_ideal.mul_mem h ),
  add_left_neg := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (-a + a) - (0) = 0 : by norm_num
               ... ∈ S : hs.zero_mem end),
  add_comm := quotient.ind₂ (begin intros a b, apply quotient.sound, exact calc
    (a + b) - (b + a) = 0 : by rw [add_comm, sub_self]
                  ... ∈ S : hs.zero_mem end),
  mul := quotient.lift₂ (λ m n, ⟦m * n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ * m₂) - (n₁ * n₂) = (m₁ * m₂ - m₁ * n₂) + (m₁ * n₂ - n₁ * n₂) : by norm_num
                      ... = m₁ * (m₂ - n₂) + (m₁ - n₁) * n₂ : by rw [mul_sub, sub_mul]
                      ... = (m₂ - n₂) * m₁ + (m₁ - n₁) * n₂ : by ac_refl
                      ... ∈ S : is_ideal.add_mem (is_ideal.mul_mem h₂) (is_ideal.mul_mem h₁) ),
  mul_assoc := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a * b) * c) - (a * (b * c)) = 0 : by rw [mul_assoc, sub_self]
                              ... ∈ S : hs.zero_mem end),
  one := ⟦1⟧,
  one_mul := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (1 * a) - (a) = 0 : by norm_num
              ... ∈ S : hs.zero_mem end),
  mul_one := quotient.ind (begin intro a, apply quotient.sound, exact calc
    (a * 1) - (a) = 0 : by norm_num
              ... ∈ S : hs.zero_mem end),
  left_distrib := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    (a * (b + c)) - ((a * b) + (a * c)) = 0 : by rw [left_distrib, sub_self]
                                    ... ∈ S : hs.zero_mem end),
  right_distrib := λ m n k, quotient.induction_on₃ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) * c) - ((a * c) + (b * c)) = 0 : by rw [right_distrib, sub_self]
                                    ... ∈ S : hs.zero_mem end),
  mul_comm := quotient.ind₂ (begin intros a b, apply quotient.sound, exact calc
    (a * b) - (b * a) = 0 : by rw [mul_comm, sub_self]
                  ... ∈ S : hs.zero_mem end),
}

instance coset.comm_ring : comm_ring (coset S) :=
(by apply_instance : comm_ring (quotient $ is_ideal.setoid S))

def to_quotient : hom α (coset S) :=
{ f       := quotient.mk,
  map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

@[simp] lemma add_coset (x y : α) : ⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl
@[simp] lemma mul_coset (x y : α) : ⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl
@[simp] lemma one_coset : (1:coset S) = ⟦(1:α)⟧ := rfl

end is_ideal

instance zero_ideal (α : Type u) [comm_ring α] : is_ideal {(0:α)} :=
{ zero_mem := set.mem_singleton 0,
  add_mem  := λ x y hx hy, begin rw set.mem_singleton_iff at *, rw [hx, hy], simp end,
  mul_mem  := λ x y hx, begin rw set.mem_singleton_iff at *, rw hx, simp end }

def univ_ideal (α : Type u) [comm_ring α] : is_ideal (set.univ : set α) :=
{ zero_mem := ⟨⟩,
  add_mem  := λ x y hx hy, ⟨⟩,
  mul_mem  := λ x y hx, ⟨⟩ }

def hom.preimage_ideal {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : hom α β) (S : set β) [hs : is_ideal S] : is_ideal ((f.f)⁻¹' S) :=
{ zero_mem := by simp [hom.map_zero, hs.zero_mem],
  add_mem  := λ x y hx hy, by simp [hom.map_add, @is_ideal.add_mem _ _ S _ _ _ hx hy],
  mul_mem  := λ x y hx, by simp [hom.map_mul, @is_ideal.mul_mem _ _ S _ _ _ hx] }

-- Proposition 1.1 start

section prop_1_1

variables {α : Type u} [comm_ring α] (S : set α) [hs : is_ideal S]
include hs

def contains_ideal := {i : Σ T : set α, is_ideal T // S ⊆ i.1}
def ideal_quotient := Σ i : set $ is_ideal.coset S, is_ideal i

theorem contains_ideal.ext : ∀ x y : contains_ideal S, x.val.1 = y.val.1 → x = y :=
begin
  intros x y hxy,
  cases x,
  cases y,
  cases x_val,
  cases y_val,
  cases x_val_snd,
  cases y_val_snd,
  apply subtype.eq,
  fapply sigma.eq,
  exact hxy,
  cases hxy,
  dsimp,
  congr
end

theorem ideal_quotient.ext : ∀ x y : ideal_quotient S, x.1 = y.1 → x = y :=
begin
  intros x y hxy,
  cases x,
  cases y,
  cases x_snd,
  cases y_snd,
  fapply sigma.eq,
  exact hxy,
  cases hxy,
  dsimp,
  congr
end

def contains_to_quotient : contains_ideal S → ideal_quotient S :=
λ ⟨⟨T, ht⟩, h⟩,
{ fst := quotient.mk '' T,
  snd :=
  { zero_mem := ⟨0, ht.zero_mem, rfl⟩,
    add_mem  := λ x y hx hy,
      begin
        cases hx with xw xh,
        cases hy with yw yh,
        existsi xw + yw,
        split,
        exact is_ideal.add_mem xh.1 yh.1,
        rw [←xh.2, ←yh.2],
        refl
      end,
    mul_mem  := λ x y hx,
      begin
        cases hx with xw xh,
        cases @quotient.exists_rep _ (is_ideal.setoid S) y with yw yh,
        existsi xw * yw,
        split,
        exact is_ideal.mul_mem xh.1,
        rw [←xh.2, ←yh],
        refl
      end } }

def quotient_to_contains : ideal_quotient S → contains_ideal S :=
λ ⟨T, ht⟩,
{ val :=
  { fst := _,
    snd := @hom.preimage_ideal _ _ _ _ (is_ideal.to_quotient S) T ht },
  property := λ x hx, begin
    simp [hom.preimage_ideal],
    have : ⟦x⟧ = @comm_ring.zero (is_ideal.coset S) (by apply_instance),
    apply quotient.sound,
    exact calc
      x - 0 = x : sub_zero x
        ... ∈ S : hx,
    simp [is_ideal.to_quotient],
    rw this,
    exact ht.zero_mem
  end }

theorem contains_to_quotient_to_contains : (quotient_to_contains S) ∘ (contains_to_quotient S) = id :=
begin
  apply funext,
  intros x,
  cases x with x hx,
  cases x with T ht,
  simp [function.comp, contains_to_quotient, quotient_to_contains, hom.preimage_ideal, is_ideal.to_quotient],
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
  apply quotient.sound,
  exact calc
      y - y = 0 : sub_self y
        ... ∈ S : hs.zero_mem
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
  cases @quotient.exists_rep _ (is_ideal.setoid S) y with z hz,
  existsi z,
  split,
  unfold is_ideal.to_quotient,
  dsimp,
  rwa hz,
  exact hz
end

theorem contains_to_quotient_of_subset (x y : contains_ideal S) : x.val.1 ⊆ y.val.1 → (contains_to_quotient S x).1 ⊆ (contains_to_quotient S y).1 :=
begin
  intros h z hz,
  cases x with x hx,
  cases x with T ht,
  cases y with y hy,
  cases y with U hu,
  simp [contains_to_quotient] at *,
  cases hz with w hw,
  existsi w,
  exact ⟨h hw.1, hw.2⟩
end

theorem quotient_to_contains_of_subset (x y : ideal_quotient S) : x.1 ⊆ y.1 → (quotient_to_contains S x).val.1 ⊆ (quotient_to_contains S y).val.1 :=
begin
  intros h z hz,
  cases x with T ht,
  cases y with U hu,
  simp [quotient_to_contains] at *,
  exact h hz
end

end prop_1_1

-- Proposition 1.1 end

namespace hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : hom α β)

def ker : set α := f.f⁻¹' {(0:β)}
instance ker.is_ideal : is_ideal (ker f) := preimage_ideal f {(0:β)}

def im := f.f '' set.univ
instance im.subring : subring β f.im :=
{ add_mem := λ x y hx hy,
    begin
      cases hx with m hm,
      cases hy with n hn,
      existsi m + n,
      simp [f.map_add, hm.2, hn.2]
    end,
  neg_mem := λ x hx,
    begin
      cases hx with m hm,
      existsi -m,
      simp [hom.map_neg, hm.2]
    end,
  mul_mem := λ x y hx hy,
    begin
      cases hx with m hm,
      cases hy with n hn,
      existsi m * n,
      simp [f.map_mul, hm.2, hn.2]
    end,
  one_mem := ⟨(1:α), ⟨⟩, f.map_one⟩ }

instance im.comm_ring : comm_ring f.im :=
@subring.comm_ring β _ (f.f '' set.univ) (im.subring f)

end hom

structure isomorphism (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : hom α β)
(g : hom β α)
(hfg : ∀ x, f.f (g.f x) = x)
(hgf : ∀ x, g.f (f.f x) = x)

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

noncomputable def first_isom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] (f : hom α β) :
isomorphism (is_ideal.coset f.ker) f.im :=
{ f :=
  { f := @quotient.lift α f.im (is_ideal.setoid f.ker) (λ x, ⟨f.f x, x, ⟨⟩, rfl⟩) (λ x y hxy, subtype.eq $ calc
    f.f x = f.f (y + (x - y))   : by norm_num
      ... = f.f y + f.f (x - y) : f.map_add _ _
      ... = f.f y : begin simp [has_equiv.equiv, setoid.r, hom.ker, zero_ideal, hom.preimage_ideal] at hxy, simp [hxy] end ),
    map_add :=
      begin
        apply quotient.ind₂,
        intros x y,
        simp [f.map_add],
        refl
      end,
    map_mul :=
      begin
        apply quotient.ind₂,
        intros x y,
        simp [f.map_mul],
        refl
      end,
    map_one :=
      begin
        simp [f.map_one],
        refl
      end },
  g :=
  { f := λ ⟨y, hy⟩, @quotient.mk α (is_ideal.setoid f.ker) (classical.some hy),
    map_add :=
      begin
        intros x y,
        cases x with x hx,
        cases y with y hy,
        simp [first_isom._match_1],
        change classical.some _ - (classical.some _ + classical.some _) ∈ f.ker,
        unfold hom.ker,
        unfold set.preimage,
        have hm := (classical.some_spec hx).2,
        have hn := (classical.some_spec hy).2,
        have hmn := (classical.some_spec (subring.add_mem x y hx hy)).2,
        simp at hm,
        simp at hn,
        simp at hmn,
        simp [f.map_add,hom.map_neg,hm,hn,hmn]
      end,
    map_mul :=
      begin
        intros x y,
        cases x with x hx,
        cases y with y hy,
        simp [first_isom._match_1],
        change classical.some _ - classical.some _ * classical.some _ ∈ f.ker,
        unfold hom.ker,
        unfold set.preimage,
        have hm := (classical.some_spec hx).2,
        have hn := (classical.some_spec hy).2,
        have hmn := (classical.some_spec (subring.mul_mem x y hx hy)).2,
        simp at hm,
        simp at hn,
        simp at hmn,
        simp [f.map_add,hom.map_neg,f.map_mul,hm,hn,hmn]
      end,
    map_one :=
      begin
        simp [first_isom._match_1],
        apply quotient.sound,
        change classical.some _ - (1 : α) ∈ f.ker,
        unfold hom.ker,
        unfold set.preimage,
        simp [f.map_add],
        have h := (classical.some_spec (subring.one_mem f.im)).2,
        simp at h,
        rw [hom.map_neg,h,f.map_one,add_left_neg]
      end },
  hfg := λ ⟨x, hx⟩, subtype.eq (by simp [first_isom._match_1]; simpa using classical.some_spec hx),
  hgf :=
    begin
      intro x,
      cases @quotient.exists_rep _ (is_ideal.setoid f.ker) x with y hy,
      rw ←hy,
      simp [first_isom._match_1],
      change classical.some _ - y ∈ f.ker,
      unfold hom.ker,
      unfold set.preimage,
      have hz := @classical.some_spec _ (λ z, f.f z = f.f y) ⟨y, rfl⟩,
      simp [f.map_add,hz,hom.map_neg]
    end
}
