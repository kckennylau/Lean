import data.set.basic algebra.group

universes u v

namespace group

variables {α : Type u} [group α] (S : set α)

inductive generate : set α
| basic : ∀ x ∈ S, generate x
| one : generate 1
| inv : ∀ x, generate x → generate x⁻¹
| mul : ∀ x y, generate x → generate y → generate (x * y)

namespace generate

def group : group (generate S) :=
by refine
{ mul := λ x y, ⟨x * y, mul x y x.2 y.2⟩,
  one := ⟨1, one S⟩,
  inv := λ x, ⟨x⁻¹, inv x x.2⟩,
  .. };
{ intros, apply subtype.eq,
  { apply mul_assoc <|> apply mul_one <|>
    apply one_mul <|> apply mul_left_inv } }

end generate

end group

variables (G : Type u) [group G]

namespace abelianization

def ambient : Type (max u (v+1)) := Π (H : Type v) [comm_group H] (f : G → H) (Hf : @is_group_hom G H _ (@comm_group.to_group H _inst_2) f), H

instance ambient.comm_group : comm_group (ambient.{u v} G) :=
by refine
{ mul := λ x y H HH f Hf, @has_mul.mul _ (@semigroup.to_has_mul _ (@monoid.to_semigroup _ (@group.to_monoid H (@comm_group.to_group H HH)))) (@x H HH f Hf) (@y H HH f Hf),
  one := λ H HH f Hf, @has_one.one _ (@monoid.to_has_one _ (@group.to_monoid H (@comm_group.to_group H HH))),
  inv := λ x H HH f Hf, @has_inv.inv _ (@group.to_has_inv H (@comm_group.to_group H HH)) (@x H HH f Hf),
  .. };
{ intros, funext, dsimp, letI := HH,
  { apply mul_assoc <|> apply mul_one <|>
    apply one_mul <|> apply mul_left_inv <|> apply mul_comm } }

def ambient.of_G : G → ambient G :=
λ x H HH f Hf, f x

end abelianization

def abelianization : Type (max u (v+1)) :=
group.generate (abelianization.ambient.of_G G '' set.univ)

namespace abelianization

def of_G : G → abelianization G :=
λ x, ⟨ambient.of_G G x, group.generate.basic _ ⟨x, trivial, rfl⟩⟩

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, subtype.eq $ by funext; apply HH.mul_comm,
  .. group.generate.group _ }

def of_G.is_group_hom : is_group_hom (of_G G) :=
λ x y, subtype.eq $ by funext; apply Hf

variables (H : Type v) [comm_group H] (f : G → H) (Hf : is_group_hom f)

def to_comm_group : abelianization G → H :=
λ x, x.1 H f Hf

def to_comm_group.is_group_hom : is_group_hom (to_comm_group G H f Hf) :=
λ x y, rfl

def to_comm_group.commute (x : G) : to_comm_group G H f Hf (of_G G x) = f x :=
rfl

variables (g : abelianization.{u v} G → H)
variables (Hg1 : is_group_hom g)
variables (Hg2 : ∀ x, g (of_G G x) = f x)
include Hg1 Hg2

def to_comm_group.unique : g = to_comm_group G H f Hf :=
begin
  funext x,
  cases x with x hx,
  induction hx with x1 h x1 h ih x1 x2 h1 h2 ih1 ih2,
  case group.generate.basic
  { rcases h with ⟨x2, h1, h2⟩,
    specialize Hg2 x2,
    dsimp [of_G] at Hg2,
    have H1 : (⟨ambient.of_G G x2, of_G._proof_1 G x2⟩ : abelianization G) =
      ⟨x1, group.generate.basic x1 (Exists.intro x2 ⟨h1, h2⟩)⟩,
    { congr, exact h2 },
    rw H1 at Hg2,
    rw Hg2,
    dsimp [to_comm_group],
    have h3 := congr_arg (λ z : ambient G, z H f) h2,
    dsimp at h3,
    rw ← h3,
    refl },
  case group.generate.one
  { exact Hg1.one },
  case group.generate.inv
  { have H1 : (⟨x1⁻¹, group.generate.inv x1 h⟩ : abelianization G) =
      @has_inv.inv _ (@group.to_has_inv _ (@comm_group.to_group _ (abelianization.comm_group G))) ⟨x1, h⟩ := rfl,
    rw [H1, ← Hg1.inv, ih],
    refl },
  case group.generate.mul
  { have H1 : (⟨x1 * x2, group.generate.mul x1 x2 h1 h2⟩ : abelianization G) =
      @has_mul.mul _ (@semigroup.to_has_mul _ (@monoid.to_semigroup _ (@group.to_monoid _ (group.generate.group _)))) ⟨x1, h1⟩ ⟨x2, h2⟩ := rfl,
    rw [H1, Hg1, ih1, ih2],
    refl }
end

end abelianization

namespace commutator

def commutators : set G :=
abelianization.of_G G ⁻¹' {1}

variables (x y : G)

theorem commutator : x * y * x⁻¹ * y⁻¹ ∈ commutators G :=
by dsimp [commutators]; simp;
rw [abelianization.of_G.is_group_hom G];
rw [abelianization.of_G.is_group_hom G];
rw [abelianization.of_G.is_group_hom G];
rw [← is_group_hom.inv (abelianization.of_G.is_group_hom G)];
rw [← is_group_hom.inv (abelianization.of_G.is_group_hom G)];
rw [mul_comm (abelianization.of_G G x)];
simp

end commutator
