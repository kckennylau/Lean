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

variable (S : Type u)

namespace free_group

def ambient : Type (u+1) := Π (G : Type u) [group G] (f : S → G), G

instance ambient.group : group (ambient S) :=
by refine
{ mul := λ x y G HG f, @has_mul.mul _ (@semigroup.to_has_mul _ (@monoid.to_semigroup _ (@group.to_monoid G HG))) (@x G HG f) (@y G HG f),
  one := λ G HG f, @has_one.one _ (@monoid.to_has_one _ (@group.to_monoid G HG)),
  inv := λ x G HG f, @has_inv.inv _ (@group.to_has_inv G HG) (@x G HG f),
  .. };
{ intros, funext,
  { apply mul_assoc <|> apply mul_one <|>
    apply one_mul <|> apply mul_left_inv } }

def ambient.of_S : S → ambient S :=
λ x G HG f, f x

end free_group

def free_group : Type (u+1) :=
group.generate (free_group.ambient.of_S S '' set.univ)

namespace free_group

def of_S : S → free_group S :=
λ x, ⟨ambient.of_S S x, group.generate.basic _ ⟨x, trivial, rfl⟩⟩

instance : group (free_group S) :=
group.generate.group _

variables (H : Type u) [group H] (f : S → H)

def to_group : free_group S → H :=
λ x, x.1 H f

def to_group.is_group_hom : is_group_hom (to_group S H f) :=
λ x y, rfl

def to_group.commute (x : S) : to_group S H f (of_S S x) = f x :=
rfl

variables (g : free_group S → H)
variables (Hg1 : is_group_hom g)
variables (Hg2 : ∀ x, g (of_S S x) = f x)
include Hg1 Hg2

def to_group.unique : g = to_group S H f :=
begin
  funext x,
  cases x with x hx,
  induction hx with x1 h x1 h ih x1 x2 h1 h2 ih1 ih2,
  case group.generate.basic
  { rcases h with ⟨x2, h1, h2⟩,
    specialize Hg2 x2,
    dsimp [of_S] at Hg2,
    have H1 : (⟨ambient.of_S S x2, of_S._proof_1 S x2⟩ : free_group S) =
      ⟨x1, group.generate.basic x1 (Exists.intro x2 ⟨h1, h2⟩)⟩,
    { congr, exact h2 },
    rw H1 at Hg2,
    rw Hg2,
    dsimp [to_group],
    have h3 := congr_arg (λ z : ambient S, z H f) h2,
    dsimp at h3,
    rw ← h3,
    refl },
  case group.generate.one
  { exact Hg1.one },
  case group.generate.inv
  { have H1 : (⟨x1⁻¹, group.generate.inv x1 h⟩ : free_group S) =
      @has_inv.inv _ (@group.to_has_inv _ (free_group.group S)) ⟨x1, h⟩ := rfl,
    rw [H1, ← Hg1.inv, ih],
    refl },
  case group.generate.mul
  { have H1 : (⟨x1 * x2, group.generate.mul x1 x2 h1 h2⟩ : free_group S) =
      @has_mul.mul _ (@semigroup.to_has_mul _ (@monoid.to_semigroup _ (@group.to_monoid _ (group.generate.group _)))) ⟨x1, h1⟩ ⟨x2, h2⟩ := rfl,
    rw [H1, Hg1, ih1, ih2],
    refl }
end

end free_group
