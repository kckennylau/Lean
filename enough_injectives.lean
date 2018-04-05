import linear_algebra.linear_map_module data.rat

namespace Q_div_Z

instance Q_div_Z.setoid : setoid ℚ :=
⟨λ x y, ∃ n : ℤ, x-y = n,
 λ x, ⟨0, by simp⟩,
 λ x y ⟨n, h⟩, ⟨-n, by simp [h.symm]⟩,
 λ x y z ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by simp [hm.symm, hn.symm]⟩⟩

end Q_div_Z

def Q_div_Z : Type :=
quotient Q_div_Z.Q_div_Z.setoid

namespace Q_div_Z

instance : add_comm_group Q_div_Z :=
by refine
{ add := quotient.lift₂ (λ x y, ⟦x + y⟧) (λ a₁ a₂ b₁ b₂ h1 h2,
    have h3 : ∃ n : ℤ, a₁ - b₁ = (n:ℚ), from h1,
    have h4 : ∃ n : ℤ, a₂ - b₂ = (n:ℚ), from h2,
    let ⟨m, hm⟩ := h3 in
    let ⟨n, hn⟩ := h4 in
    quotient.sound $ ⟨m + n, by simp [hm.symm, hn.symm]⟩),
  zero := ⟦0⟧,
  neg := quotient.lift (λ x, ⟦-x⟧) (λ a b h,
    have H : ∃ n : ℤ, a - b = (n:ℚ), from h,
    let ⟨n, hn⟩ := H in
    quotient.sound $ ⟨-n, by simp [hn.symm]⟩),
  .. };
{ intros,
  try {apply quotient.induction_on a, intro a},
  try {apply quotient.induction_on b, intro b},
  try {apply quotient.induction_on c, intro c},
  apply quotient.sound, simp }

end Q_div_Z

universes u v

variables (R : Type u) [ring R]

def Hom_R_Q_div_Z : Type u :=
{ f : R → Q_div_Z // ∀ x y, f (x + y) = f x + f y }

instance Hom_R_Q_div_Z.module : module R (Hom_R_Q_div_Z R) :=
{ add := λ ⟨f, hf⟩ ⟨g, hg⟩, ⟨λ x, f x + g x, by simp [hf, hg]⟩,
  zero := ⟨λ x, 0, by simp⟩,
  neg := λ ⟨f, hf⟩, ⟨λ x, - f x, by simp [hf]⟩,
  smul := λ r ⟨f, hf⟩, ⟨λ x, f (x * r), by simp [add_mul, hf]⟩,
  add_assoc := λ ⟨f, hf⟩ ⟨g, hg⟩ ⟨k, hk⟩, subtype.eq $ funext $ λ x, add_assoc _ _ _,
  zero_add := λ ⟨f, hf⟩, subtype.eq $ funext $ λ x, zero_add _,
  add_zero := λ ⟨f, hf⟩, subtype.eq $ funext $ λ x, add_zero _,
  add_left_neg := λ ⟨f, hf⟩, subtype.eq $ funext $ λ x, add_left_neg _,
  add_comm := λ ⟨f, hf⟩ ⟨g, hg⟩, subtype.eq $ funext $ λ x, add_comm _ _,
  add_smul := λ r s ⟨f, hf⟩, subtype.eq $ funext $ λ x,
    show f (x * (r + s)) = f (x * r) + f (x * s), by simp [mul_add, hf],
  smul_add := λ r ⟨f, hf⟩ ⟨g, hf⟩, subtype.eq $ funext $ λ x, rfl,
  mul_smul := λ r s ⟨f, hf⟩, subtype.eq $ funext $ λ x,
    show f (x * (r * s)) = f (x * r * s), by simp [mul_assoc],
  one_smul := λ ⟨f, hf⟩, subtype.eq $ funext $ λ x,
    show f (x * 1) = f x, by simp }

variables (M : Type v) [module R M]

class injective extends module R M :=
(extend_map : ∀ A B [module R A] [module R B] (f : linear_map A B) (H : function.injective f.1) (g : linear_map A M), linear_map B M)
(extend_map_extends : ∀ A B [module R A] [module R B] (f : linear_map A B) (H : function.injective f.1) (g : linear_map A M) (x : A), (extend_map A B f H g).1 (f.1 x) = g.1 x)

def find_injective : Type (max u v) :=
@linear_map R M (Hom_R_Q_div_Z R) _ _ (Hom_R_Q_div_Z.module R) → Hom_R_Q_div_Z R

instance find_injective.module : module R (find_injective R M) :=
by refine
{ add := λ x y f, by letI := Hom_R_Q_div_Z.module R; from x f + y f,
  zero := λ f, by letI := Hom_R_Q_div_Z.module R; from 0,
  neg := λ x f, by letI := Hom_R_Q_div_Z.module R; from -x f,
  smul := λ r x f, by letI := Hom_R_Q_div_Z.module R; from r • x f,
  .. };
{ intros, funext, letI := Hom_R_Q_div_Z.module R, simp,
  try { apply smul_add },
  try { apply add_smul },
  try { apply mul_smul } }

def find_injective.of_module : M → (find_injective R M) :=
λ m f, ⟨λ r, (f.1 m).1 r, (f.1 m).2⟩

theorem find_injective.of_module.is_linear_map : is_linear_map (find_injective.of_module R M) :=
{ add := λ x y, funext $ λ f, by letI := Hom_R_Q_div_Z.module R; simp [find_injective.of_module]; rw f.2.1 x y; refl,
  smul := λ c x, funext $ λ f, by letI := Hom_R_Q_div_Z.module R; simp [find_injective.of_module]; rw f.2.2 c x; refl, }

-- TODO:
-- 1. show that find_injective.of_module is injective
-- 2. show that find_injective is actually injective
-- facepalm
