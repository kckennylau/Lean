import data.polynomial

class algebra (R : out_param $ Type*) [comm_ring R] (A : Type*) extends ring A :=
(f : R → A) [hom : is_ring_hom f]
(commutes : ∀ r s, s * f r = f r * s)

attribute [instance] algebra.hom

namespace algebra

variables (R : Type*) (A : Type*)
variables [comm_ring R] [algebra R A]

@[simp] lemma f_add (r s : R) : f A (r + s) = f A r + f A s :=
is_ring_hom.map_add _

@[simp] lemma f_zero : f A (0 : R) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma f_neg (r : R) : f A (-r) = -f A r :=
is_ring_hom.map_neg _

@[simp] lemma f_sub (r s : R) : f A (r - s) = f A r - f A s :=
is_ring_hom.map_sub _

@[simp] lemma f_mul (r s : R) : f A (r * s) = f A r * f A s :=
is_ring_hom.map_mul _

@[simp] lemma f_one : f A (1 : R) = 1 :=
is_ring_hom.map_one _

instance to_module : module R A :=
{ smul := λ r x, f A r * x,
  smul_add := by intros; simp [mul_add],
  add_smul := by intros; simp [add_mul],
  mul_smul := by intros; simp [mul_assoc],
  one_smul := by intros; simp }

theorem smul_def {r : R} {x : A} : r • x = f A r * x :=
rfl

@[simp] lemma mul_smul (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
by rw [smul_def, smul_def, ← mul_assoc, commutes, mul_assoc]

@[simp] lemma smul_mul (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
mul_assoc _ _ _

end algebra

class is_alg_hom (R : Type*) {A : Type*} {B : Type*}
  [comm_ring R] [algebra R A] [algebra R B] (φ : A → B)
  extends is_ring_hom φ : Prop :=
(commutes : ∀ r : R, φ (r • 1) = r • 1)

namespace is_alg_hom

variables (R : Type*) (A : Type*) (B : Type*)
variables [comm_ring R] [algebra R A] [algebra R B]
variables (φ : A → B) [is_alg_hom R φ]

theorem is_alg_hom.smul (r : R) (x : A) : φ (r • x) = r • φ x :=
calc  φ (r • x)
    = φ (r • 1 * x) : by simp
... = φ (r • 1) * φ x : is_ring_hom.map_mul φ
... = r • φ x : by simp [is_alg_hom.commutes φ r]

end is_alg_hom

namespace polynomial

variables (R : Type*) (A : Type*)
variables [comm_ring R] [algebra R A]
variables [decidable_eq R] (x : A)

instance : algebra R (polynomial R) :=
{ f := C,
  commutes := λ _ _, mul_comm _ _ }

def eval' : polynomial R → A :=
λ p, p.sum (λ n c, c • x^n)

@[simp] lemma eval'_add (f g : polynomial R) :
  eval' R A x (f + g) =
  eval' R A x f + eval' R A x g :=
begin
  unfold eval',
  apply finsupp.sum_add_index,
  { intros, simp },
  intros n r s,
  simp [add_smul]
end

@[simp] lemma eval'_C_mul_X (r : R) (n : ℕ) :
  eval' R A x (C r * X ^ n) = r • x^n :=
begin
  unfold eval',
  rw ← single_eq_C_mul_X,
  rw finsupp.sum_single_index; simp
end

@[simp] lemma eval'_C (r : R) :
  eval' R A x (C r) = r • (1 : A) :=
by simpa using eval'_C_mul_X R A x r 0

@[simp] lemma eval'_X_pow (n : ℕ) :
  eval' R A x (X ^ n) = x^n :=
by simpa using eval'_C_mul_X R A x 1 n

@[simp] lemma eval'_X :
  eval' R A x (X) = x :=
by simpa using eval'_X_pow R A x 1

@[simp] lemma eval'_C_mul_X_mul (r : R) (n : ℕ) (p : polynomial R) :
  eval' R A x (C r * X ^ n * p) = (r • x^n) * eval' R A x p :=
begin
  apply polynomial.induction_on p,
  { intro s,
    rw [mul_right_comm, ← C_mul],
    rw [eval'_C_mul_X, eval'_C],
    simp [mul_smul] },
  { intros f g ih1 ih2,
    simp [mul_add, ih1, ih2] },
  intros m s ih,
  rw [← mul_assoc, mul_right_comm (C r)],
  rw [← C_mul, mul_assoc, ← pow_add],
  rw [eval'_C_mul_X, eval'_C_mul_X],
  simp [pow_add, mul_smul]
end

@[simp] lemma eval'_C_mul (r : R) (p : polynomial R) :
  eval' R A x (C r * p) = r • eval' R A x p :=
by simpa using eval'_C_mul_X_mul R A x r 0 p

instance is_alg_hom : is_alg_hom R (eval' R A x) :=
{ map_add := eval'_add R A x,
  map_mul := λ f g, by apply polynomial.induction_on f; intros; simp [add_mul,*],
  map_one := by simpa using eval'_X_pow R A x 0,
  commutes := λ r, (eval'_C_mul R A x r 1).trans $
    congr_arg _ $ by simpa using eval'_X_pow R A x 0 }

variables (p q : polynomial R)

@[simp] lemma eval'_zero : eval' R A x 0 = 0 :=
is_ring_hom.map_zero _

@[simp] lemma eval'_neg : eval' R A x (-p) = -eval' R A x p :=
is_ring_hom.map_neg _

@[simp] lemma eval'_sub : eval' R A x (p - q) = eval' R A x p - eval' R A x q :=
is_ring_hom.map_sub _

@[simp] lemma eval'_mul : eval' R A x (p * q) = eval' R A x p * eval' R A x q :=
is_ring_hom.map_mul _

@[simp] lemma eval'_one : eval' R A x 1 = 1 :=
is_ring_hom.map_one _

theorem eval'_unique (φ : polynomial R → A) [is_alg_hom R φ] (p) :
  φ p = eval' R A (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r,
    suffices : φ (C r * 1) = r • 1,
    { simpa using this },
    exact is_alg_hom.commutes φ r },
  { intros f g ih1 ih2,
    simp [is_ring_hom.map_add φ, ih1, ih2] },
  { intros n r ih,
    rw [pow_succ, mul_left_comm, is_ring_hom.map_mul φ, ih],
    simp }
end

end polynomial

variables (R : Type*) [ring R]

def ring.to_ℤ_algebra : algebra ℤ R :=
{ f := coe,
  hom := by constructor; intros; simp,
  commutes := λ n r, int.induction_on n (by simp)
    (λ i ih, by simp [mul_add, add_mul, ih])
    (λ i ih, by simp [mul_add, add_mul, ih]), }

def is_ring_hom.to_is_ℤ_alg_hom
  (R : Type*) [algebra ℤ R] (S : Type*) [algebra ℤ S]
  (f : R → S) [is_ring_hom f] : is_alg_hom ℤ f :=
{ commutes := λ i, show f (i • 1) = i • 1, from
    int.induction_on i (by simpa using is_ring_hom.map_zero f)
      (λ i ih, by rw [add_smul, add_smul, one_smul, one_smul];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [sub_smul, sub_smul, one_smul, one_smul];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih]) }

local attribute [instance] ring.to_ℤ_algebra
local attribute [instance] is_ring_hom.to_is_ℤ_alg_hom

instance : ring (polynomial ℤ) :=
comm_ring.to_ring _

example : {f : polynomial ℤ → R // is_ring_hom f} ≃ R :=
{ to_fun := λ f, f.1 polynomial.X,
  inv_fun := λ r, ⟨polynomial.eval' ℤ R r,
    @is_alg_hom.to_is_ring_hom ℤ _ _ _ (polynomial.algebra ℤ) _ _
      (polynomial.is_alg_hom _ _ r)⟩,
  left_inv := λ ⟨f, hf⟩, subtype.eq $ funext $ λ p,
    eq.symm $ @polynomial.eval'_unique ℤ _ _ _ _ f
      (@is_ring_hom.to_is_ℤ_alg_hom _ (polynomial.algebra ℤ) _ _ f hf) _,
  right_inv := λ r, by simp }
