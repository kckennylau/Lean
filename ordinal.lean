universe u

class ordinal (α : Type u) extends
  decidable_linear_order α, has_zero α, has_add α, has_mul α :=
(omega : α)
(succ : α → α)
(zero_le : ∀ x : α, 0 ≤ x)
(zero_lt_omega : 0 < omega)
(zero_or_succ_of_lt_omega : ∀ x : α, x < omega → (x = 0 ∨ ∃ y, x = succ y))
(succ_ne_zero : ∀ x : α, succ x ≠ 0)
(succ_ne_omega : ∀ x : α, succ x ≠ omega)
(lt_succ : ∀ x : α, x < succ x)
(le_of_lt_succ : ∀ {x y : α}, x < succ y → x ≤ y)
(add_zero : ∀ x : α, x + 0 = x)
(add_limit_le : ∀ {x y z : α}, y ≠ 0 → (∀ w : α, w < y → x + w < z) → x + y ≤ z)
(add_limit_gt : ∀ {x y z u : α}, u < y → x + u < z → x + y ≤ z)
(add_lt_add_left : ∀ {x y : α}, x < y → ∀ z, z + x < z + y)
(mul_zero : ∀ x : α, x * 0 = 0)
(mul_succ : ∀ x y : α, x * succ y = x * y + x)
(mul_limit : ∀ {x y z : α}, y ≠ 0 → (∀ w : α, w < y → x * y < z) → x * y ≤ z)
(transfinite_induction : ∀ (x: α) (φ : α → Prop), (∀ y : α, (∀ z : α, z < y → φ z) → φ y) → φ x)

lemma lt_of_lt_of_lt {α : Type u} [preorder α] :
∀ {a b c : α}, a < b → b < c → a < c
| a b c hab hbc := lt_of_lt_of_le hab $ le_of_lt hbc

namespace ordinal

variables {α : Type u} [ordinal α] {x y z u : α}

def ω := omega α

instance : has_one α := ⟨succ 0⟩

theorem lt_succ_of_le : x ≤ y → x < succ y
| hxy := lt_of_le_of_lt hxy $ lt_succ y

theorem le_iff_lt_succ : x ≤ y ↔ x < succ y :=
⟨lt_succ_of_le, le_of_lt_succ⟩

theorem lt_of_succ_le : succ y ≤ x → y < x
| hyx := lt_of_lt_of_le (lt_succ y) hyx

theorem succ_le_of_lt : y < x → succ y ≤ x
| hyx := le_of_not_gt $ λ hxy, not_le_of_gt hyx $ le_of_lt_succ hxy

theorem lt_iff_succ_le : y < x ↔ succ y ≤ x :=
⟨succ_le_of_lt, lt_of_succ_le⟩

theorem succ_lt : x < y → succ x < succ y
| hxy := lt_succ_of_le $ succ_le_of_lt hxy

theorem succ_le : x ≤ y → succ x ≤ succ y
| hxy := succ_le_of_lt $ lt_succ_of_le hxy

theorem lt_of_succ_lt : succ x < succ y → x < y
| hxy := lt_of_succ_le $ le_of_lt_succ hxy

theorem le_of_succ_le : succ x ≤ succ y → x ≤ y
| hxy := le_of_lt_succ $ lt_of_succ_le hxy

theorem succ_inj : succ x = succ y → x = y
| hxy := le_antisymm
         (le_of_succ_le $ le_of_eq hxy)
         (le_of_succ_le $ le_of_eq hxy.symm)

theorem succ_lt_of_lt_of_limit : (∀ w, succ w ≠ x) → y < x → succ y < x
| hx hyx := lt_of_le_of_ne (le_of_lt_succ $ succ_lt hyx) $ hx y

theorem add_succ : x + succ y = succ (x + y) :=
begin
  apply transfinite_induction y,
  intros z hy,
  apply le_antisymm,
  apply add_limit_le,
  exact succ_ne_zero z,
  intros w hwz,
  cases lt_or_eq_of_le (le_of_lt_succ hwz),
  apply lt_of_lt_of_lt (add_lt_add_left a x),
  apply lt_succ,
  rw a,
  apply lt_succ,
  apply le_of_lt_succ,
  apply succ_lt,
  apply add_lt_add_left,
  exact lt_succ z
end

theorem add_le_add_right : x < y → x + z ≤ y + z :=
begin
  intro hxy,
  apply transfinite_induction z,
  intros z' hz',
  cases decidable_linear_order.decidable_eq α z' 0,
  apply add_limit_le a,
  intros w hwz',
  apply lt_of_le_of_lt,
  exact hz' w hwz',
  exact add_lt_add_left hwz' y,
  rw [a,add_zero,add_zero],
  exact le_of_lt hxy
end

theorem zero_add : 0 + x = x :=
begin
  apply transfinite_induction x,
  intros y hy,
  cases decidable_linear_order.decidable_eq α y 0,
  apply le_antisymm,
  apply add_limit_le,
  exact a,
  intros w hwy,
  rw hy w, exact hwy, exact hwy,
  apply le_of_not_gt,
  intro hy2,
  apply ne_of_lt (add_lt_add_left hy2 0),
  apply hy _ hy2,
  rw a, exact add_zero 0
end

theorem one_add : x ≤ 1 + x :=
@transfinite_induction α _ x (λ x, x ≤ 1 + x) $ λ y hy,
le_of_not_gt $ λ hy2, not_le_of_gt (add_lt_add_left hy2 1) (hy _ hy2)

theorem one_add_eq_succ_of_lt_omega : x < ω → 1 + x = succ x :=
begin
  apply transfinite_induction x (λ x, x < ω → 1 + x = succ x),
  intros y hy,
  intro hyω,
  cases zero_or_succ_of_lt_omega _ hyω,
  rw [a,add_zero], unfold has_one.one,
  cases a,
  rw [a_1,add_succ],
  apply congr_arg,
  apply hy,
  rw a_1,
  apply lt_succ,
  apply lt_of_lt_of_lt,
  apply lt_succ,
  rw ←a_1,
  exact hyω
end

theorem one_add_omega : (1:α) + ω = ω :=
begin
  apply le_antisymm,
  apply add_limit_le,
  apply ne_of_gt,
  exact zero_lt_omega α,
  intro w,
  apply transfinite_induction w (λ w, w < ω → 1 + w < ω),
  intros y hy hyω,
  cases zero_or_succ_of_lt_omega _ hyω,
  rw [a,add_zero],
  apply succ_lt_of_lt_of_limit succ_ne_omega,
  apply zero_lt_omega α,
  cases a,
  rw [a_1,add_succ],
  apply succ_lt_of_lt_of_limit succ_ne_omega,
  rw one_add_eq_succ_of_lt_omega,
  rw ←a_1, apply hyω,
  apply lt_of_lt_of_lt,
  apply lt_succ,
  rw ←a_1,
  exact hyω,
  apply one_add
end

end ordinal
