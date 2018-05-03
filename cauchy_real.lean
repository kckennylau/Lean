import algebra.archimedean data.rat algebra.module

theorem congr_arg₂ {α β γ : Type*} (f : α → β → γ) {x₁ x₂ : α} {y₁ y₂ : β}
  (Hx : x₁ = x₂) (Hy : y₁ = y₂) : f x₁ y₁ = f x₂ y₂ :=
eq.drec (eq.drec rfl Hy) Hx

section rat

theorem lt_two_pow (n : nat) : n < 2 ^ n :=
nat.rec_on n dec_trivial $ λ n ih,
calc  n + 1
    < 2^n + 1   : nat.add_lt_add_right ih 1
... ≤ 2^n + 2^n : nat.add_le_add_left (nat.pow_le_pow_of_le_right dec_trivial $ nat.zero_le n) (2^n)
... = 2^n * 2   : eq.symm $ mul_two (2^n)
... = 2^(n+1)   : eq.symm $ nat.pow_succ 2 n

theorem rat.coe_pow (m n : nat) : (m : ℚ) ^ n = (m^n : ℕ) :=
nat.rec_on n rfl $ λ n ih, by simp [pow_succ', ih, nat.pow_succ]

theorem rat.num_pos_of_pos (r : rat) (H : r > 0) : r.num > 0 :=
int.cast_lt.1 $
calc  (r.num : ℚ)
    = r.num / (r.denom:ℤ) * r.denom : eq.symm $ div_mul_cancel _ $ ne_of_gt $ nat.cast_pos.2 r.pos
... = r * r.denom : by rw [← rat.mk_eq_div, ← rat.num_denom r]
... > 0 : mul_pos H $ nat.cast_pos.2 r.pos

theorem rat.one_le_num_of_pos (r : rat) (H : r > 0) : 1 ≤ (r.num : ℚ) :=
have H1 : ((0+1:ℤ):ℚ) = (1:ℚ), from rfl,
H1 ▸ int.cast_le.2 $ int.add_one_le_of_lt $ rat.num_pos_of_pos r H

theorem rat.lt (r : ℚ) (H : r > 0) : (1 / 2^r.denom : ℚ) < r :=
calc  (1 / 2^r.denom : ℚ)
    < 1 / r.denom : one_div_lt_one_div_of_lt (nat.cast_pos.2 r.pos)
  (trans_rel_left _ (nat.cast_lt.2 $ lt_two_pow _) (rat.coe_pow 2 _).symm)
... ≤ r.num / r.denom : div_le_div_of_le_of_pos (rat.one_le_num_of_pos r H) (nat.cast_pos.2 r.pos)
... = r.num / (r.denom:ℤ) : rfl
... = r : by rw [← rat.mk_eq_div, ← rat.num_denom r]

end rat

section list_max_min

variables {α : Type*} [decidable_linear_order α] [inhabited α] (L : list α)

def list.max : α :=
list.foldr max (inhabited.default _) L

def list.min : α :=
list.foldr min (inhabited.default _) L

theorem list.le_max : ∀ x ∈ L, x ≤ L.max :=
list.rec_on L (λ _, false.elim) $ λ hd tl ih x hx,
or.cases_on hx
  (assume H : x = hd, H.symm ▸ le_max_left hd tl.max)
  (assume H : x ∈ tl, le_trans (ih x H) (le_max_right hd tl.max))

theorem list.min_le : ∀ x ∈ L, L.min ≤ x :=
list.rec_on L (λ _, false.elim) $ λ hd tl ih x hx,
or.cases_on hx
  (assume H : x = hd, H.symm ▸ min_le_left hd tl.min)
  (assume H : x ∈ tl, le_trans (min_le_right hd tl.min) (ih x H))

end list_max_min

instance rat.seq : comm_ring (ℕ → ℚ) :=
by refine
{ add := λ f g n, f n + g n,
  zero := λ n, 0,
  neg := λ f n, -f n,
  mul := λ f g n, f n * g n,
  one := λ n, 1,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

def rat.cau_seq : set (ℕ → ℚ) :=
{ f : ℕ → ℚ | ∀ ε > 0, ∃ N, ∀ m > N, ∀ n > N, abs (f m - f n) < ε }

namespace rat.cau_seq

variables (f g : ℕ → ℚ) (hf : f ∈ rat.cau_seq) (hg : g ∈ rat.cau_seq)

theorem add : f + g ∈ rat.cau_seq := λ ε Hε,
let ⟨n1, h1⟩ := hf (ε/2) (half_pos Hε) in
let ⟨n2, h2⟩ := hg (ε/2) (half_pos Hε) in
⟨max n1 n2, λ m hm n hn,
have H1 : _ := h1 m (lt_of_le_of_lt (le_max_left _ _) hm)
  n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : _ := h2 m (lt_of_le_of_lt (le_max_right _ _) hm)
  n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs ((f m + g m) - (f n + g n))
    = abs ((f m - f n) + (g m - g n)) : by simp
... ≤ abs (f m - f n) + abs (g m - g n) : abs_add _ _
... < (ε/2) + (ε/2) : add_lt_add H1 H2
... = ε : add_halves _⟩

theorem mul : f * g ∈ rat.cau_seq := λ ε Hε,
let ⟨n1, h1⟩ := hf ε Hε in
let ⟨n2, h2⟩ := hg ε Hε in
have H1 : ε + abs (f (n1 + 1)) > 0,
  from add_pos_of_pos_of_nonneg Hε $ abs_nonneg _,
have H2 : ε + abs (g (n2 + 1)) > 0,
  from add_pos_of_pos_of_nonneg Hε $ abs_nonneg _,
let ⟨n3, h3⟩ := hf (ε/2 / (ε + abs (g (n2 + 1))))
  (div_pos (half_pos Hε) H2) in
let ⟨n4, h4⟩ := hg (ε/2 / (ε + abs (f (n1 + 1))))
  (div_pos (half_pos Hε) H1) in
⟨max (max n1 n2) (max n3 n4), λ m hm n hn,
have H3 : _ := h1 n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  (n1 + 1) (nat.lt_succ_self n1),
have H4 : _ := h2 m (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
  (n2 + 1) (nat.lt_succ_self n2),
have H5 : _ := h3 m (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hm)
  n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
have H6 : _ := h4 m (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  n (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn),
calc  abs ((f m * g m) - (f n * g n))
    = abs ((f m - f n) * g m + f n * (g m - g n)) : by simp [add_mul, mul_add]
... ≤ abs ((f m - f n) * g m) + abs (f n * (g m - g n)) : abs_add _ _
... = abs (f m - f n) * abs (g m) + abs (f n) * abs (g m - g n) : by rw [abs_mul, abs_mul]
... = abs (f m - f n) * abs (g m - g (n2 + 1) + g (n2 + 1)) + abs (f n - f (n1 + 1) + f (n1 + 1)) * abs (g m - g n) : by simp
... ≤ abs (f m - f n) * (abs (g m - g (n2 + 1)) + abs (g (n2 + 1))) + (abs (f n - f (n1 + 1)) + abs (f (n1 + 1))) * abs (g m - g n) :
  add_le_add (mul_le_mul_of_nonneg_left (abs_add _ _) (abs_nonneg _)) (mul_le_mul_of_nonneg_right (abs_add _ _) (abs_nonneg _))
... ≤ abs (f m - f n) * (ε + abs (g (n2 + 1))) + (ε + abs (f (n1 + 1))) * abs (g m - g n) :
  add_le_add (mul_le_mul_of_nonneg_left (le_of_lt $ add_lt_add_right H4 _) (abs_nonneg _)) (mul_le_mul_of_nonneg_right (le_of_lt $ add_lt_add_right H3 _) (abs_nonneg _))
... < (ε/2 / (ε + abs (g (n2 + 1)))) * (ε + abs (g (n2 + 1))) + (ε + abs (f (n1 + 1))) * (ε/2 / (ε + abs (f (n1 + 1)))) :
  add_lt_add (mul_lt_mul_of_pos_right H5 H2) (mul_lt_mul_of_pos_left H6 H1)
... = ε/2 + ε/2 : by rw [div_mul_cancel _ (ne_of_gt H2), mul_div_cancel' _ (ne_of_gt H1)]
... = ε : add_halves _⟩

theorem neg_one : (-1 : ℕ → ℚ) ∈ rat.cau_seq :=
λ ε Hε, ⟨0, λ m hm n hn, show abs (-1 - (-1)) < ε, by simpa using Hε⟩

instance : comm_ring rat.cau_seq :=
by refine
{ add := λ f g, ⟨f.1 + g.1, add _ _ f.2 g.2⟩,
  zero := ⟨0, have H : (-1 : ℕ → ℚ) + (-1) * (-1) = 0, by simp,
    H ▸ add _ _ neg_one $ mul _ _ neg_one neg_one⟩,
  neg := λ f, ⟨-f.1, have H : (-1) * f.1 = -f.1, by simp,
    H ▸ mul _ _ neg_one f.2⟩,
  mul := λ f g, ⟨f.1 * g.1, mul _ _ f.2 g.2⟩,
  one := ⟨1, have H : (-1 : ℕ → ℚ) * (-1) = 1, by simp,
    H ▸ mul _ _ neg_one neg_one⟩,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

protected def abs : rat.cau_seq :=
⟨λ n, abs (f n), λ ε Hε,
let ⟨N, HN⟩ := hf ε Hε in
⟨N, λ m hm n hn, lt_of_le_of_lt
  (abs_abs_sub_abs_le_abs_sub _ _)
  (HN m hm n hn)⟩⟩

end rat.cau_seq

def rat.null : set rat.cau_seq :=
{ f : rat.cau_seq | ∀ ε > 0, ∃ N, ∀ n > N, abs (f.1 n) < ε }

namespace rat.null

variables (f g : rat.cau_seq) (hf : f ∈ rat.null) (hg : g ∈ rat.null)

theorem add : f + g ∈ rat.null := λ ε Hε,
let ⟨n1, h1⟩ := hf (ε/2) (half_pos Hε) in
let ⟨n2, h2⟩ := hg (ε/2) (half_pos Hε) in
⟨max n1 n2, λ n hn,
have H1 : _ := h1 n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : _ := h2 n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs (f.1 n + g.1 n)
    ≤ abs (f.1 n) + abs (g.1 n) : abs_add _ _
... < (ε/2) + (ε/2) : add_lt_add H1 H2
... = ε : add_halves _⟩

theorem zero : (0 : rat.cau_seq) ∈ rat.null :=
λ ε Hε, ⟨0, λ n hn, show abs 0 < ε, by simpa using Hε⟩

theorem mul : f * g ∈ rat.null := λ ε Hε,
let ⟨n1, h1⟩ := f.2 ε Hε in
have H1 : ε + abs (f.1 (n1 + 1)) > 0,
  from add_pos_of_pos_of_nonneg Hε $ abs_nonneg _,
let ⟨n2, h2⟩ := hg (ε / (ε + abs (f.1 (n1 + 1)))) (div_pos Hε H1) in
⟨max n1 n2, λ n hn,
have H2 : _ := h1 n (lt_of_le_of_lt (le_max_left _ _) hn)
 (n1 + 1) (nat.lt_succ_self n1),
have H3 : _ := h2 n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs (f.1 n * g.1 n)
    = abs (f.1 n) * abs (g.1 n) : abs_mul _ _
... = abs (f.1 n - f.1 (n1 + 1) + f.1 (n1 + 1)) * abs (g.1 n) : by simp
... ≤ (abs (f.1 n - f.1 (n1 + 1)) + abs (f.1 (n1 + 1))) * abs (g.1 n) :
  mul_le_mul_of_nonneg_right (abs_add _ _) (abs_nonneg _)
... ≤ (ε + abs (f.1 (n1 + 1))) * abs (g.1 n) :
  mul_le_mul_of_nonneg_right (add_le_add_right (le_of_lt H2) _) (abs_nonneg _)
... < (ε + abs (f.1 (n1 + 1))) * (ε / (ε + abs (f.val (n1 + 1)))) :
  mul_lt_mul_of_pos_left H3 H1
... = ε : mul_div_cancel' _ $ ne_of_gt H1⟩

protected theorem abs : rat.cau_seq.abs f.1 f.2 ∈ rat.null := λ ε Hε,
let ⟨N, HN⟩ := hf ε Hε in
⟨N, λ n hn, show abs (abs (f.1 n)) < ε,
from (abs_abs (f.1 n)).symm ▸ HN n hn⟩

theorem of_abs (HF : rat.cau_seq.abs f.1 f.2 ∈ rat.null)
  : f ∈ rat.null := λ ε Hε,
let ⟨N, HN⟩ := HF ε Hε in
⟨N, λ n hn, (abs_abs (f.1 n)) ▸ HN n hn⟩

local attribute [instance] classical.prop_decidable

theorem abs_pos_of_not_null (H : f ∉ rat.null) :
  ∃ ε > 0, ∃ N, ∀ n > N, abs (f.1 n) > ε :=
let ⟨ε, Hε⟩ := not_forall.1 H in
let ⟨Hε1, Hε2⟩ := not_imp.1 Hε in
let ⟨N1, HN1⟩ := f.2 (ε/2) (half_pos Hε1) in
let ⟨N2, HN2⟩ := not_forall.1 $ not_exists.1 Hε2 N1 in
let ⟨HN3, HN4⟩ := not_imp.1 HN2 in
⟨ε/2, half_pos Hε1, N2, λ n hn,
have H : _ := HN1 n (lt_trans HN3 hn) N2 HN3,
calc  abs (f.1 n)
    = abs (f.1 N2 - (f.1 N2 - f.1 n)) : congr_arg abs $ eq.symm $ sub_sub_cancel _ _
... ≥ abs (f.1 N2) - abs (f.1 N2 - f.1 n) : abs_sub_abs_le_abs_sub _ _
... > ε - ε/2 : sub_lt_sub_of_le_of_lt (le_of_not_gt HN4) (abs_sub (f.1 n) (f.1 N2) ▸ H)
... = ε / 2 : sub_half ε⟩

end rat.null

instance real.setoid : setoid rat.cau_seq :=
⟨λ f g, f - g ∈ rat.null,
 λ f, by simpa using rat.null.zero,
 λ f g hfg, have H : (-1) * (f - g) = g - f, by simp,
   show g - f ∈ rat.null, from H ▸ rat.null.mul _ _ hfg,
 λ f g h h1 h2, have H : (f - g) + (g - h) = f - h, by simp,
   show f - h ∈ rat.null, from H ▸ rat.null.add _ _ h1 h2⟩

def real : Type :=
quotient real.setoid

theorem real.eq_of_eq : ∀ {x y : rat.cau_seq}, x = y → ⟦x⟧ = ⟦y⟧
| _ _ rfl := quotient.sound $ setoid.refl _

instance real.comm_ring : comm_ring real :=
by refine
{ add := λ x y, quotient.lift_on₂ x y (λ f g, ⟦f + g⟧) $
    λ f1 f2 g1 g2 hf hg, quotient.sound $
    have H : (f1 - g1) + (f2 - g2) = (f1 + f2) - (g1 + g2), by simp,
    show (f1 + f2) - (g1 + g2) ∈ rat.null,
    from H ▸ rat.null.add _ _ hf hg,
  zero := ⟦0⟧,
  neg := λ x, quotient.lift_on x (λ f, ⟦-f⟧) $
    λ f1 f2 hf, quotient.sound $
    have H : (-1) * (f1 - f2) = (-f1) - (-f2), by simp,
    show (-f1) - (-f2) ∈ rat.null,
    from H ▸ rat.null.mul _ _ hf,
  mul := λ x y, quotient.lift_on₂ x y (λ f g, ⟦f * g⟧) $
    λ f1 f2 g1 g2 hf hg, quotient.sound $
    have H : f2 * (f1 - g1) + g1 * (f2 - g2) = f1 * f2 - g1 * g2,
      by simp [mul_add, add_mul, mul_comm],
    show f1 * f2 - g1 * g2 ∈ rat.null,
    from H ▸ rat.null.add _ _ (rat.null.mul _ _ hf) (rat.null.mul _ _ hg),
  one := ⟦1⟧,
  .. };
{ intros,
  try { apply quotient.induction_on a, intro f },
  try { apply quotient.induction_on b, intro g },
  try { apply quotient.induction_on c, intro h },
  apply real.eq_of_eq,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

namespace rat.cau_seq

variables (f g h : ℕ → ℚ)

def lt : Prop :=
∃ ε > 0, ∃ N, ∀ n > N, f n + ε < g n

protected theorem lt_trans (H1 : lt f g) (H2 : lt g h) : lt f h :=
let ⟨ε1, Hε1, N1, HN1⟩ := H1 in
let ⟨ε2, Hε2, N2, HN2⟩ := H2 in
⟨ε1, Hε1, max N1 N2, λ n hn,
have H3 : n > N1 := (lt_of_le_of_lt (le_max_left _ _) hn),
have H4 : n > N2 := (lt_of_le_of_lt (le_max_right _ _) hn),
calc  f n + ε1
    < g n      : HN1 n H3
... < g n + ε2 : lt_add_of_pos_right _ Hε2
... < h n      : HN2 n H4⟩

theorem lt_asymm (H1 : lt f g) (H2 : lt g f) : false :=
let ⟨ε1, Hε1, N1, HN1⟩ := H1 in
let ⟨ε2, Hε2, N2, HN2⟩ := H2 in
have H1 : _ := HN1 (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_right _ _),
have H2 : _ := HN2 (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_left _ _),
lt_asymm
  (lt_trans (lt_add_of_pos_right _ Hε1) H1)
  (lt_trans (lt_add_of_pos_right _ Hε2) H2)

protected theorem add_lt_add_left (H : lt g h) : lt (f + g) (f + h) :=
let ⟨ε, Hε, N, HN⟩ := H in
⟨ε, Hε, N, λ n hn, show f n + g n + ε < f n + h n,
from (add_assoc (f n) (g n) ε).symm ▸ add_lt_add_left (HN n hn) _⟩

protected theorem mul_pos (Hf : lt 0 f) (Hg : lt 0 g) : lt 0 (f * g) :=
let ⟨ε1, Hε1, N1, HN1⟩ := Hf in
let ⟨ε2, Hε2, N2, HN2⟩ := Hg in
⟨ε1 * ε2, mul_pos Hε1 Hε2, max N1 N2, λ n hn,
have H1 : n > N1 := (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : n > N2 := (lt_of_le_of_lt (le_max_right _ _) hn),
have H3 : ε1 < f n := (zero_add ε1) ▸ HN1 n H1,
have H4 : ε2 < g n := (zero_add ε2) ▸ HN2 n H2,
show 0 + ε1 * ε2 < f n * g n,
from (zero_add $ ε1 * ε2).symm ▸ mul_lt_mul H3 (le_of_lt H4)
  Hε2 (le_of_lt (lt_trans Hε1 H3))⟩

theorem pos_or_neg_of_not_null (f : rat.cau_seq) (H : f ∉ rat.null) :
  lt 0 f.1 ∨ lt f.1 0 :=
let ⟨ε, Hε, N1, HN1⟩ := rat.null.abs_pos_of_not_null f H in
let ⟨N2, HN2⟩ := f.2 (ε/2) (half_pos Hε) in
have H1 : _ := HN1 (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_right _ _),
or.cases_on (lt_max_iff.1 H1)
  (assume H : ε < f.1 (N1 + N2 + 1), or.inl ⟨ε/2, half_pos Hε, N1 + N2, λ n hn,
    have H2 : _ := HN2 n (lt_of_le_of_lt (nat.le_add_left _ _) hn)
      (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_left _ _),
    calc  0 + ε/2
        = ε/2 : zero_add _
    ... = ε - ε/2 : eq.symm $ sub_half ε
    ... < f.1 (N1 + N2 + 1) - -(f.1 n - f.1 (N1 + N2 + 1)) : sub_lt_sub H (neg_lt.1 (abs_lt.1 H2).1)
    ... = f.1 (N1 + N2 + 1) + (f.1 n - f.1 (N1 + N2 + 1)) : sub_neg_eq_add _ _
    ... = f.1 n : add_sub_cancel'_right _ _⟩)
  (assume H : ε < -f.1 (N1 + N2 + 1), or.inr ⟨ε/2, half_pos Hε, N1 + N2, λ n hn,
    have H2 : _ := HN2 n (lt_of_le_of_lt (nat.le_add_left _ _) hn)
      (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_left _ _),
    calc  f.1 n + ε/2
        = f.1 n - f.1 (N1 + N2 + 1) + f.1 (N1 + N2 + 1) + ε/2 : by rw sub_add_cancel
    ... < ε/2 + -ε + ε/2 : add_lt_add_right (add_lt_add (abs_lt.1 H2).2 (lt_neg_of_lt_neg H)) _
    ... = ε/2 + ε/2 + -ε : add_right_comm _ _ _
    ... = 0 : by rw [add_halves, add_neg_self]⟩)

variables {f1 f2 g1 g2 : rat.cau_seq}
variables (hf : f1 ≈ g1)
variables (hg : f2 ≈ g2)

theorem lt_of_lt (H : lt f1.1 f2.1) : lt g1.1 g2.1 :=
let ⟨ε, Hε, N, HN⟩ := H in
let ⟨N1, HN1⟩ := hf (ε/2/2) (half_pos $ half_pos Hε) in
let ⟨N2, HN2⟩ := hg (ε/2/2) (half_pos $ half_pos Hε) in
⟨ε/2, half_pos Hε, max N (max N1 N2), λ n hn,
have H1 : _ := HN n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : _ := HN1 n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
have H3 : _ := HN2 n (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn),
calc  g1.1 n + ε/2
    = f1.1 n - (f1.1 n - g1.1 n) + ε/2 : by rw sub_sub_cancel
... < f1.1 n - -(ε/2/2) + ε/2 : add_lt_add_right (sub_lt_sub_left (abs_lt.1 H2).1 _) _
... = f1.1 n + (ε/2/2 + (ε/2/2 + ε/2/2) + ε/2/2 - ε/2/2) : by rw [sub_neg_eq_add, add_halves, add_sub_cancel, add_assoc]
... = f1.1 n + ((ε/2/2 + ε/2/2) + (ε/2/2 + ε/2/2) - ε/2/2) : by repeat {rw add_assoc}
... = f1.1 n + (ε - ε/2/2) : by repeat {rw add_halves}
... = (f1.1 n + ε) - ε/2/2 : eq.symm $ add_sub_assoc _ _ _
... < f2.1 n - (f2.1 n - g2.1 n) : sub_lt_sub H1 (abs_lt.1 H3).2
... = g2.1 n : sub_sub_cancel _ _⟩

end rat.cau_seq

namespace real

def lt (x y : real) : Prop :=
quotient.lift_on₂ x y (λ f g, rat.cau_seq.lt f.1 g.1) $
λ f1 f2 g1 g2 hf hg, propext ⟨λ H, rat.cau_seq.lt_of_lt hf hg H,
λ H, rat.cau_seq.lt_of_lt (setoid.symm hf) (setoid.symm hg) H⟩

protected theorem lt_trans (x y z : real) : lt x y → lt y z → lt x z :=
quotient.induction_on₃ x y z $ λ f g h H1 H2,
rat.cau_seq.lt_trans f.1 g.1 h.1 H1 H2

theorem lt_asymm (x y : real) : lt x y → lt y x → false :=
quotient.induction_on₂ x y $ λ f g H1 H2,
rat.cau_seq.lt_asymm f.1 g.1 H1 H2

theorem lt_trichotomy (x y : real) : lt x y ∨ x = y ∨ lt y x :=
classical.by_cases (assume h : x = y, or.inr $ or.inl h) $
quotient.induction_on₂ x y $ λ f g, assume h : ⟦f⟧ ≠ ⟦g⟧,
or.cases_on (rat.cau_seq.pos_or_neg_of_not_null (f - g) (λ H, h $ quotient.sound H))
  (assume H : rat.cau_seq.lt 0 (f - g), or.inr $ or.inr $
    have H1 : _ := rat.cau_seq.add_lt_add_left g _ _ H,
    by simpa using H1)
  (assume H : rat.cau_seq.lt (f - g) 0, or.inl $
    have H1 : _ := rat.cau_seq.add_lt_add_left g _ _ H,
    by simpa using H1)

theorem mul_pos (x y : real) : lt 0 x → lt 0 y → lt 0 (x * y) :=
quotient.induction_on₂ x y $ λ f g hf hg,
rat.cau_seq.mul_pos f g hf hg

end real

instance real.partial_order : partial_order real :=
{ lt := real.lt,
  le := λ x y, real.lt x y ∨ x = y,
  lt_iff_le_not_le := λ x y,
    ⟨assume hxy : real.lt x y, ⟨or.inl hxy,
      assume hyx : real.lt y x ∨ y = x, real.lt_asymm x y hxy $
        or.cases_on hyx id $ λ H, by subst H; from hxy⟩,
    assume hxy : _, or.cases_on hxy.1
      (assume H : real.lt x y, H)
      (assume H : x = y, false.elim $ hxy.2 $ or.inr $ eq.symm H)⟩,
  le_refl := λ x, or.inr rfl,
  le_trans := λ x y z hxy hyz, or.cases_on hxy
    (assume hxy : real.lt x y, or.cases_on hyz
      (assume hyz : real.lt y z, or.inl $ real.lt_trans _ _ _ hxy hyz)
      (assume hyz : y = z, hyz ▸ or.inl hxy))
    (assume hxy : x = y, hxy.symm ▸ hyz),
  le_antisymm := λ x y hxy hyx, or.cases_on hxy
    (assume hxy : real.lt x y, or.cases_on hyx
      (assume hyx : real.lt y x, false.elim $ real.lt_asymm _ _ hxy hyx)
      (assume hyx : y = x, eq.symm hyx))
    (assume hxy : x = y, hxy) }

instance real.linear_ordered_comm_ring : linear_ordered_comm_ring real :=
{ add_le_add_left := λ x y hxy c, (quotient.induction_on₃ x y c $
    λ f g h hfg, or.cases_on hfg
      (assume hfg : real.lt ⟦f⟧ ⟦g⟧, or.inl $
        rat.cau_seq.add_lt_add_left _ _ _ hfg)
      (assume hfg : ⟦f⟧ = ⟦g⟧, or.inr $ hfg ▸ rfl)) hxy,
  add_lt_add_left := λ x y hxy c, (quotient.induction_on₃ x y c $
    λ f g h hfg, rat.cau_seq.add_lt_add_left _ _ _ hfg) hxy,
  zero_lt_one := ⟨0.5, dec_trivial, 0, λ n hn, dec_trivial⟩,
  mul_nonneg := λ x y hx hy, or.cases_on hx
    (assume hx : 0 < x, or.cases_on hy
      (assume hy : 0 < y, or.inl $ real.mul_pos _ _ hx hy)
      (assume hy : 0 = y, or.inr $ eq.symm $ hy ▸ mul_zero _))
    (assume hx : 0 = x, or.inr $ eq.symm $ hx ▸ zero_mul _),
  mul_pos := real.mul_pos,
  le_total := λ x y, or.cases_on (real.lt_trichotomy x y)
    (assume hxy : x < y, or.inl $ or.inl hxy)
    (assume hxy, or.cases_on hxy
      (assume hxy : x = y, or.inl $ or.inr hxy)
      (assume hxy : y < x, or.inr $ or.inl hxy)),
  zero_ne_one := λ H,
    let ⟨N, HN⟩ := quotient.exact H.symm 0.5 dec_trivial in
    absurd (HN (N + 1) (nat.lt_succ_self N)) dec_trivial,
  .. real.comm_ring, .. real.partial_order }

instance real.inhabited : inhabited real :=
⟨0⟩

namespace rat.cau_seq

variables (f : rat.cau_seq) (Hf : f ∉ rat.null)

theorem inv.of_not_null : (λ n, 1 / f.1 n) ∈ rat.cau_seq := λ ε Hε,
let ⟨ε', Hε', N1, HN1⟩ := rat.null.abs_pos_of_not_null f Hf in
let ⟨N2, HN2⟩ := f.2 (ε * ε' * ε') (mul_pos (mul_pos Hε Hε') Hε') in
⟨max N1 N2, λ m hm n hn,
have H : _ := HN2 n (lt_of_le_of_lt (le_max_right _ _) hn)
  m (lt_of_le_of_lt (le_max_right _ _) hm),
have H1 : _ := HN1 m (lt_of_le_of_lt (le_max_left _ _) hm),
have H2 : _ := HN1 n (lt_of_le_of_lt (le_max_left _ _) hn),
have H3 : abs (f.1 m) > 0 := lt_trans Hε' H1,
have H4 : abs (f.1 n) > 0 := lt_trans Hε' H2,
calc  abs (1 / f.1 m - 1 / f.1 n)
    = abs ((1 / f.1 m) * (f.1 n - f.1 m) * (1 / f.1 n)) :
  congr_arg abs $ eq.symm $ one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
    (ne_zero_of_abs_ne_zero $ ne_of_gt H3)
    (ne_zero_of_abs_ne_zero $ ne_of_gt H4)
... = (1 / abs (f.1 m)) * abs (f.1 n - f.1 m) * (1 / abs (f.1 n)) :
  by rw [abs_mul, abs_mul, abs_one_div, abs_one_div]
... < (1 / ε') * (ε * ε' * ε') * (1 / ε') :
  mul_lt_mul
    (mul_lt_mul'
      (one_div_le_one_div_of_le Hε' $ le_of_lt H1)
      H
      (abs_nonneg _)
      (one_div_pos_of_pos Hε'))
    (one_div_le_one_div_of_le Hε' $ le_of_lt H2)
    (one_div_pos_of_pos H4)
    (le_of_lt $ mul_pos (one_div_pos_of_pos Hε') (mul_pos (mul_pos Hε Hε') Hε'))
... = ε : by rw [mul_assoc, mul_assoc, mul_one_div_cancel (ne_of_gt Hε'),
  mul_one, mul_comm, mul_assoc, mul_one_div_cancel (ne_of_gt Hε'), mul_one]⟩

def inv : rat.cau_seq :=
⟨_, inv.of_not_null f Hf⟩

variables (g : rat.cau_seq) (Hg : g ∉ rat.null)

theorem inv.well_defined (H : f - g ∈ rat.null) :
  inv f Hf - inv g Hg ∈ rat.null := λ ε Hε,
let ⟨ε1, Hε1, N1, HN1⟩ := rat.null.abs_pos_of_not_null f Hf in
let ⟨ε2, Hε2, N2, HN2⟩ := rat.null.abs_pos_of_not_null g Hg in
let ⟨N, HN⟩ := H (ε * ε1 * ε2) (mul_pos (mul_pos Hε Hε1) Hε2) in
⟨max N (max N1 N2), λ n hn,
have H1 : _ := HN1 n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
have H2 : _ := HN2 n (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn),
have H3 : _ := HN n (lt_of_le_of_lt (le_max_left _ _) hn),
calc  abs (1 / f.1 n - 1 / g.1 n)
    = abs ((1 / f.1 n) * (g.1 n - f.1 n) * (1 / g.1 n)) :
  congr_arg abs $ eq.symm $ one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
    (ne_zero_of_abs_ne_zero $ ne_of_gt (lt_trans Hε1 H1))
    (ne_zero_of_abs_ne_zero $ ne_of_gt (lt_trans Hε2 H2))
... = (1 / abs (f.1 n)) * abs (f.1 n - g.1 n) * (1 / abs (g.1 n)) :
  by rw [abs_mul, abs_mul, abs_one_div, abs_one_div, abs_sub]
... < (1 / ε1) * (ε * ε1 * ε2) * (1 / ε2) :
  mul_lt_mul
    (mul_lt_mul'
      (one_div_le_one_div_of_le Hε1 $ le_of_lt H1)
      H3
      (abs_nonneg _)
      (one_div_pos_of_pos Hε1))
    (one_div_le_one_div_of_le Hε2 $ le_of_lt H2)
    (one_div_pos_of_pos (lt_trans Hε2 H2))
    (le_of_lt $ mul_pos (one_div_pos_of_pos Hε1) (mul_pos (mul_pos Hε Hε1) Hε2))
... = ε : by rw [mul_assoc, mul_assoc, mul_one_div_cancel (ne_of_gt Hε2),
  mul_one, mul_comm, mul_assoc, mul_one_div_cancel (ne_of_gt Hε1), mul_one]⟩

theorem mul_inv_cancel : f * inv f Hf - 1 ∈ rat.null :=
let ⟨ε, Hε, N, HN⟩ := rat.null.abs_pos_of_not_null f Hf in
λ ε' Hε', ⟨N, λ n hn,
have H1 : abs (f.1 n) ≠ 0,
  from ne_of_gt $ lt_trans Hε $ HN n hn,
have H2 : f.1 n ≠ 0,
  from H1 ∘ abs_eq_zero.2,
have H3 : f.1 n * (1 / f.1 n) - 1 = 0,
  by rw [mul_one_div_cancel H2, sub_self],
calc  abs (f.1 n * (1 / f.1 n) - 1)
    = 0  : abs_eq_zero.2 H3
... < ε' : Hε'⟩

end rat.cau_seq

namespace real

-- short circuits
instance : has_zero real := by apply_instance
instance : has_one real := by apply_instance
instance : has_add real := by apply_instance
instance : has_neg real := by apply_instance
instance : has_mul real := by apply_instance
instance : has_scalar real real := by apply_instance
instance : add_comm_group real := by apply_instance
instance : add_comm_semigroup real := by apply_instance
instance : add_comm_monoid real := by apply_instance
instance : add_group real := by apply_instance
instance : add_left_cancel_semigroup real := by apply_instance
instance : add_monoid real := by apply_instance
instance : add_right_cancel_semigroup real := by apply_instance
instance : add_semigroup real := by apply_instance
instance : char_zero real := by apply_instance
instance : comm_semigroup real := by apply_instance
instance : comm_monoid real := by apply_instance
instance : distrib real := by apply_instance
instance : domain real := by apply_instance
instance : integral_domain real := by apply_instance
instance : linear_order real := by apply_instance
instance : linear_ordered_ring real := by apply_instance
instance : linear_ordered_semiring real := by apply_instance
instance : module real real := by apply_instance
instance : monoid real := by apply_instance
instance : mul_zero_class real := by apply_instance
instance : no_bot_order real := by apply_instance
instance : no_top_order real := by apply_instance
instance : no_zero_divisors real := by apply_instance
instance : ordered_cancel_comm_monoid real := by apply_instance
instance : ordered_comm_monoid real := by apply_instance
instance : ordered_comm_group real := by apply_instance
instance : ordered_ring real := by apply_instance
instance : ordered_semiring real := by apply_instance
instance : ring real := by apply_instance
instance : semigroup real := by apply_instance
instance : semiring real := by apply_instance
instance : zero_ne_one_class real := by apply_instance

local attribute [instance] classical.prop_decidable

noncomputable def inv (x : real) : real :=
quotient.lift_on x (λ f, dite _
  (assume H : f ∈ rat.null, (0 : real))
  (assume H : f ∉ rat.null, ⟦rat.cau_seq.inv f H⟧)) $
λ f g hfg, dite _
  (assume H : f ∈ rat.null,
    have H1 : f + (-1) * (f - g) = g := by rw [neg_one_mul, ← sub_eq_add_neg, sub_sub_cancel],
    have H2 : g ∈ rat.null, from H1 ▸ rat.null.add _ _ H (rat.null.mul _ _ hfg),
    (dif_pos H).trans (dif_pos H2).symm)
  (assume H : f ∉ rat.null,
    have H1 : g + (f - g) = f := add_sub_cancel'_right _ _,
    have H2 : g ∉ rat.null, from λ h, H $ H1 ▸ rat.null.add _ _ h hfg,
    (dif_neg H).trans $ eq.symm $ (dif_neg H2).trans $ eq.symm $ quotient.sound $
      rat.cau_seq.inv.well_defined _ _ _ _ hfg)

theorem mul_inv_cancel {x : real} : x ≠ 0 → x * real.inv x = 1 :=
quotient.induction_on x $ λ f hf,
have H : f ∉ rat.null, from λ h, hf $ quotient.sound $
  show f - 0 ∈ rat.null, from (sub_zero f).symm ▸ h,
(congr_arg _ (dif_neg H)).trans $ quotient.sound $
  rat.cau_seq.mul_inv_cancel _ _

noncomputable instance : discrete_linear_ordered_field real :=
{ inv := real.inv,
  mul_inv_cancel := @real.mul_inv_cancel,
  inv_mul_cancel := λ x, (mul_comm _ _).trans ∘ real.mul_inv_cancel,
  decidable_le := λ _ _, classical.prop_decidable _,
  inv_zero := dif_pos rat.null.zero,
  .. real.linear_ordered_comm_ring }

end real

theorem real.mk_eq_coe_nat (q : ℕ) : (q : real) = ⟦⟨λ n, q, λ ε Hε, ⟨0, λ m hm n hn, show abs (q - q : ℚ) < ε,
  from (sub_self (q:ℚ)).symm ▸ (@abs_zero ℚ _).symm ▸ Hε⟩⟩⟧ :=
nat.rec_on q rfl $ λ n ih, show (n : real) + 1 = _, by rw ih; refl

theorem real.mk_eq_coe_int (q : ℤ) : (q : real) = ⟦⟨λ n, q, λ ε Hε, ⟨0, λ m hm n hn, show abs (q - q : ℚ) < ε,
  from (sub_self (q:ℚ)).symm ▸ (@abs_zero ℚ _).symm ▸ Hε⟩⟩⟧ :=
int.cases_on q real.mk_eq_coe_nat $ λ n, show -((n : real) + 1) = _, by rw real.mk_eq_coe_nat; refl

theorem rat.mk_eq_coe_nat (n : ℕ) : (n : ℚ) = rat.mk' n 1 dec_trivial (nat.coprime_one_right n) :=
nat.rec_on n rfl $ λ n ih, show (n : ℚ) + rat.mk' 1 1 _ _ = _, by rw [ih]; dsimp [(+), (1:ℚ)];
unfold rat.add; unfold rat.mk_pnat; dsimp; congr; simp [-add_comm]; refl

theorem rat.mk_eq_coe_int (n : ℤ) : (n : ℚ) = rat.mk' n 1 dec_trivial (nat.coprime_one_right (int.nat_abs n)) :=
int.cases_on n rat.mk_eq_coe_nat $ λ i, show -((i:ℚ) + rat.mk' 1 1 _ _) = _, by rw rat.mk_eq_coe_nat; dsimp [(+), has_neg.neg, (1:ℚ)];
unfold rat.add; unfold rat.mk_pnat; unfold rat.neg; dsimp; congr; simp; rw [add_comm, int.neg_succ_of_nat_coe]; simp

theorem real.mk_eq_coe_rat (q : ℚ) : (q : real) = ⟦⟨λ n, q, λ ε Hε, ⟨0, λ m hm n hn, show abs (q - q) < ε,
  from (sub_self q).symm ▸ (@abs_zero ℚ _).symm ▸ Hε⟩⟩⟧ :=
rat.cases_on q $ λ n d p c, (div_eq_iff_mul_eq $ ne_of_gt $ (@nat.cast_pos real _ d).2 p).2 $
by rw [real.mk_eq_coe_int, real.mk_eq_coe_nat]; apply real.eq_of_eq; apply subtype.eq; funext m; dsimp;
change rat.mk' n d p c * d = (n:ℚ); rw [rat.mk_eq_coe_nat, rat.mk_eq_coe_int]; dsimp [(*)]; unfold rat.mul;
unfold rat.mk_pnat; simp; split; rw [nat.gcd_eq_right]; [rw int.mul_div_cancel, simp [int.nat_abs_mul], rw nat.div_self p, simp [int.nat_abs_mul]];
apply ne_of_gt; apply int.coe_nat_pos.2 p

theorem real.rat_eq_of_coe_eq {x y : ℚ} (H : (x : real) = y) : x = y :=
rat.cast_inj.1 H

theorem real.rat_lt_of_coe_lt {x y : ℚ} (H : (x : real) < y) : x < y :=
rat.cast_lt.1 H

theorem real.ex_rat_lt (x : real) : ∃ q : ℚ, (q : real) < x :=
quotient.induction_on x $ λ f,
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨f.1 (N + 1) - 2, trans_rel_right _ (real.mk_eq_coe_rat _)
⟨1, zero_lt_one, N, λ n hn,
calc  f.1 (N + 1) - 2 + 1
    = f.1 (N + 1) - (2 - 1) : sub_add _ _ _
... = f.1 (N + 1) - 1 : congr_arg _ $ add_sub_cancel _ _
... = f.1 (N + 1) - f.1 n + f.1 n - 1 : by rw sub_add_cancel
... < 1 + f.1 n - 1 : sub_lt_sub_right
  (add_lt_add_right (abs_lt.1 $ HN _ (nat.lt_succ_self N) _ hn).2 _) _
... = f.1 n : add_sub_cancel' _ _⟩⟩

theorem real.ex_lt_rat (x : real) : ∃ q : ℚ, x < (q : real) :=
quotient.induction_on x $ λ f,
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨f.1 (N + 1) + 2, by rw real.mk_eq_coe_rat; from
⟨1, zero_lt_one, N, λ n hn,
calc  f.1 n + 1
    = f.1 n - f.1 (N + 1) + f.1 (N + 1) + 1 : by rw sub_add_cancel
... < 1 + f.1 (N + 1) + 1 : add_lt_add_right
  (add_lt_add_right (abs_lt.1 $ HN _ hn _ (nat.lt_succ_self N)).2 _) _
... = f.1 (N + 1) + 2 : by rw [add_comm (1:ℚ), add_assoc]; refl⟩⟩

instance real.archimedean : archimedean real :=
archimedean_iff_rat_lt.2 real.ex_lt_rat

noncomputable instance real.floor_ring : floor_ring real :=
archimedean.floor_ring real

section completeness

local attribute [instance] classical.prop_decidable

parameters (A : set real) (x ub : real)
parameters (H1 : x ∈ A) (H2 : ∀ x ∈ A, x ≤ ub)

noncomputable def bin_div : ℕ → ℚ × ℚ
| 0     := (classical.some $ real.ex_rat_lt x, classical.some $ real.ex_lt_rat ub)
| (n+1) := if ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
    ((bin_div n).1, ((bin_div n).1 + (bin_div n).2)/2)
  else
    (((bin_div n).1 + (bin_div n).2)/2, (bin_div n).2)

theorem bin_div.snd_sub_fst (n : nat) : (bin_div n).2 - (bin_div n).1 = ((bin_div 0).2 - (bin_div 0).1) / 2^n :=
nat.rec_on n (div_one _).symm $ λ n ih,
if H : ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
  have H1 : bin_div (n+1) = ((bin_div n).1, ((bin_div n).1 + (bin_div n).2)/2),
    by dsimp [bin_div]; rw [if_pos H],
  calc  (bin_div (n+1)).2 - (bin_div (n+1)).1
      = (((bin_div n).1 + (bin_div n).2) - ((bin_div n).1 + (bin_div n).1))/2 : by rw [H1, sub_div, add_self_div_two]
  ... = ((bin_div n).2 - (bin_div n).1)/2 : by rw add_sub_add_left_eq_sub
  ... = (((bin_div 0).2 - (bin_div 0).1) / 2^n) / 2 : by rw ih
  ... = ((bin_div 0).2 - (bin_div 0).1) / 2^(n+1) : by rw [div_div_eq_div_mul, pow_add]; refl
else
  have H1 : bin_div (n+1) = (((bin_div n).1 + (bin_div n).2)/2, (bin_div n).2),
    by dsimp [bin_div]; rw [if_neg H],
  calc  (bin_div (n+1)).2 - (bin_div (n+1)).1
      = (((bin_div n).2 + (bin_div n).2) - ((bin_div n).1 + (bin_div n).2))/2 : by rw [H1, sub_div, add_self_div_two]
  ... = ((bin_div n).2 - (bin_div n).1)/2 : by rw add_sub_add_right_eq_sub
  ... = (((bin_div 0).2 - (bin_div 0).1) / 2^n) / 2 : by rw ih
  ... = ((bin_div 0).2 - (bin_div 0).1) / 2^(n+1) : by rw [div_div_eq_div_mul, pow_add]; refl

theorem bin_div.zero : (bin_div 0).1 < (bin_div 0).2 :=
real.rat_lt_of_coe_lt $
calc  ((bin_div 0).1 : real)
    < x : classical.some_spec $ real.ex_rat_lt x
... ≤ ub : H2 x H1
... < (bin_div 0).2 : classical.some_spec $ real.ex_lt_rat ub

theorem bin_div.fst_lt_snd_self (n : nat) : (bin_div n).1 < (bin_div n).2 :=
lt_of_sub_pos $ trans_rel_left _
  (div_pos (sub_pos_of_lt bin_div.zero) $ pow_pos two_pos _)
  (bin_div.snd_sub_fst n).symm

theorem bin_div.lt_snd (r) (hr : r ∈ A) (n : nat) : r < ((bin_div n).2 : real) :=
nat.rec_on n
  (calc r
      ≤ ub : H2 r hr
  ... < (bin_div 0).2 : classical.some_spec $ real.ex_lt_rat ub) $ λ n ih,
if H : ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
  have H1 : (bin_div (n+1)).2 = ((bin_div n).1 + (bin_div n).2)/2,
    by dsimp [bin_div]; rw [if_pos H],
  trans_rel_left _ (H r hr) $ congr_arg _ H1.symm
else
  have H1 : (bin_div (n+1)).2 = (bin_div n).2,
    by dsimp [bin_div]; rw [if_neg H],
  trans_rel_left _ ih $ congr_arg _ H1.symm

theorem bin_div.ex_fst_le (n : nat) : ∃ x ∈ A, ((bin_div n).1 : real) ≤ x :=
nat.rec_on n ⟨x, H1, le_of_lt $ classical.some_spec $ real.ex_rat_lt x⟩ $ λ n ih,
if H : ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
  have H1 : (bin_div (n+1)).1 = (bin_div n).1,
    by dsimp [bin_div]; rw [if_pos H],
  let ⟨y, hy1, hy2⟩ := ih in
  ⟨y, hy1, trans_rel_right _ (congr_arg _ H1) hy2⟩
else
  have H1 : (bin_div (n+1)).1 = ((bin_div n).1 + (bin_div n).2)/2,
    by dsimp [bin_div]; rw [if_neg H],
  by simpa [not_forall, H1] using H

theorem bin_div.fst_le_succ (n : nat) : (bin_div n).1 ≤ (bin_div (n+1)).1 :=
if H : ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
  have H1 : (bin_div (n+1)).1 = (bin_div n).1,
    by dsimp [bin_div]; rw [if_pos H],
  le_of_eq H1.symm
else
  have H1 : (bin_div (n+1)).1 = ((bin_div n).1 + (bin_div n).2)/2,
    by dsimp [bin_div]; rw [if_neg H],
  trans_rel_left _ (trans_rel_right _ (add_self_div_two _).symm $
    (div_le_div_right two_pos).2 $ add_le_add_left
      (le_of_lt $ bin_div.fst_lt_snd_self n) _) H1.symm

theorem bin_div.snd_le_succ (n : nat) : (bin_div (n+1)).2 ≤ (bin_div n).2 :=
if H : ∀ x ∈ A, x < (((bin_div n).1 + (bin_div n).2)/2 : ℚ) then
  have H1 : (bin_div (n+1)).2 = ((bin_div n).1 + (bin_div n).2)/2,
    by dsimp [bin_div]; rw [if_pos H],
  trans_rel_right _ H1 $ le_of_lt $ trans_rel_left _
    ((div_lt_div_right two_pos).2 $ add_lt_add_right (bin_div.fst_lt_snd_self n) _)
    (add_self_div_two _)
else
  have H1 : (bin_div (n+1)).2 = (bin_div n).2,
    by dsimp [bin_div]; rw [if_neg H],
  le_of_eq H1

theorem bin_div.fst_le : ∀ n m : nat, n ≤ m → (bin_div n).1 ≤ (bin_div m).1
| _ _     (nat.less_than_or_equal.refl n) := le_refl _
| n (m+1) (nat.less_than_or_equal.step H) := le_trans
  (bin_div.fst_le n m H) (bin_div.fst_le_succ m)

theorem bin_div.snd_le : ∀ n m : nat, n ≤ m → (bin_div m).2 ≤ (bin_div n).2
| _ _     (nat.less_than_or_equal.refl n) := le_refl _
| n (m+1) (nat.less_than_or_equal.step H) := le_trans
  (bin_div.snd_le_succ m) (bin_div.snd_le n m H)

theorem bin_div.fst_lt_snd (n m : nat) : (bin_div n).1 < (bin_div m).2 :=
or.cases_on (@nat.le_total m n)
  (assume H : m ≤ n, lt_of_lt_of_le (bin_div.fst_lt_snd_self n) $ bin_div.snd_le m n H)
  (assume H : n ≤ m, lt_of_le_of_lt (bin_div.fst_le n m H) (bin_div.fst_lt_snd_self m))

theorem bin_div.snd_sub_fst_le : ∀ n m : nat, n ≤ m → (bin_div n).2 - (bin_div m).1 ≤ ((bin_div 0).2 - (bin_div 0).1) / 2^n
| _ _     (nat.less_than_or_equal.refl n) := le_of_eq $ bin_div.snd_sub_fst n
| n (m+1) (nat.less_than_or_equal.step H) := le_trans
  (sub_le_sub_left (bin_div.fst_le_succ m) _)
  (bin_div.snd_sub_fst_le n m H)

theorem bin_div.fst_sub_fst_lt_pow (n m : nat) : (bin_div n).1 - (bin_div m).1 < ((bin_div 0).2 - (bin_div 0).1) / 2^m :=
trans_rel_left _ (sub_lt_sub_right (bin_div.fst_lt_snd n m) _) (bin_div.snd_sub_fst m)

theorem bin_div.snd_sub_snd_lt_pow (n m : nat) : (bin_div n).2 - (bin_div m).2 < ((bin_div 0).2 - (bin_div 0).1) / 2^n :=
trans_rel_left _ (sub_lt_sub_left (bin_div.fst_lt_snd n m) _) (bin_div.snd_sub_fst n)

theorem bin_div.fst_cau_seq : prod.fst ∘ bin_div ∈ rat.cau_seq := λ ε Hε,
let N := (ε / ((bin_div 0).2 - (bin_div 0).1)).denom in
⟨N, λ m hm n hn,
have H1 : (bin_div m).1 - (bin_div (N+1)).1 ≥ 0, from
sub_nonneg_of_le $ bin_div.fst_le (N+1) m hm,
have H2 : (bin_div n).1 - (bin_div (N+1)).1 ≥ 0, from
sub_nonneg_of_le $ bin_div.fst_le (N+1) n hn,
calc  abs ((bin_div m).1 - (bin_div n).1)
    ≤ abs ((bin_div m).1 - (bin_div (N+1)).1) + abs ((bin_div (N+1)).1 - (bin_div n).1) : abs_sub_le _ _ _
... = abs ((bin_div m).1 - (bin_div (N+1)).1) + abs ((bin_div n).1 - (bin_div (N+1)).1) : by rw abs_sub (bin_div n).1
... = ((bin_div m).1 - (bin_div (N+1)).1) + ((bin_div n).1 - (bin_div (N+1)).1) : by rw [abs_of_nonneg H1, abs_of_nonneg H2]
... < _ : add_lt_add (bin_div.fst_sub_fst_lt_pow m (N+1)) (bin_div.fst_sub_fst_lt_pow n (N+1))
... = ((bin_div 0).2 - (bin_div 0).1) / (2^N) : by rw [pow_succ', ← div_div_eq_div_mul, add_halves]
... = ((bin_div 0).2 - (bin_div 0).1) * (1 / (2^N)) : div_eq_mul_one_div _ _
... < ((bin_div 0).2 - (bin_div 0).1) * (ε / ((bin_div 0).2 - (bin_div 0).1)) : mul_lt_mul_of_pos_left
  (rat.lt _ $ div_pos Hε $ sub_pos_of_lt bin_div.zero) (sub_pos_of_lt bin_div.zero)
... = ε : mul_div_cancel' _ $ ne_of_gt $ sub_pos_of_lt bin_div.zero⟩

theorem bin_div.snd_cau_seq : prod.snd ∘ bin_div ∈ rat.cau_seq := λ ε Hε,
let N := (ε / ((bin_div 0).2 - (bin_div 0).1)).denom in
⟨N, λ m hm n hn,
have H1 : (bin_div (N+1)).2 - (bin_div m).2 ≥ 0, from
sub_nonneg_of_le $ bin_div.snd_le (N+1) m hm,
have H2 : (bin_div (N+1)).2 - (bin_div n).2 ≥ 0, from
sub_nonneg_of_le $ bin_div.snd_le (N+1) n hn,
calc  abs ((bin_div m).2 - (bin_div n).2)
    ≤ abs ((bin_div m).2 - (bin_div (N+1)).2) + abs ((bin_div (N+1)).2 - (bin_div n).2) : abs_sub_le _ _ _
... = abs ((bin_div (N+1)).2 - (bin_div m).2) + abs ((bin_div (N+1)).2 - (bin_div n).2) : by rw abs_sub
... = ((bin_div (N+1)).2 - (bin_div m).2) + ((bin_div (N+1)).2 - (bin_div n).2) : by rw [abs_of_nonneg H1, abs_of_nonneg H2]
... < _ : add_lt_add (bin_div.snd_sub_snd_lt_pow (N+1) m) (bin_div.snd_sub_snd_lt_pow (N+1) n)
... = ((bin_div 0).2 - (bin_div 0).1) / (2^N) : by rw [pow_succ', ← div_div_eq_div_mul, add_halves]
... = ((bin_div 0).2 - (bin_div 0).1) * (1 / (2^N)) : div_eq_mul_one_div _ _
... < ((bin_div 0).2 - (bin_div 0).1) * (ε / ((bin_div 0).2 - (bin_div 0).1)) : mul_lt_mul_of_pos_left
  (rat.lt _ $ div_pos Hε $ sub_pos_of_lt bin_div.zero) (sub_pos_of_lt bin_div.zero)
... = ε : mul_div_cancel' _ $ ne_of_gt $ sub_pos_of_lt bin_div.zero⟩

noncomputable def sup : real :=
⟦⟨prod.snd ∘ bin_div, bin_div.snd_cau_seq⟩⟧

theorem bin_div.sup_le_snd (n : nat) : sup ≤ (bin_div n).2 :=
(real.mk_eq_coe_rat (bin_div n).2).symm ▸
(le_of_not_gt $ λ ⟨ε, Hε, N, HN⟩, lt_asymm
  (HN (n+N+1) (nat.succ_le_succ $ nat.le_add_left _ _))
  (lt_of_le_of_lt
    (bin_div.snd_le n (n+N+1) (nat.le_add_right n (N+1)))
    (lt_add_of_pos_right _ Hε)))

theorem bin_div.mk_fst_eq_sup : (⟦⟨prod.fst ∘ bin_div, bin_div.fst_cau_seq⟩⟧ : real) = sup :=
quotient.sound $ λ ε Hε,
let N := (ε / ((bin_div 0).2 - (bin_div 0).1)).denom in
⟨N, λ n hn,
have H1 : (2:ℚ)^n > (2:ℚ)^N, from
calc  (2:ℚ)^n
    = ((2^n:ℕ):ℚ) : rat.coe_pow 2 n
... > ((2^N:ℕ):ℚ) : nat.cast_lt.2 $ nat.pow_lt_pow_of_lt_right (nat.lt_succ_self 1) hn
... = (2:ℚ)^N      : eq.symm $ rat.coe_pow 2 N,
have H2 : (2:ℚ)^n > (2:ℚ)^N, from
calc  (2:ℚ)^n
    = ((2^n:ℕ):ℚ) : rat.coe_pow 2 n
... > ((2^N:ℕ):ℚ) : nat.cast_lt.2 $ nat.pow_lt_pow_of_lt_right (nat.lt_succ_self 1) hn
... = (2:ℚ)^N      : eq.symm $ rat.coe_pow 2 N,
calc  abs ((bin_div n).1 - (bin_div n).2)
    = abs ((bin_div n).2 - (bin_div n).1) : abs_sub _ _
... = (bin_div n).2 - (bin_div n).1 : abs_of_pos $ sub_pos_of_lt $ bin_div.fst_lt_snd_self n
... = ((bin_div 0).2 - (bin_div 0).1) / 2^n : bin_div.snd_sub_fst n
... < ((bin_div 0).2 - (bin_div 0).1) / 2^N :
  (div_lt_div_left (sub_pos_of_lt bin_div.zero) (pow_pos two_pos _) (pow_pos two_pos _)).2 H1
... = ((bin_div 0).2 - (bin_div 0).1) * (1 / (2^N)) : div_eq_mul_one_div _ _
... < ((bin_div 0).2 - (bin_div 0).1) * (ε / ((bin_div 0).2 - (bin_div 0).1)) : mul_lt_mul_of_pos_left
  (rat.lt _ $ div_pos Hε $ sub_pos_of_lt bin_div.zero) (sub_pos_of_lt bin_div.zero)
... = ε : mul_div_cancel' _ $ ne_of_gt $ sub_pos_of_lt bin_div.zero⟩

theorem le_sup (r : real) : r ∈ A → r ≤ sup :=
quotient.induction_on r $ λ f hf, le_of_not_gt $ λ ⟨ε1, Hε1, N1, HN1⟩,
let ⟨N2, HN2⟩ := f.2 (ε1/2) (half_pos Hε1) in
let ⟨ε3, Hε3, N3, HN3⟩ := trans_rel_left _ (bin_div.lt_snd _ hf (N1+N2+1)) (real.mk_eq_coe_rat _) in
have H1 : _ := HN1 (N1+N2+1) (nat.succ_le_succ $ nat.le_add_right _ _),
have H2 : _ := HN2 (N1+N2+1) (nat.succ_le_succ $ nat.le_add_left _ _)
  (N2+N3+1) (nat.succ_le_succ $ nat.le_add_right _ _),
have H3 : _ := HN3 (N2+N3+1) (nat.succ_le_succ $ nat.le_add_left _ _),
lt_irrefl _ $
calc  f.1 (N2+N3+1) + ε1
    < f.1 (N2+N3+1) + ε3 + ε1 : add_lt_add_right (lt_add_of_pos_right _ Hε3) _
... < (bin_div (N1+N2+1)).2 + ε1 : add_lt_add_right H3 _
... < f.1 (N1+N2+1) : H1
... = f.1 (N2+N3+1) + (f.1 (N1+N2+1) - f.1 (N2+N3+1)) : eq.symm $ add_sub_cancel'_right _ _
... < f.1 (N2+N3+1) + ε1/2 : add_lt_add_left (abs_lt.1 H2).2 _
... < f.1 (N2+N3+1) + ε1 : add_lt_add_left (half_lt_self Hε1) _

theorem sup_le (r : real) : (∀ x ∈ A, x ≤ r) → sup ≤ r :=
quotient.induction_on r $ λ f hf, bin_div.mk_fst_eq_sup ▸ (le_of_not_gt $ λ ⟨ε, Hε, N1, HN1⟩,
let ⟨N2, HN2⟩ := f.2 (ε/2) (half_pos Hε) in
let ⟨r, hr1, hr2⟩ := bin_div.ex_fst_le (N1+N2+1) in
have H1 : _ := HN1 (N1+N2+1) (nat.succ_le_succ $ nat.le_add_right _ _),
not_lt_of_ge (le_trans hr2 $ hf r hr1) $
(real.mk_eq_coe_rat (bin_div (N1+N2+1)).1).symm ▸
⟨ε/2, half_pos Hε, N2, λ n hn,
have H2 : _ := HN2 n hn (N1+N2+1) (nat.succ_le_succ $ nat.le_add_left _ _),
calc  f.1 n + ε/2
    = f.1 (N1+N2+1) + (f.1 n - f.1 (N1+N2+1)) + ε/2 : by rw add_sub_cancel'_right
... < f.1 (N1+N2+1) + ε/2 + ε/2 : add_lt_add_right (add_lt_add_left (abs_lt.1 $ H2).2 _) _
... = f.1 (N1+N2+1) + (ε/2 + ε/2) : add_assoc _ _ _
... = f.1 (N1+N2+1) + ε : by rw add_halves
... < (bin_div (N1+N2+1)).1 : H1⟩)

theorem ex_sup_sub_le (ε : real) (Hε : ε > 0) :
  ∃ r ∈ A, sup - ε ≤ r :=
classical.by_contradiction $ λ H,
have H3 : sup ≤ sup - ε,
  from sup_le (sup - ε) $ λ r hr,
    le_of_not_le $ not_bex.1 H r hr,
not_lt_of_le H3 $ sub_lt_self sup Hε

end completeness

section inf

parameters (A : set real) (x lb : real)
parameters (H1 : x ∈ A) (H2 : ∀ x ∈ A, lb ≤ x)

noncomputable def inf : real :=
-sup (has_neg.neg ⁻¹' A) (-x) (-lb)
  (show -(-x) ∈ A, from (neg_neg x).symm ▸ H1)
  (λ r hr, le_neg_of_le_neg $ H2 (-r) hr)

theorem inf_le (r : real) (H : r ∈ A) : inf ≤ r :=
neg_le_of_neg_le $ le_sup _ _ _ _ _ (-r) $
show -(-r) ∈ A, from (neg_neg r).symm ▸ H

theorem le_inf (r : real) (H : ∀ x ∈ A, r ≤ x) : r ≤ inf :=
le_neg_of_le_neg $ sup_le _ _ _ _ _ (-r) $ λ x hx,
le_neg_of_le_neg $ H (-x) hx

end inf

instance real.seq : comm_ring (ℕ → real) :=
by refine
{ add := λ f g n, f n + g n,
  zero := λ n, 0,
  neg := λ f n, -f n,
  mul := λ f g n, f n * g n,
  one := λ n, 1,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

namespace real

def cau_seq : set (ℕ → real) :=
{ f | ∀ ε > 0, ∃ N, ∀ m > N, ∀ n > N, abs (f m - f n) < ε }

noncomputable def lim_sup (f : ℕ → real) (ub lb : real)
  (H1 : ∀ m, f m ≤ ub) (H2 : ∀ m, ∃ k ≥ m, lb ≤ f m) : real :=
inf
  { x | ∃ m, x = sup
    { y | ∃ k ≥ m, y = f k }
    (f m) ub ⟨m, nat.le_refl _, rfl⟩ (λ r ⟨k, hr1, hr2⟩, hr2.symm ▸ H1 k) }
  _ lb ⟨0, rfl⟩
  (λ r ⟨m, hr⟩, let ⟨k, hk1, hk2⟩ := H2 m in
    le_trans hk2 $ hr.symm ▸ le_sup _ _ _ _ _ _ ⟨m, nat.le_refl _, rfl⟩)

variable (f : cau_seq)

theorem cau_seq.ub : ∃ ub, ∀ n, f.1 n ≤ ub :=
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨max (((list.range (N+1)).map f.1).max) (f.1 (N+1) + 1), λ n,
or.cases_on (nat.lt_or_ge n (N+1))
  (assume H : n < N + 1, le_max_left_of_le $ list.le_max _ _ $
    list.mem_map_of_mem _ $ list.mem_range.2 H)
  (assume H : n ≥ N + 1, le_max_right_of_le $ le_of_lt $
    calc  f.1 n
        = f.1 (N+1) + (f.1 n - f.1 (N+1)) : eq.symm $ add_sub_cancel'_right _ _
    ... < f.1 (N+1) + 1 : add_lt_add_left (abs_lt.1 $ HN _ (nat.lt_of_succ_le H)
      (N+1) (nat.lt_succ_self _)).2 _ )⟩

theorem cau_seq.lb : ∃ lb, ∀ n, lb ≤ f.1 n :=
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨min (((list.range (N+1)).map f.1).min) (f.1 (N+1) - 1), λ n,
or.cases_on (nat.lt_or_ge n (N+1))
  (assume H : n < N + 1, min_le_left_of_le $ list.min_le _ _ $
    list.mem_map_of_mem _ $ list.mem_range.2 H)
  (assume H : n ≥ N + 1, min_le_right_of_le $ le_of_lt $
    calc  f.1 n
        = f.1 (N+1) + (f.1 n - f.1 (N+1)) : eq.symm $ add_sub_cancel'_right _ _
    ... > f.1 (N+1) + -1 : add_lt_add_left (abs_lt.1 $ HN _ (nat.lt_of_succ_le H)
      (N+1) (nat.lt_succ_self _)).1 _ )⟩

noncomputable def lim : real :=
lim_sup f.1 (classical.some $ cau_seq.ub f) (classical.some $ cau_seq.lb f)
  (classical.some_spec $ cau_seq.ub f)
  (λ m, ⟨m, nat.le_refl _, classical.some_spec (cau_seq.lb f) m⟩)

def close (f : ℕ → real) (L : real) : Prop :=
∀ ε > 0, ∃ N, ∀ n > N, abs (f n - L) < ε

theorem lim_close : close f.1 (lim f) := λ ε Hε,
let ⟨N, HN⟩ := f.2 (ε/2) (half_pos Hε) in
⟨N, λ n hn, abs_lt_of_lt_of_neg_lt
  (have H1 : f.1 n - ε/2 ≤ lim f,
    from le_inf _ _ _ _ _ _ $ λ r ⟨m, hr⟩, hr.symm ▸
      le_trans
        (le_of_lt $ sub_lt_of_sub_lt (abs_lt.1 $ HN n hn _ $ lt_of_lt_of_le hn $ le_max_right _ _).2)
        (le_sup _ _ _ _ _ _ ⟨max m n, le_max_left _ _, rfl⟩),
  sub_lt_of_sub_lt $ lt_of_lt_of_le (sub_lt_sub_left (half_lt_self Hε) _) H1)
  (calc -(f.1 n - lim f)
      = lim f - f.1 n : neg_sub _ _
  ... ≤ _ - f.1 n : sub_le_sub_right (inf_le _ _ _ _ _ _ ⟨n, rfl⟩) _
  ... ≤ (f.1 n + ε/2) - f.1 n : sub_le_sub_right (sup_le _ _ _ _ _ _ $ λ r ⟨k, hk1, hk2⟩,
    hk2.symm ▸ le_of_lt $ lt_add_of_sub_left_lt (abs_lt.1 $ HN k (gt_of_ge_of_gt hk1 hn) n hn).2) _
  ... = ε/2 : add_sub_cancel' _ _
  ... < ε : half_lt_self Hε)⟩

theorem lim_def (L : real) : lim f = L ↔ close f.1 L :=
iff.intro
  (assume H : lim f = L, H ▸ lim_close f)
  (assume H : close f.1 L,
    classical.by_contradiction $ assume H1 : lim f ≠ L,
    have H2 : abs (lim f - L) > 0,
      from abs_pos_of_ne_zero $ mt eq_of_sub_eq_zero H1,
    let ⟨N1, HN1⟩ := H _ (half_pos H2) in
    let ⟨N2, HN2⟩ := lim_close f _ (half_pos H2) in
    have H3 : _ := HN1 (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_right _ _),
    have H4 : _ := HN2 (N1 + N2 + 1) (nat.succ_le_succ $ nat.le_add_left _ _),
    not_lt_of_ge (abs_sub_le (lim f) (f.1 (N1+N2+1)) L) $
    calc  abs (lim f - f.1 (N1+N2+1)) + abs (f.1 (N1+N2+1) - L)
        = abs (f.1 (N1+N2+1) - lim f) + abs (f.1 (N1+N2+1) - L) : by rw abs_sub
    ... < _ + _ : add_lt_add H4 H3
    ... = _     : add_halves _)

def cau_seq.of_close (f : ℕ → real)
  (H : ∃ L, close f L) : cau_seq :=
⟨f, λ ε Hε,
let ⟨L, H⟩ := H in
let ⟨N, HN⟩ := H (ε/2) (half_pos Hε) in
⟨N, λ m hm n hn,
calc  abs (f m - f n)
    ≤ abs (f m - L) + abs (L - f n) : abs_sub_le _ _ _
... = abs (f m - L) + abs (f n - L) : by rw abs_sub (f n)
... < ε/2 + ε/2                     : add_lt_add (HN m hm) (HN n hn)
... = ε                             : add_halves ε⟩⟩

theorem lim.of_close (f : ℕ → real)
  (L : real) (H : close f L) :
  lim (cau_seq.of_close f ⟨L, H⟩) = L :=
(lim_def _ _).2 H

theorem ex_seq_to_sup (A : set real) (x ub : real)
  (H1 : x ∈ A) (H2 : ∀ x ∈ A, x ≤ ub) :
  ∃ f : cau_seq, (∀ n, f.1 n ∈ A) ∧ lim f = sup A x ub H1 H2 :=
have H3 : ∀ n : ℕ, ∃ r ∈ A, sup A x ub H1 H2 - (1/(n+1)) ≤ r,
  from λ n, ex_sup_sub_le _ _ _ _ _ _
    (one_div_pos_of_pos $ (@nat.cast_lt real _ 0 (n+1)).2 $ nat.zero_lt_succ n),
⟨cau_seq.of_close
  (λ n, classical.some $ H3 n)
  ⟨sup A x ub H1 H2, λ ε Hε, ⟨int.nat_abs ⌈1/ε⌉, λ n hn,
    let r := classical.some $ H3 n in
    let (⟨hr1, hr2⟩ : ∃ (H : r ∈ A), sup A x ub H1 H2 - _ ≤ r) :=
      classical.some_spec $ H3 n in
    have H4 : ⌈1/ε⌉ > 0,
      from lt_ceil.2 $ one_div_pos_of_pos Hε,
    calc  abs (r - sup A x ub H1 H2)
        = abs (sup A x ub H1 H2 - r) : abs_sub _ _
    ... = sup A x ub H1 H2 - r : abs_of_nonneg $ sub_nonneg_of_le $ le_sup _ _ _ _ _ _ hr1
    ... ≤ 1/(n+1) : sub_le_of_sub_le hr2
    ... < 1/(int.nat_abs ⌈1/ε⌉:int) : one_div_lt_one_div_of_lt
      ((@nat.cast_lt real _ 0 _).2 $ int.nat_abs_pos_of_ne_zero $ ne_of_gt H4)
      ((@nat.cast_lt real _ _ (n+1)).2 $ lt_trans hn $ nat.lt_succ_self n)
    ... = 1/⌈1/ε⌉ : by rw int.nat_abs_of_nonneg (le_of_lt H4)
    ... ≤ 1/(1/ε) : (div_le_div_left (@zero_lt_one real _) ((@int.cast_lt real _ 0 _).2 H4)
      (one_div_pos_of_pos Hε)).2 $ le_ceil _
    ... = ε : one_div_one_div _⟩⟩,
λ n, (classical.some_spec $ H3 n).fst,
lim.of_close _ _ _⟩

end real

namespace real.cau_seq

variables (r : real) (f g : ℕ → real) (hf : f ∈ real.cau_seq) (hg : g ∈ real.cau_seq)

theorem add : f + g ∈ real.cau_seq := λ ε Hε,
let ⟨n1, h1⟩ := hf (ε/2) (half_pos Hε) in
let ⟨n2, h2⟩ := hg (ε/2) (half_pos Hε) in
⟨max n1 n2, λ m hm n hn,
have H1 : _ := h1 m (lt_of_le_of_lt (le_max_left _ _) hm)
  n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : _ := h2 m (lt_of_le_of_lt (le_max_right _ _) hm)
  n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs ((f m + g m) - (f n + g n))
    = abs ((f m - f n) + (g m - g n)) : by simp
... ≤ abs (f m - f n) + abs (g m - g n) : abs_add _ _
... < (ε/2) + (ε/2) : add_lt_add H1 H2
... = ε : add_halves _⟩

theorem mul : f * g ∈ real.cau_seq := λ ε Hε,
let ⟨n1, h1⟩ := hf ε Hε in
let ⟨n2, h2⟩ := hg ε Hε in
have H1 : ε + abs (f (n1 + 1)) > 0,
  from add_pos_of_pos_of_nonneg Hε $ abs_nonneg _,
have H2 : ε + abs (g (n2 + 1)) > 0,
  from add_pos_of_pos_of_nonneg Hε $ abs_nonneg _,
let ⟨n3, h3⟩ := hf (ε/2 / (ε + abs (g (n2 + 1))))
  (div_pos (half_pos Hε) H2) in
let ⟨n4, h4⟩ := hg (ε/2 / (ε + abs (f (n1 + 1))))
  (div_pos (half_pos Hε) H1) in
⟨max (max n1 n2) (max n3 n4), λ m hm n hn,
have H3 : _ := h1 n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  (n1 + 1) (nat.lt_succ_self n1),
have H4 : _ := h2 m (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
  (n2 + 1) (nat.lt_succ_self n2),
have H5 : _ := h3 m (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hm)
  n (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
have H6 : _ := h4 m (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  n (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn),
calc  abs ((f m * g m) - (f n * g n))
    = abs ((f m - f n) * g m + f n * (g m - g n)) : by simp [add_mul, mul_add]
... ≤ abs ((f m - f n) * g m) + abs (f n * (g m - g n)) : abs_add _ _
... = abs (f m - f n) * abs (g m) + abs (f n) * abs (g m - g n) : by rw [abs_mul, abs_mul]
... = abs (f m - f n) * abs (g m - g (n2 + 1) + g (n2 + 1)) + abs (f n - f (n1 + 1) + f (n1 + 1)) * abs (g m - g n) : by simp
... ≤ abs (f m - f n) * (abs (g m - g (n2 + 1)) + abs (g (n2 + 1))) + (abs (f n - f (n1 + 1)) + abs (f (n1 + 1))) * abs (g m - g n) :
  add_le_add (mul_le_mul_of_nonneg_left (abs_add _ _) (abs_nonneg _)) (mul_le_mul_of_nonneg_right (abs_add _ _) (abs_nonneg _))
... ≤ abs (f m - f n) * (ε + abs (g (n2 + 1))) + (ε + abs (f (n1 + 1))) * abs (g m - g n) :
  add_le_add (mul_le_mul_of_nonneg_left (le_of_lt $ add_lt_add_right H4 _) (abs_nonneg _)) (mul_le_mul_of_nonneg_right (le_of_lt $ add_lt_add_right H3 _) (abs_nonneg _))
... < (ε/2 / (ε + abs (g (n2 + 1)))) * (ε + abs (g (n2 + 1))) + (ε + abs (f (n1 + 1))) * (ε/2 / (ε + abs (f (n1 + 1)))) :
  add_lt_add (mul_lt_mul_of_pos_right H5 H2) (mul_lt_mul_of_pos_left H6 H1)
... = ε/2 + ε/2 : by rw [div_mul_cancel _ (ne_of_gt H2), mul_div_cancel' _ (ne_of_gt H1)]
... = ε : add_halves _⟩

theorem neg_one : (-1 : ℕ → real) ∈ real.cau_seq :=
λ ε Hε, ⟨0, λ m hm n hn, show abs (-1 - (-1)) < ε, by simpa using Hε⟩

theorem real_mul : (λ n, r * f n) ∈ real.cau_seq := λ ε Hε,
classical.by_cases
  (assume H : r = 0, ⟨0, λ m hm n hn, by simpa [H] using Hε⟩)
  (assume H : r ≠ 0,
    let ⟨N, HN⟩ := hf (ε / abs r) (div_pos Hε $ abs_pos_iff.2 H) in
    ⟨N, λ m hm n hn,
    calc  abs (r * f m - r * f n)
        = abs (r * (f m - f n)) : congr_arg _ $ eq.symm $ mul_sub _ _ _
    ... = abs r * abs (f m - f n) : abs_mul _ _
    ... < abs r * (ε / abs r) : mul_lt_mul_of_pos_left (HN m hm n hn) $ abs_pos_iff.2 H
    ... = ε : mul_div_cancel' _ $ mt eq_zero_of_abs_eq_zero H⟩)

theorem neg : -f ∈ real.cau_seq :=
(neg_one_mul f) ▸ mul _ _ neg_one hf

theorem sub : f - g ∈ real.cau_seq :=
add _ _ hf (neg g hg)

theorem one : (1 : ℕ → real) ∈ real.cau_seq :=
(neg_neg (1 : ℕ → real)) ▸ neg _ neg_one

theorem shift (k : nat) : (λ n, f (n + k)) ∈ real.cau_seq := λ ε Hε,
let ⟨N, HN⟩ := hf ε Hε in
⟨N, λ m hm n hn, HN (m + k) (lt_of_lt_of_le hm $ nat.le_add_right m k)
  (n + k) (lt_of_lt_of_le hn $ nat.le_add_right n k)⟩

theorem of_increasing_of_bounded_above
  (H1 : ∃ N, ∀ n > N, f n ≤ f (n + 1))
  (H2 : ∃ L N, ∀ n > N, f n ≤ L) : f ∈ real.cau_seq :=
let ⟨N1, H3⟩ := H1 in
let ⟨L, N2, H4⟩ := H2 in
have H5 : ∀ m > N1, ∀ n, m ≤ n → f m ≤ f n,
  from λ m hm n H, @nat.less_than_or_equal.rec_on
    m (λ b, f m ≤ f b) n H (le_refl _) $ λ b H ih,
    le_trans ih $ H3 b $ lt_of_lt_of_le hm H,
subtype.property $ of_close f $
let S := { x | ∃ n > max N1 N2, f n = x } in
let M := sup S (f (max N1 N2 + 1)) L
  ⟨_, nat.lt_succ_self _, rfl⟩ $ λ x ⟨n, hn1, hn2⟩,
  hn2 ▸ H4 n $ lt_of_le_of_lt (le_max_right _ _) hn1 in
⟨M, λ ε Hε, let (⟨r, ⟨N3, HN3, HN4⟩, hr2⟩ : ∃ r ∈ S, M - (ε/2) ≤ r) :=
  ex_sup_sub_le _ _ _ _ _ (ε/2) (half_pos Hε) in
⟨N3, λ n hn,
have hn1 : f n ≤ M,
  from le_sup _ _ _ _ _ _ ⟨_, lt_trans HN3 hn, rfl⟩,
have hn2 : M - f n ≤ ε/2,
  from sub_le_of_sub_le $ le_trans hr2 $ HN4 ▸
    (H5 N3 (lt_of_le_of_lt (le_max_left _ _) HN3) n $ le_of_lt hn),
abs_sub_lt_iff.2 ⟨lt_of_le_of_lt (sub_nonpos_of_le hn1) Hε,
  lt_of_le_of_lt hn2 $ half_lt_self Hε⟩⟩⟩

theorem of_decreasing_of_bounded_below
  (H1 : ∃ N, ∀ n > N, f (n + 1) ≤ f n)
  (H2 : ∃ L N, ∀ n > N, L ≤ f n) : f ∈ real.cau_seq :=
let ⟨N1, H3⟩ := H1 in
let ⟨L, N2, H4⟩ := H2 in
neg_neg f ▸ (neg_eq_neg_one_mul (-f)).symm ▸
(mul _ _ neg_one $ of_increasing_of_bounded_above (-f)
  ⟨N1, λ n hn, neg_le_neg $ H3 n hn⟩
  ⟨-L, N2, λ n hn, neg_le_neg $ H4 n hn⟩)

theorem of_eventually_equal
  (H : ∃ N, ∀ n > N, f n = g n) : g ∈ real.cau_seq := λ ε Hε,
let ⟨N1, HN1⟩ := hf ε Hε in
let ⟨N2, HN2⟩ := H in
⟨max N1 N2, λ m hm n hn,
HN2 m (lt_of_le_of_lt (le_max_right N1 N2) hm) ▸
HN2 n (lt_of_le_of_lt (le_max_right N1 N2) hn) ▸
HN1 m (lt_of_le_of_lt (le_max_left N1 N2) hm)
    n (lt_of_le_of_lt (le_max_left N1 N2) hn)⟩

instance : comm_ring real.cau_seq :=
by refine
{ add := λ f g, ⟨f.1 + g.1, add _ _ f.2 g.2⟩,
  zero := ⟨0, have H : (-1 : ℕ → real) + (-1) * (-1) = 0, by simp,
    H ▸ add _ _ neg_one $ mul _ _ neg_one neg_one⟩,
  neg := λ f, ⟨-f.1, have H : (-1) * f.1 = -f.1, by simp,
    H ▸ mul _ _ neg_one f.2⟩,
  mul := λ f g, ⟨f.1 * g.1, mul _ _ f.2 g.2⟩,
  one := ⟨1, have H : (-1 : ℕ → real) * (-1) = 1, by simp,
    H ▸ mul _ _ neg_one neg_one⟩,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

instance : has_coe_to_fun real.cau_seq :=
⟨_, λ f, f.1⟩

instance : module real real.cau_seq :=
{ smul := λ r f, ⟨λ n, r * f n, real_mul r f.1 f.2⟩,
  smul_add := λ r x y, subtype.eq $ funext $ λ n, mul_add _ _ _,
  add_smul := λ r s x, subtype.eq $ funext $ λ n, add_mul _ _ _,
  mul_smul := λ r s x, subtype.eq $ funext $ λ n, mul_assoc _ _ _,
  one_smul := λ r, subtype.eq $ funext $ λ n, one_mul _ }

instance : has_coe real real.cau_seq :=
⟨λ r, ⟨λ n, r, λ ε Hε, ⟨0, λ m hm n hn, show abs (r - r) < ε,
from (sub_self r).symm ▸ (@abs_zero real _).symm ▸ Hε⟩⟩⟩

theorem coe_inj (x y : real) (H : (x : real.cau_seq) = y) : x = y :=
congr_fun (congr_arg subtype.val H) 0

-- which direction is more useful?
theorem smul_eq_coe_mul (r : real) (f : real.cau_seq) : r • f = r * f := rfl

theorem coe_zero : ((0 : real) : real.cau_seq) = 0 := rfl

theorem coe_one : ((1 : real) : real.cau_seq) = 1 := rfl

theorem coe_neg_one : ((-1 : real) : real.cau_seq) = -1 := rfl

theorem coe_add (x y : real) : ((x + y : real) : real.cau_seq) = x + y := rfl

theorem coe_neg (x : real) : ((-x : real) : real.cau_seq) = -x := rfl

theorem coe_sub (x y : real) : ((x - y : real) : real.cau_seq) = x - y := rfl

theorem coe_mul (x y : real) : ((x * y : real) : real.cau_seq) = x * y := rfl

end real.cau_seq

namespace real
/-
@[elab_as_eliminator] protected theorem induction_on {C : real → Prop} (r : real)
  (x : real) (H1 : C x)                                 -- nonempty
  (H2 : ∀ t, C t → ∃ ε > 0, ∀ x, abs (x - t) < ε → C x) -- open
  (H3 : ∀ f : cau_seq, (∀ n, C (f n)) → C (lim f)) :    -- closed
  C r :=
classical.by_contradiction $ assume H4 : ¬ C r,
let S := { ε | ∀ b, abs (x - b) < ε → C b } in
let M := sup S 0 (abs (x - r))
  (λ b hb, false.elim $ not_lt_of_ge (abs_nonneg _) hb)
  (λ ε Hε, le_of_not_gt $ λ H5, H4 $ Hε r H5) in
_
-/
def shift (f : real.cau_seq) (k : nat) : real.cau_seq :=
⟨_, cau_seq.shift f.1 f.2 k⟩

section calculus_of_limits

variables (r : real) (f g : cau_seq) (s : real)

theorem lim_add : lim (f + g) = lim f + lim g :=
(lim_def _ _).2 $ λ ε Hε,
let ⟨N1, HN1⟩ := lim_close f (ε/2) (half_pos Hε) in
let ⟨N2, HN2⟩ := lim_close g (ε/2) (half_pos Hε) in
⟨max N1 N2, λ n hn,
have H1 : abs (f n - lim f) < ε/2,
  from HN1 n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : abs (g n - lim g) < ε/2,
  from HN2 n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs ((f n + g n) - (lim f + lim g))
    = abs ((f n - lim f) + (g n - lim g))   : by simp
... ≤ abs (f n - lim f) + abs (g n - lim g) : abs_add _ _
... < ε/2 + ε/2                             : add_lt_add H1 H2
... = ε                                     : add_halves ε⟩

theorem lim_const : lim r = r :=
(lim_def _ _).2 $ λ ε Hε,
⟨0, λ n hn,
calc  abs (r - r)
    = abs 0 : congr_arg abs $ sub_self r
... = 0     : abs_zero
... < ε     : Hε⟩

theorem lim_const_mul : lim (r * f) = r * lim f :=
(lim_def _ _).2 $ λ ε Hε,
have H1 : abs r + 1 > 0,
  from add_pos_of_nonneg_of_pos (abs_nonneg r) zero_lt_one,
let ⟨N, HN⟩ := lim_close f (ε / (abs r + 1)) (div_pos Hε H1) in
⟨N, λ n hn,
calc  abs (r * f n - r * lim f)
    = abs r * abs (f n - lim f)       : by rw [← mul_sub, abs_mul]
... < (abs r + 1) * (ε / (abs r + 1)) : mul_lt_mul' (le_of_lt $ lt_add_one _) (HN n hn) (abs_nonneg _) H1
... = ε                               : mul_div_cancel' _ $ ne_of_gt H1⟩

theorem lim_mul_const : lim (f * s) = lim f * s :=
by simpa [mul_comm] using lim_const_mul s f

theorem lim_neg : lim (-f) = -lim f :=
calc  lim (-f)
    = lim ((-1) * f)        : congr_arg lim $ neg_eq_neg_one_mul f
... = lim ((-1 : real) * f) : rfl
... = (-1) * lim f          : lim_const_mul (-1) f
... = -lim f                : neg_one_mul (lim f)

theorem lim_sub : lim (f - g) = lim f - lim g :=
(lim_add f (-g)).trans (congr_arg _ $ lim_neg g)

theorem lim_mul_zero (Hf : lim f = 0) (Hg : lim g = 0) : lim (f * g) = 0 :=
(lim_def _ _).2 $ λ ε Hε,
let ⟨N1, HN1⟩ := (lim_def _ _).1 Hf ε Hε in
let ⟨N2, HN2⟩ := (lim_def _ _).1 Hg 1 zero_lt_one in
⟨max N1 N2, λ n hn,
have H1 : abs (f n) < ε,
  by simpa using HN1 n (lt_of_le_of_lt (le_max_left _ _) hn),
have H2 : abs (g n) < 1,
  by simpa using HN2 n (lt_of_le_of_lt (le_max_right _ _) hn),
calc  abs (f n * g n - 0)
    = abs (f n) * abs (g n) : by rw [sub_zero, abs_mul]
... < ε * 1 : mul_lt_mul' (le_of_lt H1) H2 (abs_nonneg (g n)) Hε
... = ε : mul_one ε⟩

theorem lim_mul : lim (f * g) = lim f * lim g :=
have Hf : lim (f - lim f) = 0, by rw [lim_sub, lim_const, sub_self],
have Hg : lim (g - lim g) = 0, by rw [lim_sub, lim_const, sub_self],
calc    lim (f * g)
    =   lim ((f - lim f + lim f) * (g - lim g + lim g))          : by simp
... =   lim (((f - lim f) * (g - lim g) + (f - lim f) * (lim g))
      + ((lim f) * (g - lim g) + (lim f) * (lim g)))             : by rw [add_mul, mul_add, mul_add]
... =   ((lim ((f - lim f) * (g - lim g)) + lim ((f - lim f) * (lim g)))
      + (lim ((lim f) * (g - lim g)) + lim ((lim f) * (lim g)))) : by rw [lim_add, lim_add, lim_add]
... =   lim f * lim g : by rw [lim_mul_zero _ _ Hf Hg, lim_mul_const, lim_const_mul, Hf, Hg, zero_mul,
                               mul_zero, ← cau_seq.coe_mul, lim_const, zero_add, zero_add, zero_add]

theorem lim_shift (k : nat) : lim (shift f k) = lim f :=
(lim_def _ _).2 $ λ ε Hε,
let ⟨N, HN⟩ := lim_close f ε Hε in
⟨N, λ n hn, HN (n + k) $ lt_of_lt_of_le hn $ nat.le_add_right n k⟩

theorem lim_le (H : ∃ N, ∀ n > N, f n ≤ g n) : lim f ≤ lim g :=
le_of_not_gt $ assume H1 : lim g < lim f,
have H2 : (lim f - lim g) / 2 > 0,
  from half_pos $ sub_pos_of_lt H1,
let ⟨N, HN⟩ := H in
let ⟨N1, HN1⟩ := lim_close f _ H2 in
let ⟨N2, HN2⟩ := lim_close g _ H2 in
not_lt_of_ge (HN (N+(N1+N2)+1) $ nat.succ_le_succ $ nat.le_add_right _ _) $
calc  g (N+(N1+N2)+1)
    = (g (N+(N1+N2)+1) - lim g) + (lim f - f (N+(N1+N2)+1)) + (lim g - lim f + f (N+(N1+N2)+1)) : by simp [add_assoc]
... < (lim f - lim g) / 2 + (lim f - lim g) / 2 + (lim g - lim f + f (N+(N1+N2)+1)) :
  add_lt_add_right (add_lt_add
    (abs_sub_lt_iff.1 $ HN2 _ $ nat.succ_le_succ $ le_trans (nat.le_add_left _ _) (nat.le_add_left _ _)).1
    (abs_sub_lt_iff.1 $ HN1 _ $ nat.succ_le_succ $ le_trans (nat.le_add_right _ _) (nat.le_add_left _ _)).2) _
... = f (N+(N1+N2)+1) : by simp

theorem squeeze.close (a b c : cau_seq) (L : real)
  (Ha : lim a = L) (Hc : lim c = L)
  (Hb : ∃ N, ∀ n > N, a n ≤ b n ∧ b n ≤ c n) :
  close b L := λ ε Hε,
let ⟨N1, HN1⟩ := (lim_def _ _).1 Ha ε Hε in
let ⟨N2, HN2⟩ := (lim_def _ _).1 Hc ε Hε in
let ⟨N, HN⟩ := Hb in
⟨max N (max N1 N2), λ n hn,
have H1 : b n - L < ε, from
calc  b n - L
    ≤ c n - L : sub_le_sub_right (HN _ $ lt_of_le_of_lt (le_max_left _ _) hn).2 _
... < ε : (abs_sub_lt_iff.1 $ HN2 n $ lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn).1,
have H2 : L - b n < ε, from
calc  L - b n
    ≤ L - a n : sub_le_sub_left (HN _ $ lt_of_le_of_lt (le_max_left _ _) hn).1 _
... < ε : (abs_sub_lt_iff.1 $ HN1 n $ lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn).2,
abs_sub_lt_iff.2 ⟨H1, H2⟩⟩

def squeeze.cau_seq (a b c : cau_seq) (L : real)
  (Ha : lim a = L) (Hc : lim c = L)
  (Hb : ∃ N, ∀ n > N, a n ≤ b n ∧ b n ≤ c n) : cau_seq :=
cau_seq.of_close b ⟨L, squeeze.close a b c L Ha Hc Hb⟩

theorem squeeze (a b c : cau_seq) (L : real)
  (Ha : lim a = L) (Hc : lim c = L)
  (Hb : ∃ N, ∀ n > N, a n ≤ b n ∧ b n ≤ c n) :
  lim (squeeze.cau_seq a b c L Ha Hc Hb) = L :=
lim.of_close _ _ $ squeeze.close a b c L Ha Hc Hb

end calculus_of_limits

end real

instance real.fun : comm_ring (real → real) :=
by refine
{ add := λ f g x, f x + g x,
  zero := λ x, 0,
  neg := λ f x, -f x,
  mul := λ f g x, f x * g x,
  one := λ x, 1,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

def real.cts_at (a : real) : set (real → real) :=
{ f | ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε }

namespace real.cts_at

variables (a : real) (f g : real → real) (Hf : f ∈ real.cts_at a) (Hg : g ∈ real.cts_at a)

theorem add : f + g ∈ real.cts_at a := λ ε Hε,
let ⟨δ1, Hδ1, Hδf⟩ := Hf (ε/2) (half_pos Hε) in
let ⟨δ2, Hδ2, Hδg⟩ := Hg (ε/2) (half_pos Hε) in
⟨min δ1 δ2, lt_min Hδ1 Hδ2, λ x hx,
have H1 : abs (f x - f a) < ε/2,
  from Hδf x (lt_min_iff.1 hx).1,
have H2 : abs (g x - g a) < ε/2,
  from Hδg x (lt_min_iff.1 hx).2,
calc  abs ((f x + g x) - (f a + g a))
    = abs ((f x - f a) + (g x - g a)) : by simp
... ≤ abs (f x - f a) + abs (g x - g a) : abs_add _ _
... < ε/2 + ε/2 : add_lt_add H1 H2
... = ε : add_halves ε⟩

theorem neg : -f ∈ real.cts_at a := λ ε Hε,
let ⟨δ, Hδ, Hδf⟩ := Hf ε Hε in
⟨δ, Hδ, λ x hx,
calc  abs (-f x - -f a)
    = abs (-(-f x - -f a)) : eq.symm $ abs_neg _
... = abs (f x - f a)      : congr_arg abs $ neg_neg_sub_neg _ _
... < ε                    : Hδf x hx⟩

theorem mul : f * g ∈ real.cts_at a := λ ε Hε,
let ε1 := ε/2/(abs (g a) + 1) in
have Hε1 : ε1 > 0, from div_pos (half_pos Hε)
  (add_pos_of_nonneg_of_pos (abs_nonneg (g a)) zero_lt_one),
let ε2 := ε/2/(ε1 + abs (f a)) in
have Hε2 : ε2 > 0, from div_pos (half_pos Hε)
  (add_pos_of_pos_of_nonneg Hε1 (abs_nonneg (f a))),
let ⟨δ1, Hδ1, Hδf⟩ := Hf ε1 Hε1 in
let ⟨δ2, Hδ2, Hδg⟩ := Hg ε2 Hε2 in
⟨min δ1 δ2, lt_min Hδ1 Hδ2, λ x hx,
have H1 : abs (f x - f a) < ε1,
  from Hδf x (lt_min_iff.1 hx).1,
have H2 : abs (g x - g a) < ε2,
  from Hδg x (lt_min_iff.1 hx).2,
calc  abs ((f x * g x) - (f a * g a))
    = abs (f x * (g x - g a) + (f x - f a) * g a) :
  by rw [mul_sub, sub_mul, ← add_sub_assoc, sub_add_cancel]
... ≤ abs (f x * (g x - g a)) + abs ((f x - f a) * g a) :
  abs_add _ _
... = abs (f x - f a + f a) * abs (g x - g a) + abs (f x - f a) * abs (g a) :
  by rw [abs_mul, abs_mul, sub_add_cancel]
... < (abs (f x - f a) + abs (f a)) * ε2 + ε1 * (abs (g a) + 1) :
  add_lt_add_of_le_of_lt
    (mul_le_mul (abs_add _ _) (le_of_lt H2) (abs_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_lt_mul' (le_of_lt H1) (lt_add_one _) (abs_nonneg _) Hε1)
... < (ε1 + abs (f a)) * ε2 + ε1 * (abs (g a) + 1) :
  add_lt_add_right (mul_lt_mul_of_pos_right
    (add_lt_add_right H1 _) Hε2) _
... = ε/2 + ε/2 :
  congr_arg₂ (+)
    (mul_div_cancel' _ $ ne_of_gt $ add_pos_of_pos_of_nonneg Hε1 $ abs_nonneg _)
    (div_mul_cancel _ $ ne_of_gt $ add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one)
... = ε : add_halves ε⟩

end real.cts_at

def real.cts : set (real → real) :=
{ f | ∀ a, f ∈ real.cts_at a }

namespace real.cts

variables (f g : real → real) (Hf : f ∈ real.cts) (Hg : g ∈ real.cts)

theorem add : f + g ∈ real.cts := λ a,
real.cts_at.add a f g (Hf a) (Hg a)

theorem mul : f * g ∈ real.cts := λ a,
real.cts_at.mul a f g (Hf a) (Hg a)

theorem neg_one : (-1 : real → real) ∈ real.cts := λ a ε Hε,
⟨1, zero_lt_one, λ x hx, show abs (-1 - -1) < ε,
from trans_rel_right _ (by simp) Hε⟩

theorem id : id ∈ real.cts := λ a ε Hε,
⟨ε, Hε, λ x, id⟩

instance : comm_ring real.cts :=
by refine
{ add := λ f g, ⟨f.1 + g.1, add _ _ f.2 g.2⟩,
  zero := ⟨0, have H : (-1 : real → real) + (-1) * (-1) = 0, by simp,
    H ▸ add _ _ neg_one $ mul _ _ neg_one neg_one⟩,
  neg := λ f, ⟨-f.1, have H : (-1) * f.1 = -f.1, by simp,
    H ▸ mul _ _ neg_one f.2⟩,
  mul := λ f g, ⟨f.1 * g.1, mul _ _ f.2 g.2⟩,
  one := ⟨1, have H : (-1 : real → real) * (-1) = 1, by simp,
    H ▸ mul _ _ neg_one neg_one⟩,
  .. };
{ intros,
  { simp [mul_assoc, mul_add, add_mul] }
  <|> simp [mul_comm] }

theorem pow (n : nat) : (λ x, x^n) ∈ real.cts :=
nat.rec_on n (1 : real.cts).2 $ λ n ih,
real.cts.mul _ _ id ih

end real.cts

section IVT

parameters (f : real → real) (hf : f ∈ real.cts) (a b c : real)
parameters (H1 : a < b) (H2 : f a < c) (H3 : c < f b)

noncomputable def real.cts_sol : real :=
sup { x | x < b ∧ f x < c } a b ⟨H1, H2⟩ $ λ x hx, le_of_lt hx.1

theorem real.cts_sol.lt : real.cts_sol < b :=
have H4 : real.cts_sol ≤ b := sup_le _ _ _ _ _ _ $ λ x hx, le_of_lt hx.1,
or.resolve_right H4 $ assume H5 : real.cts_sol = b,
let ⟨δ, Hδ1, Hδ2⟩ := hf b (f b - c) (sub_pos_of_lt H3) in
have H6 : real.cts_sol ≤ b - δ,
  from sup_le _ _ _ _ _ _ $ λ x ⟨hx1, hx2⟩, le_of_not_gt $ λ hx3,
  have H7 : abs (x - b) < δ,
    from abs_sub_lt_iff.2 ⟨lt_trans (sub_neg_of_lt hx1) Hδ1, sub_lt_of_sub_lt hx3⟩,
  have H8 : _ := (abs_sub_lt_iff.1 (Hδ2 x H7)).2,
  lt_asymm H8 $ sub_lt_sub_left hx2 _,
not_lt_of_ge H6 $ (trans_rel_left _ (sub_lt_self _ Hδ1) H5.symm)

theorem real.cts_sol.sol : f real.cts_sol = c :=
classical.by_contradiction $
assume H : f real.cts_sol ≠ c,
or.cases_on (lt_or_gt_of_ne H)
  (assume H4 : f real.cts_sol < c,
    let ⟨δ, Hδ1, Hδ2⟩ := hf real.cts_sol (c - f real.cts_sol) (sub_pos_of_lt H4) in
    let x := min (δ/2) ((b - real.cts_sol)/2) in
    have H5 : x > 0,
      from lt_min (half_pos Hδ1) (half_pos $ sub_pos_of_lt real.cts_sol.lt),
    have H6 : x < δ,
      from min_lt_iff.2 $ or.inl $ half_lt_self Hδ1,
    have H7 : real.cts_sol + x < b,
      from add_lt_of_lt_sub_left $ min_lt_iff.2 $ or.inr $
        half_lt_self $ sub_pos_of_lt real.cts_sol.lt,
    have H8 : _ := Hδ2 (real.cts_sol + x) $
      by simp; rw abs_of_pos H5; from H6,
    have H9 : real.cts_sol + x ≤ real.cts_sol,
      from le_sup _ _ _ _ _ _ ⟨H7,
        ((sub_lt_sub_iff_right _).1 (abs_sub_lt_iff.1 H8).1)⟩,
    not_lt_of_ge H9 $ lt_add_of_pos_right _ H5)
  (assume H4 : f real.cts_sol > c,
    let ⟨δ, Hδ1, Hδ2⟩ := hf real.cts_sol (f real.cts_sol - c) (sub_pos_of_lt H4) in
    have H5 : real.cts_sol ≤ real.cts_sol - δ,
      from sup_le _ _ _ _ _ _ $ λ r ⟨hr1, hr2⟩, le_of_not_gt $ λ H5,
        have H6 : r ≤ real.cts_sol,
          from le_sup _ _ _ _ _ _ ⟨hr1, hr2⟩,
        have H7 : r - real.cts_sol < δ,
          from lt_of_le_of_lt (sub_nonpos_of_le H6) Hδ1,
        have H8 : _ := Hδ2 r $ abs_sub_lt_iff.2 ⟨H7, sub_lt_of_sub_lt H5⟩,
        lt_asymm (abs_sub_lt_iff.1 H8).2 $ sub_lt_sub_left hr2 _,
    not_lt_of_ge H5 $ sub_lt_self _ Hδ1)

end IVT

-- TODO: make a computable version and prove equality
noncomputable def sqrt2 : real :=
real.cts_sol (λ x, x^2) 0 2 2 two_pos $
  trans_rel_right _ (mul_zero 0) two_pos

theorem sqrt2_pow : sqrt2 ^ 2 = 2 :=
real.cts_sol.sol (λ x, x^2) (real.cts.pow 2) 0 2 2 _ _ $
  trans_rel_left _ (lt_add_of_pos_right _ two_pos) (mul_two 2).symm

theorem sqrt2_mul_sqrt2 : sqrt2 * sqrt2 = 2 :=
(pow_two _).symm.trans sqrt2_pow

namespace real

theorem pow.cau_seq.nonneg (x : real) (Hx1 : 0 ≤ x) (Hx2 : x < 1) :
  (λ n, x ^ n) ∈ cau_seq :=
cau_seq.of_decreasing_of_bounded_below _
  ⟨0, λ n hn, trans_rel_left _ (mul_le_mul (le_of_lt Hx2)
    (le_refl _) (pow_nonneg Hx1 n) zero_le_one) (one_mul _)⟩
  ⟨0, 0, λ n hn, pow_nonneg Hx1 n⟩

def pow.nonneg (x : real) (Hx1 : 0 ≤ x) (Hx2 : x < 1) : cau_seq :=
⟨_, pow.cau_seq.nonneg x Hx1 Hx2⟩

theorem pow.lim.nonneg (x : real) (Hx1 : 0 ≤ x) (Hx2 : x < 1) :
  lim (pow.nonneg x Hx1 Hx2) = 0 :=
have H1 : _, from
  calc  x * lim (pow.nonneg x Hx1 Hx2)
      = lim (x * pow.nonneg x Hx1 Hx2)       : eq.symm $ lim_const_mul _ _
  ... = lim (shift (pow.nonneg x Hx1 Hx2) 1) : congr_arg lim $ subtype.eq rfl
  ... = lim (pow.nonneg x Hx1 Hx2)           : lim_shift _ 1,
have H2 : (x - 1) * lim (pow.nonneg x Hx1 Hx2) = 0,
  by rw [sub_mul, H1, one_mul, sub_self],
or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H2) $
assume H3 : x - 1 = 0, lt_irrefl (1:real) $
calc  1
    = x - (x - 1) : eq.symm $ sub_sub_cancel x 1
... = x - 0       : congr_arg _ H3
... = x           : sub_zero x
... < 1           : Hx2

def pow.cau_seq (x : real) (Hx : abs x < 1) : cau_seq :=
cau_seq.of_close (λ n, x^n) ⟨0, λ ε Hε,
let ⟨N, HN⟩ := (lim_def _ _).1 (pow.lim.nonneg
  (abs x) (abs_nonneg _) Hx) ε Hε in
⟨N, λ n hn,
calc  abs (x^n - 0)
    = abs ((abs x)^n -0) : by simp [pow_abs, abs_abs]
... < ε : HN n hn⟩⟩

theorem pow.lim (x : real) (Hx : abs x < 1) :
  lim (pow.cau_seq x Hx) = 0 :=
lim.of_close _ _ $ λ ε Hε,
let ⟨N, HN⟩ := (lim_def _ _).1 (pow.lim.nonneg
  (abs x) (abs_nonneg _) Hx) ε Hε in
⟨N, λ n hn,
calc  abs (x^n - 0)
    = abs ((abs x)^n -0) : by simp [pow_abs, abs_abs]
... < ε : HN n hn⟩

variables (f g : ℕ → real)

def partial_sum : ℕ → real
| 0     := 0
| (n+1) := partial_sum n + f n

theorem close_zero_of_sum_cau_seq
  (H : partial_sum f ∈ cau_seq) : close f 0 := λ ε Hε,
let ⟨N, HN⟩ := H ε Hε in ⟨N, λ n hn,
calc  abs (f n - 0)
    = abs (f n) : congr_arg abs $ sub_zero _
... = abs (partial_sum f (n+1) - partial_sum f n) :
  congr_arg abs $ eq.symm $ add_sub_cancel' _ _
... < ε : HN (n+1) (nat.lt_succ_of_lt hn) n hn⟩

theorem lim_zero_of_sum_cau_seq
  (H : partial_sum f ∈ cau_seq) :
  lim (cau_seq.of_close f ⟨0, close_zero_of_sum_cau_seq f H⟩) = 0 :=
lim.of_close _ _ _

theorem partial_sum_pow (x : real) (n : nat) (H : x ≠ 1) :
  partial_sum (λ n, x^n) n = (1 - x^n) / (1 - x) :=
have H1 : 1 + -x ≠ 0, from λ H2, H $ eq.symm $ eq_of_sub_eq_zero H2,
by induction n with n ih; simp [partial_sum];
simp [ih, add_div_eq_mul_add_div _ _ H1, mul_add, pow_succ']

def partial_sum_pow.cau_seq (x : real) (H : abs x < 1) : cau_seq :=
⟨partial_sum (λ n, x^n),
have H1 : x ≠ 1, from λ H1, by subst H1; simp at H; from lt_irrefl _ H,
have H2 : partial_sum (λ n, x^n) = ((1:real) - (λ n, x^n)) * (1 / (1 - x) : real),
  from funext $ λ n, (partial_sum_pow x n H1).trans $ div_eq_mul_one_div _ _,
H2.symm ▸ cau_seq.mul _ _ (cau_seq.sub _ _ cau_seq.one (pow.cau_seq x H).2)
  (((1 / (1 - x) : real) : cau_seq).2)⟩

theorem partial_sum_pow.lim (x : real) (H : abs x < 1) :
  lim (partial_sum_pow.cau_seq x H) = 1 / (1 - x) :=
have H1 : x ≠ 1, from λ H1, by subst H1; simp at H; from lt_irrefl _ H,
calc  lim (partial_sum_pow.cau_seq x H)
    = lim (((1 : real) - pow.cau_seq x H) * (1 / (1 - x) : real)) :
  congr_arg lim $ subtype.eq $ funext $ λ n,
    (partial_sum_pow x n H1).trans $ div_eq_mul_one_div _ _
... = 1 / (1 - x) : by rw [lim_mul, lim_sub, lim_const, lim_const, pow.lim, sub_zero, one_mul]

theorem partial_sum.add : partial_sum (f + g) = partial_sum f + partial_sum g :=
funext $ λ n,
show partial_sum (f + g) n = partial_sum f n + partial_sum g n,
from nat.rec_on n (zero_add _).symm $ λ n ih,
show partial_sum (f + g) n + (f n + g n) = (partial_sum f n + f n) + (partial_sum g n + g n),
by rw ih; ac_refl

theorem partial_sum.const_mul (r : real) (f : ℕ → real) : partial_sum (r * f) = r * partial_sum f :=
funext $ λ n,
show partial_sum (r * f) n = r * partial_sum f n,
from nat.rec_on n (mul_zero r).symm $ λ n ih,
show partial_sum (r * f) n + r * f n = r * (partial_sum f n + f n),
by rw [ih, mul_add]

theorem partial_sum.const (r : real) (n : nat) : partial_sum r n = n * r :=
nat.rec_on n (zero_mul r).symm $ λ n ih,
show partial_sum r n + r = (n + 1) * r,
by rw [ih, add_mul, one_mul]

theorem partial_sum.neg : partial_sum (-f) = -partial_sum f :=
calc  partial_sum (-f)
    = partial_sum ((-1) * f) : by rw [neg_eq_neg_one_mul]
... = partial_sum ((-1 : real) * f) : rfl
... = (-1) * partial_sum f : partial_sum.const_mul _ _
... = -partial_sum f : neg_one_mul _

theorem partial_sum.sub : partial_sum (f - g) = partial_sum f - partial_sum g :=
calc  partial_sum (f - g)
    = partial_sum f + partial_sum (-g) : partial_sum.add _ _
... = partial_sum f - partial_sum g    : congr_arg _ $ partial_sum.neg _

def partial_sum.cau_seq_of_nonneg_of_bounded
  (H1 : ∃ N, ∀ n > N, f n ≥ 0)
  (H2 : ∃ L N, ∀ n > N, partial_sum f n ≤ L) : cau_seq :=
⟨partial_sum f,
let ⟨N1, H3⟩ := H1 in
let ⟨L, N2, H4⟩ := H2 in
cau_seq.of_increasing_of_bounded_above _
  ⟨N1, λ n hn, le_add_of_nonneg_right $ H3 n hn⟩
  ⟨L, N2, λ n hn, H4 n hn⟩⟩

theorem partial_sum.nonneg_of_nonneg (f : ℕ → real)
  (Hf : partial_sum f ∈ cau_seq) (H : ∀ n, f n ≥ 0) :
  lim ⟨_, Hf⟩ ≥ 0 :=
(lim_const 0) ▸ lim_le _ _
⟨0, λ n hn, nat.rec_on n (le_refl _) $
λ n ih, add_nonneg ih $ H n⟩

end real
