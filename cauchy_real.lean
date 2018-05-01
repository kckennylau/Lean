import data.rat

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

instance : has_coe ℚ real :=
⟨λ q, ⟦⟨λ n, q, λ ε Hε, ⟨0, λ m hm n hn, show abs (q - q) < ε,
from (sub_self q).symm ▸ (@abs_zero ℚ _).symm ▸ Hε⟩⟩⟧⟩

theorem real.rat_eq_of_coe_eq {x y : ℚ} (H : (x : real) = y) : x = y :=
by_contradiction $ λ H1,
have H2 : x - y ≠ 0, from mt eq_of_sub_eq_zero H1,
have H3 : _ := quotient.exact H (abs (x - y) / 2) (half_pos $ abs_pos_iff.2 H2),
let ⟨N, HN⟩ := H3 in
have H4 : _ := HN (N + 1) (nat.lt_succ_self N),
lt_asymm H4 $ half_lt_self $ abs_pos_iff.2 H2

theorem real.rat_lt_of_coe_lt {x y : ℚ} (H : (x : real) < y) : x < y :=
let ⟨ε, Hε, N, HN⟩ := H in
calc  x
    < x + ε : lt_add_of_pos_right _ Hε
... < y     : HN (N + 1) (nat.lt_succ_self N)

theorem real.ex_rat_lt (x : real) : ∃ q : ℚ, (q : real) < x :=
quotient.induction_on x $ λ f,
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨f.1 (N + 1) - 2, 1, zero_lt_one, N, λ n hn,
calc  f.1 (N + 1) - 2 + 1
    = f.1 (N + 1) - (2 - 1) : sub_add _ _ _
... = f.1 (N + 1) - 1 : congr_arg _ $ add_sub_cancel _ _
... = f.1 (N + 1) - f.1 n + f.1 n - 1 : by rw sub_add_cancel
... < 1 + f.1 n - 1 : sub_lt_sub_right
  (add_lt_add_right (abs_lt.1 $ HN _ (nat.lt_succ_self N) _ hn).2 _) _
... = f.1 n : add_sub_cancel' _ _⟩

theorem real.ex_lt_rat (x : real) : ∃ q : ℚ, x < (q : real) :=
quotient.induction_on x $ λ f,
let ⟨N, HN⟩ := f.2 1 zero_lt_one in
⟨f.1 (N + 1) + 2, 1, zero_lt_one, N, λ n hn,
calc  f.1 n + 1
    = f.1 n - f.1 (N + 1) + f.1 (N + 1) + 1 : by rw sub_add_cancel
... < 1 + f.1 (N + 1) + 1 : add_lt_add_right
  (add_lt_add_right (abs_lt.1 $ HN _ hn _ (nat.lt_succ_self N)).2 _) _
... = f.1 (N + 1) + 2 : by rw [add_comm (1:ℚ), add_assoc]; refl⟩

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
le_of_not_gt $ λ ⟨ε, Hε, N, HN⟩, lt_asymm
  (HN (n+N+1) (nat.succ_le_succ $ nat.le_add_left _ _))
  (lt_of_le_of_lt
    (bin_div.snd_le n (n+N+1) (nat.le_add_right n (N+1)))
    (lt_add_of_pos_right _ Hε))

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
let ⟨ε3, Hε3, N3, HN3⟩ := bin_div.lt_snd _ hf (N1+N2+1) in
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
not_lt_of_ge (le_trans hr2 $ hf r hr1) $ ⟨ε/2, half_pos Hε, N2, λ n hn,
have H2 : _ := HN2 n hn (N1+N2+1) (nat.succ_le_succ $ nat.le_add_left _ _),
calc  f.1 n + ε/2
    = f.1 (N1+N2+1) + (f.1 n - f.1 (N1+N2+1)) + ε/2 : by rw add_sub_cancel'_right
... < f.1 (N1+N2+1) + ε/2 + ε/2 : add_lt_add_right (add_lt_add_left (abs_lt.1 $ H2).2 _) _
... = f.1 (N1+N2+1) + (ε/2 + ε/2) : add_assoc _ _ _
... = f.1 (N1+N2+1) + ε : by rw add_halves
... < (bin_div (N1+N2+1)).1 : H1⟩)

end completeness
