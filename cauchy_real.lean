import data.rat linear_algebra.quotient_module ring_theory.ideals

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

def abs : rat.cau_seq :=
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

theorem mul_pos (Hf : lt 0 f) (Hg : lt 0 g) : lt 0 (f * g) :=
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
