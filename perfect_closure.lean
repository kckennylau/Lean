import data.padics.padic_norm data.nat.binomial

universe u

theorem inv_pow' {α : Type u} [discrete_field α] {x : α} {n : ℕ} : (x⁻¹)^n = (x^n)⁻¹ :=
decidable.by_cases
  (assume H : x = 0, or.cases_on (nat.eq_zero_or_pos n)
    (λ hn, by rw [H, hn, pow_zero, pow_zero, inv_one])
    (λ hn, by rw [H, zero_pow hn, inv_zero, zero_pow hn]))
  (λ H, division_ring.inv_pow H n)

theorem pow_eq_zero {α : Type u} [domain α] {x : α} {n : ℕ} (H : x^n = 0) : x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

class char_p (α : Type u) [has_zero α] [has_one α] [has_add α] (p : ℕ) : Prop :=
(cast_eq_zero : (p:α) = 0)

theorem add_pow_char (α : Type u) [comm_ring α] {p : ℕ} (hp : nat.prime p)
  [char_p α p] (x y : α) : (x + y)^p = x^p + y^p :=
begin
  rw [add_pow, finset.sum_range_succ, nat.sub_self, pow_zero, choose_self],
  rw [nat.cast_one, mul_one, mul_one, add_left_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { intros b h1 h2,
      have := nat.prime.dvd_choose (nat.pos_of_ne_zero h2) (finset.mem_range.1 h1) hp,
      rw [← nat.div_mul_cancel this, nat.cast_mul, char_p.cast_eq_zero α p],
      simp only [mul_zero] },
    { intro H, exfalso, apply H, exact finset.mem_range.2 hp.pos } },
  rw [pow_zero, nat.sub_zero, one_mul, choose_zero_right, nat.cast_one, mul_one]
end

theorem nat.iterate₀ {α : Type u} {op : α → α} {x : α} (H : op x = x) {n : ℕ} :
  op^[n] x = x :=
by induction n; [simp only [nat.iterate_zero], simp only [nat.iterate_succ', H, *]]

theorem nat.iterate₁ {α : Type u} {op op' : α → α} (H : ∀ x, op (op' x) = op' (op x)) {n : ℕ} {x : α} :
  op^[n] (op' x) = op' (op^[n] x) :=
by induction n; [simp only [nat.iterate_zero], simp only [nat.iterate_succ', H, *]]

theorem nat.iterate₂ {α : Type u} {op : α → α} {op' : α → α → α} (H : ∀ x y, op (op' x y) = op' (op x) (op y)) {n : ℕ} {x y : α} :
  op^[n] (op' x y) = op' (op^[n] x) (op^[n] y) :=
by induction n; [simp only [nat.iterate_zero], simp only [nat.iterate_succ', H, *]]

theorem nat.iterate_inj {α : Type u} {op : α → α} (Hinj : function.injective op) (n : ℕ) (x y : α)
  (H : (op^[n] x) = (op^[n] y)) : x = y :=
by induction n with n ih; simp only [nat.iterate_zero, nat.iterate_succ'] at H;
[exact H, exact ih (Hinj H)]

def frobenius (α : Type u) [monoid α] (p : ℕ) (x : α) : α :=
x^p

theorem frobenius_def (α : Type u) [monoid α] (p : ℕ) (x : α) : frobenius α p x = x ^ p := rfl

theorem frobenius_mul (α : Type u) [comm_monoid α] (p : ℕ) (x y : α) :
  frobenius α p (x * y) = frobenius α p x * frobenius α p y := mul_pow x y p
theorem frobenius_one (α : Type u) [monoid α] (p : ℕ) :
  frobenius α p 1 = 1 := one_pow _

instance {α : Type u} [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : is_ring_hom (frobenius α p) :=
{ map_one := frobenius_one α p,
  map_mul := frobenius_mul α p,
  map_add := add_pow_char α hp }

section
variables (α : Type u) [comm_ring α] (p : ℕ) [hp : nat.prime p]
theorem frobenius_zero : frobenius α p 0 = 0 := zero_pow hp.pos
variables [char_p α p] (x y : α)
include hp
theorem frobenius_add : frobenius α p (x + y) = frobenius α p x + frobenius α p y := is_ring_hom.map_add _
theorem frobenius_neg : frobenius α p (-x) = -frobenius α p x := is_ring_hom.map_neg _
theorem frobenius_sub : frobenius α p (x - y) = frobenius α p x - frobenius α p y := is_ring_hom.map_sub _
end

theorem frobenius_inj (α : Type u) [integral_domain α] (p : ℕ) [nat.prime p] [char_p α p] (x y : α)
  (H : frobenius α p x = frobenius α p y) : x = y :=
by rw ← sub_eq_zero at H ⊢; rw ← frobenius_sub at H; exact pow_eq_zero H

inductive perfect_closure.r (α : Type u) [monoid α] (p : ℕ) : (ℕ × α) → (ℕ × α) → Prop
| intro : ∀ n x, perfect_closure.r (n, x) (n+1, frobenius α p x)
run_cmd tactic.mk_iff_of_inductive_prop `perfect_closure.r `perfect_closure.r_iff

def perfect_closure (α : Type u) [monoid α] (p : ℕ) : Type u :=
quot (perfect_closure.r α p)

namespace perfect_closure

variables (α : Type u)

--set_option profiler true

private lemma mul_aux_left [comm_monoid α] (p : ℕ) (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) * ((frobenius α p)^[x1.1] y.2)) =
  quot.mk (r α p) (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) * ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul, nat.succ_add]; apply r.intro
end

private lemma mul_aux_right [comm_monoid α] (p : ℕ) (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) * ((frobenius α p)^[x.1] y1.2)) =
  quot.mk (r α p) (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) * ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul]; apply r.intro
end

instance [comm_monoid α] (p : ℕ) : has_mul (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) * ((frobenius α p)^[x.1] y.2))) (mul_aux_right α p x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
mul_aux_left α p x1 x2 y H)⟩

instance [comm_monoid α] (p : ℕ) : comm_monoid (perfect_closure α p) :=
{ mul_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, mul_assoc, nat.iterate₂ (frobenius_mul _ _),
      (nat.iterate_add _ _ _ _).symm, add_comm, add_left_comm],
  one := quot.mk _ (0, 1),
  one_mul := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate_zero, one_mul, zero_add]),
  mul_one := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate_zero, mul_one, add_zero]),
  mul_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm, mul_comm])),
  .. (infer_instance : has_mul (perfect_closure α p)) }

private lemma add_aux_left [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) + ((frobenius α p)^[x1.1] y.2)) =
  quot.mk (r α p) (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) + ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add, nat.succ_add]; apply r.intro
end

private lemma add_aux_right [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) + ((frobenius α p)^[x.1] y1.2)) =
  quot.mk (r α p) (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) + ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add]; apply r.intro
end

instance [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : has_add (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) + ((frobenius α p)^[x.1] y.2))) (add_aux_right α p hp x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
add_aux_left α p hp x1 x2 y H)⟩

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : has_neg (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.mk (r α p) (x.1, -x.2)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro _ n x := quot.sound $ by rw ← frobenius_neg; apply r.intro
end)⟩

theorem mk_zero [comm_ring α] (p : ℕ) [nat.prime p] (n : ℕ) : quot.mk (r α p) (n, 0) = quot.mk (r α p) (0, 0) :=
by induction n with n ih; [refl, rw ← ih]; symmetry; apply quot.sound;
have := r.intro p n (0:α); rwa [frobenius_zero α p] at this

theorem r.sound [monoid α] (p m n : ℕ) (x y : α) (H : frobenius α p^[m] x = y) :
  quot.mk (r α p) (n, x) = quot.mk (r α p) (m + n, y) :=
by subst H; induction m with m ih; [simp only [zero_add, nat.iterate_zero],
  rw [ih, nat.succ_add, nat.iterate_succ']]; apply quot.sound; apply r.intro

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : comm_ring (perfect_closure α p) :=
{ add_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_comm, add_left_comm],
  zero := quot.mk _ (0, 0),
  zero_add := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, zero_add]),
  add_zero := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, add_zero]),
  add_left_neg := λ e, quot.induction_on e (λ ⟨n, x⟩, show quot.mk _ _ = _,
    by simp only [nat.iterate₁ (frobenius_neg α p), add_left_neg, mk_zero]; refl),
  add_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm])),
  left_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm, add_left_comm]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul α p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, mul_add, add_comm, add_left_comm],
  right_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm _ s, add_left_comm _ s]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul α p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_mul, add_comm, add_left_comm],
  .. (infer_instance : has_add (perfect_closure α p)),
  .. (infer_instance : has_neg (perfect_closure α p)),
  .. (infer_instance : comm_monoid (perfect_closure α p)) }

instance [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] : has_inv (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.mk (r α p) (x.1, x.2⁻¹)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro _ n x := quot.sound $ by simp only [frobenius]; rw [← inv_pow']; apply r.intro
end)⟩

theorem eq_iff [integral_domain α] (p : ℕ) [nat.prime p] [char_p α p]
  (x y : ℕ × α) : quot.mk (r α p) x = quot.mk (r α p) y ↔ 
    (frobenius α p^[y.1] x.2) = (frobenius α p^[x.1] y.2) :=
begin
  split,
  { intro H,
    replace H := quot.exact _ H,
    induction H,
    case eqv_gen.rel : x y H
    { cases H with n x, refl },
    case eqv_gen.refl : H
    { refl },
    case eqv_gen.symm : x y H ih
    { exact ih.symm },
    case eqv_gen.trans : x y z H1 H2 ih1 ih2
    { apply nat.iterate_inj (frobenius_inj α p) y.1,
      dsimp only,
      rw [← nat.iterate_add, add_comm, nat.iterate_add, ih1],
      rw [← nat.iterate_add, add_comm, nat.iterate_add, ih2],
      rw [← nat.iterate_add, ← nat.iterate_add, add_comm] } },
  intro H,
  cases x with m x,
  cases y with n y,
  change (frobenius α p^[n] x) = (frobenius α p^[m] y) at H,
  rw [r.sound α p m n y _ rfl, r.sound α p n m x _ rfl, add_comm, H]
end

instance [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] : discrete_field (perfect_closure α p) :=
{ zero_ne_one := λ H, zero_ne_one ((eq_iff _ _ _ _).1 H),
  mul_inv_cancel := λ e, quot.induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate₀ (frobenius_zero α p),
        nat.iterate_zero, (nat.iterate₂ (frobenius_mul α p)).symm] at this ⊢;
        rw [mul_inv_cancel this, nat.iterate₀ (frobenius_one _ _)]),
  inv_mul_cancel := λ e, quot.induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate₀ (frobenius_zero α p),
        nat.iterate_zero, (nat.iterate₂ (frobenius_mul α p)).symm] at this ⊢;
        rw [inv_mul_cancel this, nat.iterate₀ (frobenius_one _ _)]),
  has_decidable_eq := λ e f, quot.rec_on_subsingleton e $ λ ⟨m, x⟩,
    quot.rec_on_subsingleton f $ λ ⟨n, y⟩,
    decidable_of_iff' _ (eq_iff α p _ _),
  inv_zero := congr_arg (quot.mk (r α p)) (by rw [inv_zero]),
  .. (infer_instance : has_inv (perfect_closure α p)),
  .. (infer_instance : comm_ring (perfect_closure α p)) }

end perfect_closure
