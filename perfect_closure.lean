import data.padics.padic_norm data.nat.binomial

example (a b c : fin 2) : a = b ∨ b = c ∨ c = a :=
(dec_trivial : ∀ a b c, a = b ∨ b = c ∨ c = a) a b c

universe u

class char_p (α : Type u) [has_zero α] [has_one α] [has_add α] (p : ℕ) : Prop :=
(cast_eq_zero : (p:α) = 0)

theorem add_pow_char (α : Type u) [comm_ring α] {p : ℕ} (hp : nat.prime p)
  [char_p α p] (x y : α) : (x + y)^p = x^p + y^p :=
begin
  rw [add_pow, finset.sum_range_succ, nat.sub_self, pow_zero, choose_self],
  rw [nat.cast_one, mul_one, mul_one, add_left_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { sorry },
    { intro H, exfalso, apply H, exact finset.mem_range.2 hp.pos } },
  rw [pow_zero, nat.sub_zero, one_mul, choose_zero_right, nat.cast_one, mul_one]
end

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
#check nat.iterate_add
section
variables (α : Type u) [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] (x y : α)
theorem frobenius_add : frobenius α p (x + y) = frobenius α p x + frobenius α p y := is_ring_hom.map_add _
theorem frobenius_zero : frobenius α p 0 = 0 := is_ring_hom.map_zero _
theorem frobenius_neg : frobenius α p (-x) = -frobenius α p x := is_ring_hom.map_neg _
theorem frobenius_sub : frobenius α p (x - y) = frobenius α p x - frobenius α p y := is_ring_hom.map_sub _
end

inductive perfect_closure.r (α : Type u) [monoid α] (p : ℕ) : (ℕ × α) → (ℕ × α) → Prop
| intro : ∀ n x, perfect_closure.r (n, x) (n+1, x^p)
run_cmd tactic.mk_iff_of_inductive_prop `perfect_closure.r `perfect_closure.r_iff

def perfect_closure (α : Type u) [monoid α] (p : ℕ) : Type u :=
quot (perfect_closure.r α p)

namespace perfect_closure

variables (α : Type u)

set_option profiler true

private lemma mul_aux_left [comm_monoid α] (p : ℕ) (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, x1.2 ^ p ^ y.1 * y.2 ^ p ^ x1.1) =
  quot.mk (r α p) (x2.1 + y.1, x2.2 ^ p ^ y.1 * y.2 ^ p ^ x2.1) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by dsimp only; rw [← pow_mul, nat.mul_comm, pow_mul];
    rw [nat.pow_succ, pow_mul, ← mul_pow, nat.succ_add]; apply perfect_closure.r.intro
end

private lemma mul_aux_right [comm_monoid α] (p : ℕ) (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, x.2 ^ p ^ y1.1 * y1.2 ^ p ^ x.1) =
  quot.mk (r α p) (x.1 + y2.1, x.2 ^ p ^ y2.1 * y2.2 ^ p ^ x.1) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← pow_mul, nat.mul_comm, pow_mul];
    rw [nat.pow_succ, pow_mul, ← mul_pow]; apply perfect_closure.r.intro
end

instance [comm_monoid α] (p : ℕ) : has_mul (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, x.2^p^y.1 * y.2^p^x.1)) (mul_aux_right α p x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
mul_aux_left α p x1 x2 y H)⟩

instance [comm_monoid α] (p : ℕ) : comm_monoid (perfect_closure α p) :=
{ mul_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩,
    quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨r, z⟩,
    congr_arg (quot.mk _) $
    by simp only [add_assoc, mul_pow, nat.pow_add,
      (pow_mul _ _ _).symm, nat.mul_comm, mul_assoc],
  one := quot.mk _ (0, 1),
  one_mul := λ e, quot.induction_on e (λ ⟨n, x⟩,
    congr_arg (quot.mk _) $
    by simp only [nat.zero_add, one_pow, nat.pow_zero, one_mul, pow_one]),
  mul_one := λ e, quot.induction_on e (λ ⟨n, x⟩,
    congr_arg (quot.mk _) $
    by simp only [nat.add_zero, one_pow, nat.pow_zero, mul_one, pow_one]),
  mul_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩,
    quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $
    by simp only [add_comm, mul_comm])),
  .. (infer_instance : has_mul (perfect_closure α p)) }

private lemma add_aux_left [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, x1.2 ^ p ^ y.1 + y.2 ^ p ^ x1.1) =
  quot.mk (r α p) (x2.1 + y.1, x2.2 ^ p ^ y.1 + y.2 ^ p ^ x2.1) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by rw [← pow_mul, nat.mul_comm, pow_mul];
    rw [nat.pow_succ, pow_mul, ← add_pow_char α hp, nat.succ_add]; apply perfect_closure.r.intro
end

private lemma add_aux_right [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, x.2 ^ p ^ y1.1 + y1.2 ^ p ^ x.1) =
  quot.mk (r α p) (x.1 + y2.1, x.2 ^ p ^ y2.1 + y2.2 ^ p ^ x.1) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← pow_mul, nat.mul_comm, pow_mul];
    rw [nat.pow_succ, pow_mul, ← add_pow_char α hp]; apply perfect_closure.r.intro
end

instance [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : has_add (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, x.2^p^y.1 + y.2^p^x.1)) (add_aux_right α p hp x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
add_aux_left α p hp x1 x2 y H)⟩

instance [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : comm_ring (perfect_closure α p) :=
{ zero := quot.mk _ (0, 0),
  .. (infer_instance : has_add (perfect_closure α p)),
  .. (infer_instance : comm_monoid (perfect_closure α p)) }

end perfect_closure
