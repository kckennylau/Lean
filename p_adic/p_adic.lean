import data.nat.prime tactic.norm_num

structure Z_p (p : ℕ) (hp : nat.prime p) :=
(f : ℕ → fin p)

namespace Z_p

variables (p : ℕ) (hp : nat.prime p)

variables {p}

theorem nat.prime.gt_zero : p > 0 := lt_of_lt_of_le (by norm_num : 0 < 2) (nat.prime.ge_two hp)

variables (p)

def pre_add_aux (n : ℕ) : fin p × bool := (⟨n % p, nat.mod_lt _ (nat.prime.gt_zero hp)⟩, n ≥ p)

variables (p hp)

def pre_add (f g : ℕ → fin p) : ℕ → (fin p × bool)
| 0            := pre_add_aux p hp ((f 0).val + (g 0).val)
| (nat.succ n) := pre_add_aux p hp ((f (n+1)).val + (g (n+1)).val + (if (pre_add n).2 then 1 else 0))

def add (f g : ℕ → fin p) : ℕ → fin p := prod.fst ∘ pre_add p hp f g

instance : has_add (Z_p p hp) := ⟨λ m n, ⟨hp, add p hp m.f n.f⟩⟩

def zero : Z_p p hp := ⟨hp, λ n, ⟨0, nat.prime.gt_zero hp⟩⟩

instance : has_zero (Z_p p hp) := ⟨zero p hp⟩

def pre_neg_aux (n : ℕ) : fin p × bool := (if h : n = 0 then (⟨0, nat.prime.gt_zero hp⟩, ff) else (⟨p-n, nat.sub_lt_self (nat.prime.gt_zero hp) (nat.pos_of_ne_zero h)⟩, tt))

def pre_neg (f : ℕ → fin p) : ℕ → (fin p × bool)
| 0            := pre_neg_aux p hp (f 0).val
| (nat.succ n) := (if (pre_neg n).2 then (⟨p - nat.succ ((f (n+1)).val), nat.sub_lt_self (nat.prime.gt_zero hp) (nat.zero_lt_succ _)⟩, tt) else pre_neg_aux p hp (f (n+1)).val)

def neg (f : ℕ → fin p) : ℕ → fin p := prod.fst ∘ pre_neg p hp f

instance : has_neg (Z_p p hp) := ⟨λ n, ⟨hp, neg p hp n.f⟩⟩

protected theorem ext : Π (m n : Z_p p hp), (∀ i, m.f i = n.f i) → m = n
| ⟨hpf, f⟩ ⟨hpg, g⟩ h := begin congr, exact funext h end

theorem zero_add (m : Z_p p hp) : m + 0 = m :=
begin
  apply Z_p.ext,
  intro i,
  unfold has_add.add,
  unfold add,
  have h : pre_add p hp m.f (0 : Z_p p hp).f i = (m.f i, ff),
    unfold has_zero.zero,
    unfold zero,
    induction i with i ih,
    unfold pre_add,
    unfold pre_add_aux,
    dsimp,
    rw nat.add_zero,
    cases m.f 0,
    congr,
    dsimp,
    exact nat.mod_eq_of_lt is_lt,
    dsimp,
    unfold to_bool,
    apply if_neg,
    exact not_le_of_lt is_lt,
    unfold pre_add at *,
    unfold pre_add_aux at *,
    dsimp at *,
    rw ih,
    dsimp,
    rw if_neg,
    rw nat.add_zero,
    rw nat.add_zero,
    cases m.f (i+1),
    congr,
    dsimp,
    exact nat.mod_eq_of_lt is_lt,
    dsimp,
    unfold to_bool,
    apply if_neg,
    exact not_le_of_lt is_lt,
    trivial,
    dsimp,
    unfold function.comp,
    rw h
end

end Z_p
