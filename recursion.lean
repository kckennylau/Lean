/-
f = ( nat n ↦ ( n<3 ? n : ( even(n) ? f(n−2)+f(n−3) : f(n−1)+f(n+1) ) ) )
where even = ( nat n ↦ exists m in nat ( m*2=n ) )
-/

def even : nat → Prop :=
λ n, ∃ m, m * 2 = n

def odd : nat → Prop :=
λ n, ∃ m, nat.succ (m * 2) = n

theorem even_xor_odd (n : nat) : xor (even n) (odd n) :=
begin
  induction n with n ih,
  { left,
    split,
    { existsi 0,
      refl },
    { intro h,
      cases h with n h,
      exact nat.no_confusion h, } },
  { cases ih; cases ih with ih1 ih2,
    { right,
      split,
      { cases ih1 with m hm,
        existsi m,
        rw hm },
      { intro h,
        cases h with m hm,
        cases m with m,
        { exact nat.no_confusion hm },
        { rw [nat.mul_succ, nat.add_succ, nat.add_comm, nat.mul_one, nat.add_succ] at hm,
          apply ih2,
          existsi m,
          rw [nat.mul_succ, nat.mul_one],
          exact nat.succ_inj hm } } },
    { left,
      split,
      { cases ih1 with m hm,
        cases m with m,
        { existsi 1,
          rw ← hm,
          refl },
        { existsi m + 2,
          rw [← hm],
          simp [add_mul, nat.succ_mul, nat.succ_eq_add_one],
          rw [← add_assoc, ← add_assoc, ← add_assoc] } },
      { intro ih,
        cases ih with m ih,
        apply ih2,
        existsi m,
        exact nat.succ_inj ih } } }
end

theorem odd_of_not_even (n : nat) : ¬ even n → odd n :=
λ h, or.cases_on (even_xor_odd n) (λ h1, false.elim $ h h1.1) and.left

theorem not_even_of_odd (n : nat) : odd n → ¬ even n :=
λ h1 h2, or.cases_on (even_xor_odd n) (λ h3, h3.2 h1) (λ h3, h3.2 h2)

theorem even_of_even_add_two : ∀ n, even (n+2) → even n
| 0 _               := ⟨0, rfl⟩
| n ⟨0, hm⟩          := false.elim $ nat.no_confusion hm
| n ⟨nat.succ m, hm⟩ := ⟨m, by simp [nat.succ_eq_add_one, add_mul] at hm;
    rw add_comm at hm;
    exact nat.add_right_cancel hm⟩

theorem not_even_of_even_succ : ∀ n, even (n+1) → ¬even n
| n ⟨0, hm⟩          := nat.no_confusion hm
| n ⟨nat.succ m, hm⟩ := not_even_of_odd _ ⟨m, by rw [← nat.succ_inj hm, add_comm, nat.mul_succ, add_comm]; refl⟩

theorem even_of_not_even_succ : ∀ n, ¬ even (n+1) → even n
| 0 _       := ⟨0, rfl⟩
| (nat.succ n) hm := let ⟨m, hm⟩ := odd_of_not_even _ hm in ⟨m, nat.succ_inj hm⟩

theorem even_succ_of_not_even : ∀ n, ¬ even n → even (n+1) :=
λ n h, let ⟨m, hm⟩ := odd_of_not_even _ h in ⟨m+1, hm ▸ by rw [add_mul]; refl⟩

instance : decidable_pred even :=
begin
  intro n,
  induction n with n ih,
  { right,
    existsi 0,
    refl },
  { cases ih,
    { right,
      cases even_xor_odd n with h h,
      { exfalso,
        exact ih h.1 },
      { cases h.1 with m hm,
        cases m with m,
        { existsi 1,
          rw ← hm,
          refl },
        { existsi m + 2,
          rw [← hm],
          simp [add_mul, nat.succ_mul, nat.succ_eq_add_one],
          rw [← add_assoc, ← add_assoc, ← add_assoc] } } },
    { left,
      intro h1,
      cases even_xor_odd (nat.succ n) with h h,
      { apply h.2,
        cases ih with p hp,
        existsi p,
        rw hp },
      { exact h.2 h1 } } }
end

def aux : nat → nat
| n := if n < 3 then n else
if even n then n - 1 else n + 1

instance aux2 : has_well_founded ℕ :=
{ r := inv_image (<) aux,
  wf := inv_image.wf aux nat.lt_wf }

theorem nat.le_of_not_gt {n m : nat} : ¬ m > n → m ≤ n :=
begin
  intro h,
  cases nat.lt_trichotomy m n with h1 h1,
  { exact nat.le_of_lt h1 },
  cases h1 with h1 h1,
  { rw h1 },
  { exfalso,
    exact h h1 }
end

theorem aux3 (n : nat) (H1 : ¬n < 3) (H2 : even n) : aux (n - 2) < aux n :=
begin
  have H3 := nat.le_of_not_gt H1,
  rw [aux, aux, if_neg H1, if_pos H2],
  let m := n - 3,
  have H4 : n = m + 3,
  { dsimp [m], rw [nat.sub_add_cancel H3] },
  rw H4 at *,
  simp,
  by_cases m + 1 < 3,
  { simp [h],
    apply add_lt_add_left,
    constructor },
  { simp [h, even_of_even_add_two _ H2],
    apply nat.lt_add_of_pos_right,
    constructor,
    constructor }
end

theorem aux4 (n : nat) (H1 : ¬n < 3) (H2 : even n) : aux (n - 3) < aux n :=
begin
  have H3 := nat.le_of_not_gt H1,
  simp [aux, H1, H2],
  let m := n - 3,
  have H4 : n = m + 3,
  { dsimp [m], rw [nat.sub_add_cancel H3] },
  rw H4 at *,
  simp,
  by_cases m < 3,
  { simp [h],
    apply nat.lt_add_of_pos_right,
    constructor,
    constructor },
  { simp [h],
    simp [not_even_of_even_succ _ (even_of_even_add_two _ H2)],
    apply nat.add_lt_add_left,
    constructor }
end

theorem aux5 (n : nat) (H1 : ¬n < 3) (H2 : ¬even n) : aux (n - 1) < aux n :=
begin
  have H3 := nat.le_of_not_gt H1,
  simp [aux, H1, H2],
  let m := n - 3,
  have H4 : n = m + 3,
  { dsimp [m], rw [nat.sub_add_cancel H3] },
  rw H4 at *,
  simp,
  by_cases m + 2 < 3,
  { simp [h],
    apply nat.add_lt_add_left,
    constructor,
    constructor },
  { simp [h],
    simp [even_of_not_even_succ _ H2],
    apply nat.add_lt_add_left,
    constructor,
    constructor,
    constructor }
end

theorem aux6 (n : nat) (H1 : ¬n < 3) (H2 : ¬even n) : aux (n + 1) < aux n :=
begin
  have H3 := nat.le_of_not_gt H1,
  simp [aux, H1, H2],
  let m := n - 3,
  have H4 : n = m + 3,
  { dsimp [m], rw [nat.sub_add_cancel H3] },
  rw H4 at *,
  simp,
  by_cases m + 4 < 3,
  { exfalso,
    cases h with h h,
    cases h with h h,
    cases h with h h,
    cases h with h h },
  { simp [h],
    simp [even_succ_of_not_even _ H2],
    apply add_lt_add_left,
    constructor }
end

def f : nat → nat
| n := if H1 : n < 3 then n else
if H2 : even n then
  f (n - 2) + f (n - 3)
else
  f (n - 1) + f (n + 1)
using_well_founded
{ dec_tac := `[exact aux3 n H1 H2 <|> exact aux4 n H1 H2 <|>
    exact aux5 n H1 H2 <|> exact aux6 n H1 H2],
  rel_tac := λ _ _, `[exact aux2] }
