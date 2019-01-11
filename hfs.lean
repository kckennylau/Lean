import data.fintype

universes u v

theorem nat.of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
(lt_or_eq_of_le H).imp nat.le_of_lt_succ id

@[elab_with_expected_type]
def nat.le_rec_on {C : ℕ → Sort u} (next : Π {n}, C n → C (n+1)) : Π {n m : ℕ}, n ≤ m → C n → C m
| n 0 H x := eq.rec_on (nat.eq_zero_of_le_zero H) x
| n (m+1) H x := or.by_cases (nat.of_le_succ H) (λ h : n ≤ m, next $ nat.le_rec_on h x) (λ h : n = m + 1, eq.rec_on h x)

theorem nat.le_rec_on_self {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) {n h} (x : C n) : (nat.le_rec_on next h x : C n) = x :=
by cases n; unfold nat.le_rec_on or.by_cases; rw [dif_neg n.not_succ_le_self, dif_pos rfl]

theorem nat.le_rec_on_succ {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) {n m h2} (h1) (x : C n) :
  (nat.le_rec_on next h2 x : C (m+1)) = next m (nat.le_rec_on next h1 x) :=
by conv { to_lhs, rw [nat.le_rec_on, or.by_cases, dif_pos h1] }

theorem nat.le_rec_on_succ' {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) {n h} (x : C n) :
  (nat.le_rec_on next h x : C (n+1)) = next n x :=
by rw [nat.le_rec_on_succ next (le_refl n), nat.le_rec_on_self]

theorem nat.le_rec_on_trans {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {hnk} (x : C n) :
  (nat.le_rec_on next hnk x : C k) = nat.le_rec_on next hmk (nat.le_rec_on next hnm x) :=
begin
  induction hmk with k hmk ih, { rw nat.le_rec_on_self },
  rw [nat.le_rec_on_succ _ (le_trans hnm hmk), ih, nat.le_rec_on_succ]
end

theorem nat.le_rec_on_injective {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.injective (next n))
  {n m} (hnm : n ≤ m) : function.injective (nat.le_rec_on next hnm) :=
begin
  induction hnm with m hnm ih, { intros x y H, rwa [nat.le_rec_on_self, nat.le_rec_on_self] at H },
  intros x y H, rw [nat.le_rec_on_succ _ hnm, nat.le_rec_on_succ _ hnm] at H, exact ih (Hnext _ H)
end

theorem nat.le_rec_on_surjective {C : ℕ → Sort u} (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.surjective (next n))
  {n m} (hnm : n ≤ m) : function.surjective (nat.le_rec_on next hnm) :=
begin
  induction hnm with m hnm ih, { intros x, use x, rw nat.le_rec_on_self },
  intros x, rcases Hnext _ x with ⟨w, rfl⟩, rcases ih w with ⟨x, rfl⟩, use x, rw nat.le_rec_on_succ
end

lemma to_Prop_inj : Π {a b : bool} (H : (a : Prop) ↔ (b : Prop)), a = b
| a tt H := H.2 rfl
| a ff H := bool.eq_ff_of_ne_tt $ λ h, absurd (H.1 h) dec_trivial

def von_Neumann : ℕ → Type
| 0     := empty
| (n+1) := von_Neumann n → bool

namespace von_Neumann

def fintype_and_decidable_eq : Π n, fintype (von_Neumann n) × decidable_eq (von_Neumann n)
| 0     := (empty.fintype, empty.decidable_eq)
| (n+1) := let ⟨i1, i2⟩ := fintype_and_decidable_eq n in (@pi.fintype _ _ i1 i2 _,
    λ f g, @decidable_of_iff _ (∀ i, f i = g i) ⟨funext, λ (H:f=g) i, congr_fun H i⟩ (@fintype.decidable_forall_fintype _ i1 _ _))

instance (n) : fintype (von_Neumann n) := (fintype_and_decidable_eq n).1
instance (n) : decidable_eq (von_Neumann n) := (fintype_and_decidable_eq n).2

instance (n) : has_mem (von_Neumann n) (von_Neumann (n+1)) := ⟨λ u f, f u⟩

@[extensionality] theorem ext {n} {f g : von_Neumann (n+1)} (H : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
funext $ λ s, to_Prop_inj (H s)

def next : Π {n}, von_Neumann n → von_Neumann (n+1)
| (n+1) f := λ t, ∃ u ∈ f, next u = t

theorem mem_next {n} (f s : von_Neumann (n+1)) : s ∈ next f ↔ ∃ u ∈ f, next u = s :=
bool.coe_to_bool _

theorem next_inj : ∀ n, function.injective (@next n)
| (n+1) f g H := funext $ λ s, to_Prop_inj
    ⟨λ hfs, have _ := congr_fun H (next s), let ⟨u, hug, hnus⟩ := (bool.to_bool_eq.1 this).1 ⟨s, hfs, rfl⟩ in next_inj n hnus ▸ hug,
    λ hgs, have _ := congr_fun H (next s), let ⟨u, huf, hnus⟩ := (bool.to_bool_eq.1 this).2 ⟨s, hgs, rfl⟩ in next_inj n hnus ▸ huf⟩

theorem next_mem_next {n} (f : von_Neumann (n+1)) (s) : next s ∈ next f ↔ s ∈ f :=
(mem_next _ _).trans ⟨λ ⟨u, huf, hus⟩, next_inj n hus ▸ huf, λ hsf, ⟨s, hsf, rfl⟩⟩

def Next {n m} (H : n ≤ m) : von_Neumann n → von_Neumann m :=
nat.le_rec_on (λ n, next) H

theorem Next_self {n h} (x : von_Neumann n) : Next h x = x := nat.le_rec_on_self _ _
theorem Next_succ {n m h2} (h1 : n ≤ m) (x) : Next h2 x = next (Next h1 x) := nat.le_rec_on_succ _ _ _
theorem Next_succ' {n h} (x : von_Neumann n) : Next h x = next x := nat.le_rec_on_succ' _ _
theorem Next_trans {n m k} (h1 : n ≤ m) (h2 : m ≤ k) {h3} (x) : Next h3 x = Next h2 (Next h1 x) := nat.le_rec_on_trans _ _ _ _
theorem Next_trans' {n m k} (h1 : n ≤ m) (h2 : m ≤ k) (x) : Next h2 (Next h1 x) = Next (le_trans h1 h2) x := (Next_trans _ _ _).symm

theorem Next_inj {n m} (H : n ≤ m) : function.injective (Next H) :=
by unfold Next; convert nat.le_rec_on_injective _ next_inj H; ext; refl

instance : setoid Σ n, von_Neumann n :=
{ r := λ S T, Next (le_max_left _ _) S.2 = Next (le_max_right _ _) T.2,
  iseqv := ⟨λ _, rfl, λ ⟨m,s⟩ ⟨n,t⟩ H, Next_inj (le_of_eq $ max_comm _ _) $ by rw [Next_trans', Next_trans', H],
    λ ⟨m,s⟩ ⟨n,t⟩ ⟨p,u⟩ h1 h2, have h3 : _ := congr_arg (Next $ le_max_left _ p) h1,
    have h4 : _ := congr_arg (Next $ max_le (le_trans (le_max_right m _) (le_max_left _ _)) (le_max_right _ _)) h2,
    Next_inj (max_le (le_trans (le_max_left _ n) (le_max_left _ _)) (le_max_right _ _)) $
    by rw [Next_trans', Next_trans'] at h3 h4 ⊢; exact h3.trans h4⟩ }

theorem Next_mem_Next {n m h1} {h2 : n+1 ≤ m+1} {s} {f : von_Neumann (n+1)} : Next h1 s ∈ Next h2 f ↔ s ∈ f :=
begin
  induction h1 with m hnm ih, { rw [Next_self, Next_self] },
  rw [Next_succ hnm, Next_succ (nat.succ_le_succ hnm), next_mem_next, ih]
end

theorem Next_mem_Next_symm {n m} (h1 : n ≤ m) {s} {f : von_Neumann (n+1)} : s ∈ f ↔ Next h1 s ∈ Next (nat.succ_le_succ h1) f :=
Next_mem_Next.symm

end von_Neumann

/-- Hereditarily finite sets. V[ω]. -/
def hfs : Type :=
quotient von_Neumann.setoid

namespace hfs

--def aux {n} (m) : n ≤ m → von_Neumann n → von_Neumann m := von_Neumann.Next
--theorem a {n m} (h : n ≤ m) {x} : von_Neumann.Next h x = aux m h x := rfl

instance : has_mem hfs hfs :=
⟨λ s f, quotient.lift_on₂ s f (λ s f, von_Neumann.Next (le_max_left _ f.1) s.2 ∈ von_Neumann.Next (nat.le_succ_of_le (le_max_right s.1 _)) f.2) $
λ s₁ f₁ s₂ f₂ hs hf, have hs' : _ := congr_arg (von_Neumann.Next (le_max_left _ (max f₁.1 f₂.1))) hs,
have hf' : _ := congr_arg (von_Neumann.Next (le_max_right (max s₁.1 s₂.1) _)) hf,
show (_ ∈ _) = (_ ∈ _), by rw [von_Neumann.Next_mem_Next_symm (max_le_max (le_max_left _ s₂.1) (le_max_left _ f₂.1)),
    von_Neumann.Next_mem_Next_symm (max_le_max (le_max_right s₁.1 s₂.1) (le_max_right f₁.1 f₂.1))];
rw [von_Neumann.Next_trans', von_Neumann.Next_trans'] at hs' hf'; iterate 4 { rw von_Neumann.Next_trans' };
rw [von_Neumann.Next_succ, von_Neumann.Next_succ, hf', hs']⟩

-- Extensionality
@[extensionality] theorem ext {f g : hfs} (H : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
quotient.induction_on₂ f g $ λ f g, quotient.sound $ show _ = _, begin
  generalize : von_Neumann.setoid._proof_1 f g = h1,
  generalize : von_Neumann.setoid._proof_2 f g = h2,
  revert h1 h2, generalize : max _ _ = n, cases n with n ih,
  { intros, change @eq empty _ _, exact subsingleton.elim _ _ },
  intros h1 h2, ext x,
  sorry
end

end hfs
