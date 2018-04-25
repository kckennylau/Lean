import algebra.ring order.lattice data.pnat data.rat

universes u v

theorem congr_arg₂ {α β γ : Type*} (f : α → β → γ) {x₁ x₂ : α} {y₁ y₂ : β}
  (Hx : x₁ = x₂) (Hy : y₁ = y₂) : f x₁ y₁ = f x₂ y₂ :=
eq.drec (eq.drec rfl Hy) Hx

open lattice

def is_add_group_hom {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) : Prop :=
@is_group_hom (multiplicative α) (multiplicative β) _ _ f

attribute [class] is_add_group_hom

namespace is_add_group_hom

variables {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) [hf : is_add_group_hom f]

theorem mk (H : ∀ x y, f (x + y) = f x + f y) : is_add_group_hom f :=
⟨H⟩

theorem add (x y) : f (x + y) = f x + f y :=
@is_group_hom.mul (multiplicative α) (multiplicative β) _ _ f hf x y

theorem zero : f 0 = 0 :=
@is_group_hom.one (multiplicative α) (multiplicative β) _ _ f hf

theorem neg (x) : f (-x) = -f x :=
@is_group_hom.inv (multiplicative α) (multiplicative β) _ _ f hf x

end is_add_group_hom

instance is_ring_hom.to_is_add_group_hom {α : Type*} {β : Type*} [ring α] [ring β]
  (f : α → β) [is_ring_hom f] : is_add_group_hom f :=
⟨λ _ _, is_ring_hom.map_add f⟩

class directed_order (α : Type u) extends has_sup α, partial_order α :=
(le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
(le_sup_right : ∀ a b : α, b ≤ a ⊔ b)

theorem le_sup_left {α : Type u} [directed_order α] {x y : α} : x ≤ x ⊔ y :=
directed_order.le_sup_left x y

theorem le_sup_right {α : Type u} [directed_order α] {x y : α} : y ≤ x ⊔ y :=
directed_order.le_sup_right x y

variables {ι : out_param (Type u)} [inhabited ι] [directed_order ι]
variables {G : ι → Type v}

class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

def direct_limit.setoid (f : Π i j, i ≤ j → G i → G j)
  [directed_system f] : setoid (sigma G) :=
⟨λ i j, ∃ k (hik : i.1 ≤ k) (hjk : j.1 ≤ k), f i.1 k hik i.2 = f j.1 k hjk j.2,
 λ i, ⟨i.1, le_refl i.1, le_refl i.1, rfl⟩,
 λ i j ⟨k, hik, hjk, H⟩, ⟨k, hjk, hik, H.symm⟩,
 λ i j k ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩,
   ⟨ij ⊔ jk, le_trans hiij le_sup_left, le_trans hkjk le_sup_right,
    calc  f i.1 (ij ⊔ jk) _ i.2
        = f ij (ij ⊔ jk) _ (f i.1 ij _ i.2) : eq.symm $ directed_system.Hcomp f _ _ _ _ _ _
    ... = f ij (ij ⊔ jk) _ (f j.1 ij _ j.2) : congr_arg _ hij
    ... = f j.1 (ij ⊔ jk) _ j.2 : directed_system.Hcomp f _ _ _ _ _ _
    ... = f jk (ij ⊔ jk) _ (f j.1 jk _ j.2) : eq.symm $ directed_system.Hcomp f _ _ _ _ _ _
    ... = f jk (ij ⊔ jk) _ (f k.1 jk _ k.2) : congr_arg _ hjk
    ... = f k.1 (ij ⊔ jk) _ k.2 : directed_system.Hcomp f _ _ _ _ _ _⟩⟩

local attribute [instance] direct_limit.setoid

def direct_limit (f : Π i j, i ≤ j → G i → G j)
  [directed_system f] : Type (max u v) :=
quotient (direct_limit.setoid f)

namespace direct_limit

variables (f : Π i j, i ≤ j → G i → G j) [directed_system f]

def of (i x) : direct_limit f :=
⟦⟨i, x⟩⟧

theorem of_f {i j hij x} : (of f j (f i j hij x)) = of f i x :=
quotient.sound ⟨j, le_refl j, hij, directed_system.Hcomp f _ _ _ _ _ _⟩

variables {P : Type*} (g : Π i, G i → P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

def rec (x : direct_limit f) : P :=
quotient.lift_on x (λ i, g i.1 i.2) $
λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩,
calc  g p xp
    = g t (f p t hpt xp) : eq.symm $ Hg p t hpt xp
... = g t (f q t hqt xq) : congr_arg _ hpqt
... = g q xq : Hg q t hqt xq

lemma rec_of {i} (x) : rec f g Hg (of f i x) = g i x := rfl

end direct_limit

namespace directed_system

variables [∀ i, add_comm_group (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_add_group_hom (f i j h)] [directed_system f]

theorem map_add {i j k m xi xj hik hjk hkm} :
  f k m hkm (f i k hik xi + f j k hjk xj) = f i m (le_trans hik hkm) xi + f j m (le_trans hjk hkm) xj :=
(is_add_group_hom.add _ _ _).trans $
congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)

theorem add {i j hij x y} : f i j hij (x + y) = f i j hij x + f i j hij y :=
is_add_group_hom.add _ _ _

theorem zero {i j hij} : f i j hij 0 = 0 :=
is_add_group_hom.zero _

theorem neg {i j hij x} : f i j hij (-x) = -f i j hij x :=
is_add_group_hom.neg _ _

end directed_system

namespace directed_system

variables [∀ i, ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

theorem map_mul {i j k m xi xj hik hjk hkm} :
  f k m hkm (f i k hik xi * f j k hjk xj) = f i m (le_trans hik hkm) xi * f j m (le_trans hjk hkm) xj :=
(is_ring_hom.map_mul _).trans $
congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)

theorem mul {i j hij x y} : f i j hij (x * y) = f i j hij x * f i j hij y :=
is_ring_hom.map_mul _

theorem one {i j hij} : f i j hij 1 = 1 :=
is_ring_hom.map_one _

end directed_system

namespace direct_limit

variables [∀ i, add_comm_group (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_add_group_hom (f i j h)] [directed_system f]

local attribute [instance] direct_limit.setoid

instance add_comm_group' : add_comm_group (quotient (direct_limit.setoid f)) :=
{ add := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 +
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨(p ⊔ q) ⊔ (r ⊔ s) ⊔ (t ⊔ u),
       le_trans le_sup_left le_sup_left,
       le_trans le_sup_right le_sup_left,
       calc   f (p ⊔ q) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_left le_sup_left)
                (f p (p ⊔ q) le_sup_left xp + f q (p ⊔ q) le_sup_right xq)
          =   f p (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hpt (le_trans le_sup_left le_sup_right)) xp
            + f q (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hqu (le_trans le_sup_right le_sup_right)) xq :
        directed_system.map_add f
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f p t hpt xp)
            + f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f q u hqu xq) :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f r t hrt xr)
            + f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f s u hsu xs) :
        congr_arg₂ (+) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   f r (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xr
            + f s (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xs :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f (r ⊔ s) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_right le_sup_left)
                (f r (r ⊔ s) le_sup_left xr + f s (r ⊔ s) le_sup_right xs) :
        eq.symm $ directed_system.map_add f⟩),
  add_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨((p ⊔ q) ⊔ r) ⊔ (p ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.add f, directed_system.Hcomp f, -add_comm]⟩,
  zero := ⟦⟨default _, 0⟩⟧,
  zero_add := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.zero f, directed_system.Hcomp f]⟩,
  add_zero := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left,
     by dsimp; simp [directed_system.map_add f, directed_system.zero f, directed_system.Hcomp f]⟩,
  neg := λ i, quotient.lift_on i (λ p, ⟦⟨p.1, -p.2⟩⟧ : sigma G → quotient (direct_limit.setoid f)) $
    λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩, quotient.sound $
    ⟨t, hpt, hqt, by dsimp at hpqt ⊢; simp [directed_system.neg f, hpqt]⟩,
  add_left_neg := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound $
    ⟨(p ⊔ p) ⊔ default ι, le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.neg f, directed_system.zero f]⟩,
  add_comm := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩, quotient.sound
    ⟨(p ⊔ q) ⊔ (q ⊔ p), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f]⟩ }

instance : add_comm_group (direct_limit f) :=
direct_limit.add_comm_group' f

instance of.is_add_group_hom {i} : is_add_group_hom (direct_limit.of f i) :=
is_add_group_hom.mk _ $ λ x y, quotient.sound
⟨i ⊔ i, le_sup_left, le_refl _,
 by dsimp; simp [directed_system.map_add f]; simp [directed_system.add f]⟩

theorem of.zero_exact {i x} (H : of f i x = 0) :
  ∃ p hp1, f i p hp1 x = (0 : G p) :=
let ⟨p, hp1, hp2, hp3⟩ := quotient.exact H in
⟨p, hp1, hp3.trans $ is_add_group_hom.zero _⟩

variables {P : Type*} [add_comm_group P]
variables (g : Π i, G i → P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variables [∀ i, is_add_group_hom (g i)]

def rec.is_add_group_hom : is_add_group_hom (rec f g Hg) :=
is_add_group_hom.mk _ $ λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩,
calc  _ = _ : is_add_group_hom.add _ _ _
    ... = _ : congr_arg₂ (+) (Hg _ _ _ _) (Hg _ _ _ _)

end direct_limit

namespace direct_limit

variables [∀ i, ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

local attribute [instance] direct_limit.setoid

instance ring' : ring (quotient (direct_limit.setoid f)) :=
{ mul := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 *
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨(p ⊔ q) ⊔ (r ⊔ s) ⊔ (t ⊔ u),
       le_trans le_sup_left le_sup_left,
       le_trans le_sup_right le_sup_left,
       calc   f (p ⊔ q) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_left le_sup_left)
                (f p (p ⊔ q) le_sup_left xp * f q (p ⊔ q) le_sup_right xq)
          =   f p (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hpt (le_trans le_sup_left le_sup_right)) xp
            * f q (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hqu (le_trans le_sup_right le_sup_right)) xq :
        directed_system.map_mul f
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f p t hpt xp)
            * f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f q u hqu xq) :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f r t hrt xr)
            * f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f s u hsu xs) :
        congr_arg₂ (*) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   f r (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xr
            * f s (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xs :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f (r ⊔ s) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_right le_sup_left)
                (f r (r ⊔ s) le_sup_left xr * f s (r ⊔ s) le_sup_right xs) :
        eq.symm $ directed_system.map_mul f⟩),
  mul_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨((p ⊔ q) ⊔ r) ⊔ (p ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_mul f, directed_system.mul f, directed_system.Hcomp f, mul_assoc]⟩,
  one := ⟦⟨default _, 1⟩⟧,
  one_mul := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right,
     by dsimp; simp [directed_system.map_mul f, directed_system.one f, directed_system.Hcomp f]⟩,
  mul_one := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left,
     by dsimp; simp [directed_system.map_mul f, directed_system.one f, directed_system.Hcomp f]⟩,
  left_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.add f, directed_system.mul f, directed_system.Hcomp f, mul_add]⟩,
  right_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.add f, directed_system.mul f, directed_system.Hcomp f, add_mul]⟩,
  .. direct_limit.add_comm_group' f }

instance: ring (direct_limit f) :=
direct_limit.ring' f

instance of.is_ring_hom {i} : is_ring_hom (direct_limit.of f i) :=
{ map_add := is_add_group_hom.add _,
  map_mul := λ x y, quotient.sound ⟨i ⊔ i, le_sup_left, le_refl _,
    by dsimp; simp [directed_system.mul f, directed_system.Hcomp f]⟩,
  map_one := quotient.sound ⟨i ⊔ default _, le_sup_left, le_sup_right,
    by dsimp; simp [directed_system.one f]⟩ }

theorem of.one_exact {i x} (H : of f i x = 1) :
  ∃ p hp1, f i p hp1 x = (1 : G p) :=
let ⟨p, hp1, hp2, hp3⟩ := quotient.exact H in
⟨p, hp1, hp3.trans $ is_ring_hom.map_one _⟩

variables {P : Type*} [ring P]
variables (g : Π i, G i → P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variables [∀ i, is_ring_hom (g i)]

local attribute [instance] rec.is_add_group_hom

def rec.is_ring_hom : is_ring_hom (rec f g Hg) :=
{ map_add := is_add_group_hom.add _,
  map_mul := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩,
    calc  _ = _ : is_ring_hom.map_mul _
        ... = _ : congr_arg₂ (*) (Hg _ _ _ _) (Hg _ _ _ _),
  map_one := show g (default _) 1 = 1, from is_ring_hom.map_one _ }

end direct_limit


namespace test

instance : has_dvd ℕ+ :=
⟨λ m n, m.1 ∣ n.1⟩

instance : directed_order pnat :=
{ le := λ m n, m ∣ n,
  le_refl := λ _, ⟨1, by simp⟩,
  le_trans := λ _ _ _ ⟨k1, hk1⟩ ⟨k2, hk2⟩, ⟨k1 * k2, by rw [hk2, hk1, mul_assoc]⟩,
  le_antisymm := λ _ _ h1 h2, pnat.eq $ nat.dvd_antisymm h1 h2,
  sup := (*),
  le_sup_left := λ _ n, ⟨n, rfl⟩,
  le_sup_right := λ m _, ⟨m, nat.mul_comm _ _⟩ }

def ff : Π i j : pnat, i ≤ j → ℤ → ℤ :=
λ i j h n, n * (j / i : nat)

instance : inhabited pnat := ⟨1⟩

instance ds : directed_system ff :=
⟨λ ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨p, hp⟩ ⟨q, hq⟩ n, by unfold ff; clear _fun_match; dsimp at hp hq ⊢;
 rw [mul_assoc, hq, nat.mul_div_cancel_left _ hj, hp, nat.mul_div_cancel_left _ hi];
 rw [mul_assoc, nat.mul_div_cancel_left _ hi]; refl⟩

instance agh (i j h) : is_add_group_hom (ff i j h) :=
is_add_group_hom.mk _ $ λ x y, by unfold ff; rw add_mul

theorem pnat.div_mul_div {p q t u : ℕ+} (H1 : p ∣ t) (H2 : q ∣ u) : ↑t * ↑u / (↑p * ↑q) = (t / p : nat) * (u / q : nat) :=
begin
  cases p with p hp, cases q with q hq, cases t with t ht, cases u with u hu,
  dsimp at *,
  rw [← nat.div_div_eq_div_mul, nat.mul_comm, nat.mul_div_assoc _ H1],
  rw [nat.mul_comm, nat.mul_div_assoc _ H2]
end

theorem pnat.dvd_mul {p q t u : ℕ+} (H1 : p ∣ t) (H2 : q ∣ u) : (p * q) ∣ (t * u) :=
begin
  cases H1 with m hm, cases H2 with n hn,
  existsi m * n,
  change (t : ℕ) = p * m at hm,
  change (u : ℕ) = q * n at hn,
  change (t : ℕ) * u = p * q * _,
  rw [hm, hn],
  ac_refl
end

instance : comm_ring (direct_limit ff) :=
{ mul := λ i j, quotient.lift_on₂ i j
    (λ p q, (⟦⟨p.1 * q.1, p.2 * q.2⟩⟧ : direct_limit ff)) $
    λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound
    ⟨t * u, pnat.dvd_mul hpt hqu, pnat.dvd_mul hrt hsu, begin
      repeat { clear _x _fun_match }, dsimp [ff] at *,
      rw [pnat.div_mul_div hpt hqu, pnat.div_mul_div hrt hsu],
      simp [int.coe_nat_mul], cc
    end⟩,
  mul_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p * q * r, le_refl _, by simp [mul_assoc], by simp [mul_assoc]⟩,
  one := ⟦⟨1, 1⟩⟧,
  one_mul := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p, by simp, by simp, by simp⟩,
  mul_one := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p, by simp, by simp, by simp⟩,
  left_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨_, le_sup_left, le_sup_right, begin
      repeat { clear _x _fun_match },
      simp [mul_add],
      rw [directed_system.map_add ff],
      dsimp [ff, (⊔)] at *,
      rw [nat.mul_div_cancel_left, nat.mul_div_cancel_left, nat.mul_div_cancel],
      rw [nat.mul_div_assoc, nat.mul_div_cancel_left],
      rw [nat.mul_div_assoc, nat.mul_div_cancel],
      simp [add_mul, int.coe_nat_mul], cc,
      repeat { apply mul_pos <|> simp }
    end⟩,
  right_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨_, le_sup_left, le_sup_right, begin
      repeat { clear _x _fun_match },
      dsimp at *,
      rw [directed_system.map_add ff, add_mul],
      dsimp [ff, (⊔)] at *,
      rw [nat.mul_div_cancel_left, nat.mul_div_cancel_left, nat.mul_div_cancel],
      rw [nat.mul_div_assoc, nat.mul_div_cancel_left],
      rw [nat.mul_div_assoc, nat.mul_div_cancel],
      simp [add_mul, int.coe_nat_mul], cc,
      repeat { apply mul_pos <|> simp }
    end⟩,
  mul_comm := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩, quotient.sound
    ⟨p * q, by simp, by simp [mul_comm], by simp [mul_comm]⟩,
  .. direct_limit.add_comm_group ff }

theorem rat.mk_pnat_eq_iff (a b c d) : rat.mk_pnat a b = rat.mk_pnat c d ↔ a * d = c * b :=
begin
  cases b with b hb, cases d with d hd,
  simp [rat.mk_pnat_eq],
  rw [rat.mk_eq],
  exact ne_of_gt (int.coe_nat_pos.2 hb),
  exact ne_of_gt (int.coe_nat_pos.2 hd),
end

theorem pnat.eq_of_mul_of_mul {a b : ℕ} (c : ℕ+) (H : a * c = b * c) : a = b :=
begin
  rcases nat.lt_trichotomy a b with H1 | H1 | H1,
  { replace H1 := nat.mul_lt_mul_of_pos_right H1 c.2,
    exfalso,
    exact ne_of_lt H1 H },
  { exact H1 },
  { replace H1 := nat.mul_lt_mul_of_pos_right H1 c.2,
    exfalso,
    exact ne_of_lt H1 H.symm }
end

theorem nat.eq_of_mul_of_mul_of_pos {a b : ℕ} (c : ℕ) (Hc : c > 0) (H : a * c = b * c) : a = b :=
pnat.eq_of_mul_of_mul ⟨c, Hc⟩ H

theorem nat.pos_and_pos_of_mul_pos {a b : ℕ} (H : a * b > 0) : a > 0 ∧ b > 0 :=
⟨nat.pos_of_ne_zero $ λ Ha, by subst Ha; simp at H; cases H,
 nat.pos_of_ne_zero $ λ Hb, by subst Hb; simp at H; cases H⟩

theorem nat.div_self_div {a b : ℕ} (Ha : a > 0) (H : b ∣ a) : a / (a / b) = b :=
let ⟨n, hn⟩ := H in
have H1 : b * n > 0, from hn ▸ Ha,
let ⟨Hb, Hn⟩ := nat.pos_and_pos_of_mul_pos H1 in
by rw [hn, nat.mul_div_cancel_left _ Hb, nat.mul_div_cancel _ Hn]

def to_rat (x : direct_limit ff) : ℚ :=
quotient.lift_on x (λ i, (rat.mk_pnat i.2 i.1 : ℚ)) $
λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩, begin
  cases hpt with m hm, cases hqt with n hn,
  change (t : ℕ) = p * m at hm,
  change (t : ℕ) = q * n at hn,
  dsimp [ff] at hpqt, dsimp,
  rw rat.mk_pnat_eq_iff,
  rw [hm, nat.mul_div_cancel_left, ← hm, hn, nat.mul_div_cancel_left] at hpqt,
  have H : (m:ℤ) * n ≠ 0,
  { intro H,
    rcases eq_zero_or_eq_zero_of_mul_eq_zero H; simp at h,
    { subst h, simp at hm, exact hm },
    { subst h, simp at hn, exact hn } },
  apply eq_of_mul_eq_mul_right H,
  rw [← mul_assoc, ← mul_assoc, mul_assoc xq, mul_right_comm, mul_assoc xp],
  simp,
  rw [← int.coe_nat_mul, ← int.coe_nat_mul, ← hm, ← hn],
  rw [mul_right_comm xp, mul_right_comm xq, hpqt],
  simp, simp
end

def of_rat (x : ℚ) : direct_limit ff :=
⟦⟨⟨x.denom, x.pos⟩, x.num⟩⟧

def equiv : direct_limit ff ≃ ℚ :=
{ to_fun := to_rat,
  inv_fun := of_rat,
  left_inv := λ x, quotient.induction_on x $ λ ⟨⟨p, hp⟩, xp⟩, quotient.sound
    ⟨⟨p, hp⟩, ⟨nat.gcd (int.nat_abs xp) p,
        by simp [to_rat, rat.mk_pnat, nat.div_mul_cancel (nat.gcd_dvd_right _ _)]⟩,
    le_refl _, begin
      dsimp [ff, to_rat], dsimp at xp,
      simp [nat.div_self hp, rat.mk_pnat],
      rw [nat.div_self_div hp (nat.gcd_dvd_right _ _)],
      rw [mul_comm, ← int.mul_div_assoc, int.mul_div_cancel_left],
      { simp, apply nat.pos_iff_ne_zero.1,
        exact nat.gcd_pos_of_pos_right _ hp },
      { rw [← int.dvd_nat_abs, int.coe_nat_dvd],
        apply nat.gcd_dvd_left }
    end⟩,
  right_inv := λ x, rat.num_denom_cases_on x $ λ n d p c,
    (rat.mk_pnat_eq _ _ _).trans $ eq.symm $ rat.num_denom _ }

end test
