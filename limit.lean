import data.set.basic

universes u v

variable (ι : Type u)
variable (Obj : ι → Type v)
variable (Mor : Π x y, set (Obj x → Obj y))
variable (Hid : ∀ x, id ∈ Mor x x)
variable (Hcomp : ∀ (x y z) (f : Mor x y) (g : Mor y z), g.1 ∘ f.1 ∈ Mor x z)

def limit : Type (max u v) :=
{ p : Π x, Obj x // ∀ (x y) (f : Obj x → Obj y) (H : f ∈ Mor x y), f (p x) = p y }

def limit.to_Obj (x : ι) : limit ι Obj Mor → Obj x :=
λ p, p.1 x

theorem limit.commute (x y : ι) (f : Obj x → Obj y) (H : f ∈ Mor x y) (p : limit ι Obj Mor) : f (p.1 x) = p.1 y :=
p.2 x y f H

variable (T : Type (max u v))
variable (T_to : Π x, T → Obj x)
variable (HT : ∀ (x y) (f : Obj x → Obj y) (H : f ∈ Mor x y) (z : T), f (T_to x z) = T_to y z)

def limit.from_T : T → limit ι Obj Mor :=
λ z, ⟨λ x, T_to x z, λ x y f H, HT x y f H z⟩

theorem limit.from_T.commute (x : ι) (z : T) : limit.to_Obj ι Obj Mor x (limit.from_T ι Obj Mor T T_to HT z) = T_to x z :=
rfl

variable (g : T → limit ι Obj Mor)
variable (Hg : ∀ x z, limit.to_Obj ι Obj Mor x (g z) = T_to x z)

theorem limit.from_T.unique (z : T) : limit.from_T ι Obj Mor T T_to HT z = g z :=
subtype.eq $ funext $ λ x, show T_to x z = (g z).val x, from Hg x z ▸ rfl
