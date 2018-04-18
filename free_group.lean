/- 
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group algebra.group_power
import data.equiv data.list.basic data.quot
import group_theory.subgroup

universes u v w

variables {α : Type u}

namespace list

theorem prefix_or_prefix_of_append_eq_append {L1 L2 L3 L4 : list α}
  (H : L1 ++ L2 = L3 ++ L4) : L1 <+: L3 ∨ L3 <+: L1 :=
@prefix_or_prefix_of_prefix _ L1 _ (L3 ++ L4)
  (H ▸ prefix_append _ _) (prefix_append _ _)

theorem cons_eq_of_eq {x} {L₁ L₂ : list α} (H : L₁ = L₂) : x :: L₁ = x :: L₂ :=
congr_arg _ H

end list

instance is_group_hom.id [group α] : is_group_hom (@id α) :=
⟨λ _ _, rfl⟩

namespace free_group

inductive red : list (α × bool) → list (α × bool) → Prop
| refl {L} : red L L
| trans_bnot {L₁ L₂ L₃ x b} : red L₁ (L₂ ++ (x, b) :: (x, bnot b) :: L₃) → red L₁ (L₂ ++ L₃)

attribute [refl] red.refl

variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

theorem red.bnot {x b} : red (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂) :=
red.trans_bnot red.refl

theorem red.cons_bnot {x b} : red ((x, b) :: (x, bnot b) :: L) L :=
@red.bnot _ [] _ _ _

theorem red.length (H : red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n :=
begin
  induction H with L1 L1 L2 L3 x b H ih,
  case red.refl
  { exact ⟨0, rfl⟩ },
  case red.trans_bnot
  { cases ih with n ih,
    existsi nat.succ n,
    change _ = list.length _ + 2 * n + 2,
    rw [ih, list.length_append, list.length_append],
    change _ + L3.length + 2 + 2 * n = _,
    ac_refl }
end

@[trans] theorem red.trans (H12 : red L₁ L₂) (H23 : red L₂ L₃) : red L₁ L₃ :=
begin
  induction H23 with L1 L1 L2 L3 x b H ih generalizing L₁,
  case red.refl
  { assumption },
  case red.trans_bnot
  { exact red.trans_bnot (ih H12) }
end

theorem church_rosser_1 {x b} (H : red (L₁ ++ (x, b) :: (x, bnot b) :: L₂) L₃) :
  red (L₁ ++ L₂) L₃ ∨
  ∃ L₄ L₅ x' b', L₃ = L₄ ++ (x', b') :: (x', bnot b') :: L₅ ∧ red (L₁ ++ L₂) (L₄ ++ L₅) :=
begin
  revert H,
  generalize HL12 : L₁ ++ (x, b) :: (x, bnot b) :: L₂ = L12,
  intro H,
  induction H with L1 L1 L2 L3 x1 b1 H1 ih1,
  case red.refl
  { right,
    subst HL12,
    exact ⟨_, _, _, _, rfl, red.refl⟩ },
  case free_group.red.trans_bnot
  { specialize ih1 HL12,
    rcases ih1 with ih1 | ⟨L₄, L₅, x', b', H2, H3⟩,
    { left,
      apply red.trans_bnot ih1 },
    { cases list.prefix_or_prefix_of_append_eq_append H2 with H4 H4,
      { cases H4 with L4 H4,
        subst H4,
        rw list.append_assoc at H2,
        replace H2 := list.append_right_cancel H2,
        change [(x1, b1)] ++ _ = _ at H2,
        cases list.prefix_or_prefix_of_append_eq_append H2 with H4 H4,
        { cases H4 with L5 H4,
          subst H4,
          rw list.append_assoc at H2,
          replace H2 := list.append_right_cancel H2,
          change [(x1, bnot b1)] ++ _ = _ at H2,
          cases list.prefix_or_prefix_of_append_eq_append H2 with H4 H4,
          { cases H4 with L6 H4,
            subst H4,
            rw list.append_assoc at H2,
            replace H2 := list.append_right_cancel H2,
            subst H2,
            right,
            rw ← list.append_assoc,
            existsi [_, _, _, _, rfl],
            change red (L₁ ++ L₂) (L2 ++ ((x1, b1) :: (x1, bnot b1) :: L6) ++ L₅) at H3,
            rw list.append_assoc,
            rw [list.append_assoc, list.cons_append, list.cons_append] at H3,
            exact red.trans_bnot H3 },
          { cases H4 with L6 H4,
            cases L5 with hd tl,
            case list.nil
            { dsimp at H2 H4,
              subst H4,
              cases list.cons.inj H2 with H4 H6,
              cases prod.mk.inj H4 with H4 H5,
              subst_vars, clear H2 H4,
              left,
              simpa using H3 },
            case list.cons
            { cases list.cons.inj H4 with H5 H6,
              change _ ++ _ = _ at H6,
              rw list.append_eq_nil at H6,
              cases H6 with H6 H7,
              subst_vars, clear H4,
              replace H2 := list.append_right_cancel H2,
              subst H2,
              right,
              existsi [_, _, _, _, rfl],
              rw list.append_assoc at H3,
              exact red.trans_bnot H3 } } },
        { cases H4 with L5 H4,
          cases L4 with hd tl,
          case list.nil
          { dsimp at H2 H4,
            subst H4,
            cases list.cons.inj H2 with H4 H6, clear H4,
            cases list.cons.inj H6 with H4 H6,
            cases prod.mk.inj H4 with H4 H5,
            subst_vars, clear H2 H4 H6,
            left,
            simpa using H3 },
          case list.cons
          { cases list.cons.inj H4 with H5 H6,
            change _ ++ _ = _ at H6,
            rw list.append_eq_nil at H6,
            cases H6 with H6 H7,
            subst_vars, clear H4,
            replace H2 := list.append_right_cancel H2,
            cases list.cons.inj H2 with H4 H6,
            cases prod.mk.inj H4 with H4 H5,
            subst_vars,
            left,
            simpa using H3 } } },
      { cases H4 with L4 H4,
        subst H4,
        rw list.append_assoc at H2,
        replace H2 := list.append_right_cancel H2,
        change _ = [(x', b')] ++ _ at H2,
        cases list.prefix_or_prefix_of_append_eq_append H2 with H4 H4,
        { cases H4 with L5 H4,
          cases L4 with hd tl,
          case list.nil
          { dsimp at H2 H4,
            subst H4,
            cases list.cons.inj H2 with H4 H6,
            cases list.cons.inj H6 with H4 H6, clear H4,
            subst H6,
            left,
            simpa using H3 },
          case list.cons
          { cases list.cons.inj H4 with H5 H6,
            change _ ++ _ = _ at H6,
            rw list.append_eq_nil at H6,
            cases H6 with H6 H7,
            subst_vars,
            replace H2 := list.append_right_cancel H2,
            cases list.cons.inj H2 with H4 H6,
            cases prod.mk.inj H4 with H4 H5,
            subst_vars,
            left,
            simpa using H3 } },
        { cases H4 with L5 H4,
          subst H4,
          rw list.append_assoc at H2,
          replace H2 := list.append_right_cancel H2,
          change _ = [(x', bnot b')] ++ _ at H2,
          cases list.prefix_or_prefix_of_append_eq_append H2 with H4 H4,
          { cases H4 with L6 H4,
            cases L5 with hd tl,
            case list.nil
            { simp at H2,
              cases H2 with H5 H7,
              cases H5 with H5 H6,
              subst_vars,
              left,
              simpa using H3 },
            case list.cons
            { simp at H4,
              rcases H4 with ⟨_, _, _⟩,
              simp at H2,
              cases H2,
              subst_vars,
              right,
              rw list.append_assoc,
              existsi [_, _, _, _, rfl],
              exact red.trans_bnot H3 } },
          { cases H4 with L6 H4,
            subst H4,
            simp at H2,
            subst H2,
            right,
            rw list.append_assoc,
            existsi [_, _, _, _, rfl],
            change red _ (L₄ ++ (L6 ++ L3)),
            rw ← list.append_assoc at H3 ⊢,
            exact red.trans_bnot H3 } } } } }
end

theorem church_rosser (H12 : red L₁ L₂) (H13: red L₁ L₃) :
  ∃ L₄, red L₂ L₄ ∧ red L₃ L₄ :=
begin
  induction H12 with L1 L1 L2 L3 x1 b1 H1 ih1 generalizing L₃,
  case red.refl
  { exact ⟨L₃, H13, red.refl⟩ },
  case red.trans_bnot
  { specialize ih1 H13,
    rcases ih1 with ⟨L₄, H24, H34⟩,
    revert H24,
    generalize HL23 : L2 ++ (x1, b1) :: (x1, bnot b1) :: L3 = L23,
    intro H24,
    suffices : ∃ L₅, red (L2 ++ L3) L₅ ∧ red L₄ L₅,
    { rcases this with ⟨L₅, H25, H45⟩,
      exact ⟨L₅, H25, red.trans H34 H45⟩ },
    clear H13 H1 L1 L₁ L₂ H34 L₃,
    induction H24 with L4 L4 L5 L6 x2 b2 H2 ih2,
    case red.refl
    { subst HL23,
      exact ⟨L2 ++ L3, red.refl, red.trans_bnot red.refl⟩ },
    case red.trans_bnot
    { specialize ih2 HL23,
      rcases ih2 with ⟨L₅, H25, H45⟩,
      have := church_rosser_1 H45,
      rcases this with H3 | ⟨L₆, L₇, x3, b3, H4, H5⟩,
      { exact ⟨_, H25, H3⟩ },
      { subst H4,
        exact ⟨_, red.trans_bnot H25, H5⟩ } } }
end

variable α

instance : setoid (list (α × bool)) :=
⟨λ L₁ L₂, ∃ L₃, red L₁ L₃ ∧ red L₂ L₃,
 λ L, ⟨L, red.refl, red.refl⟩,
 λ L₁ L₂ ⟨L₃, H13, H23⟩, ⟨L₃, H23, H13⟩,
 λ L₁ L₂ L₃ ⟨L₄, H14, H24⟩ ⟨L₅, H25, H35⟩,
   let ⟨L₆, H46, H56⟩ := church_rosser H24 H25 in
   ⟨L₆, red.trans H14 H46, red.trans H35 H56⟩⟩

end free_group

variable α

def free_group : Type u :=
quotient (free_group.setoid α)

namespace free_group

variables {α} {L L₁ L₂ L₃ L₄ : list (α × bool)}

theorem red.append (H13 : red L₁ L₃) (H24 : red L₂ L₄) : red (L₁ ++ L₂) (L₃ ++ L₄) :=
begin
  induction H13 with L1 L1 L2 L3 x1 b1 H1 ih1 generalizing L₂ L₄,
  case red.refl
  { induction H24 with L4 L4 L5 L6 x2 b2 H2 ih2,
    case red.refl
    { exact red.refl },
    case red.trans_bnot
    { rw ← list.append_assoc at ih2 ⊢,
      exact red.trans_bnot ih2 } },
  case red.trans_bnot
  { induction H24 with L4 L4 L5 L6 x2 b2 H2 ih2,
    case red.refl
    { specialize @ih1 L4 L4 red.refl,
      rw list.append_assoc at ih1 ⊢,
      rw [list.cons_append, list.cons_append] at ih1,
      exact red.trans_bnot ih1 },
    case red.trans_bnot
    { rw ← list.append_assoc at ih2 ⊢,
      exact red.trans_bnot ih2 } }
end

theorem red.cons (H : red L₁ L₂) {x} : red (x :: L₁) (x :: L₂) :=
red.append (@red.refl _ [x]) H

theorem rel.append : L₁ ≈ L₃ → L₂ ≈ L₄ → (L₁ ++ L₂) ≈ (L₃ ++ L₄) :=
λ ⟨L₅, H15, H35⟩ ⟨L₆, H26, H46⟩,
⟨L₅ ++ L₆, red.append H15 H26, red.append H35 H46⟩

def inv : list (α × bool) → list (α × bool) :=
λ L, (L.map $ λ x : α × bool, (x.1, bnot x.2)).reverse

@[simp] protected lemma inv_inv : inv (inv L) = L :=
have H1 : (λ (x : α × bool), (x.fst, bnot (x.snd))) ∘ (λ (x : α × bool), (x.fst, bnot (x.snd))) = id,
  by funext; simp,
by simp [inv, H1]

theorem red.inv (H : red L₁ L₂) : red (inv L₁) (inv L₂) :=
begin
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { exact red.refl },
  case red.trans_bnot
  { simp [inv] at ih ⊢,
    exact red.trans_bnot ih }
end

theorem red.reverse (H : red L₁ L₂) : red L₁.reverse L₂.reverse :=
begin
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { exact red.refl },
  case red.trans_bnot
  { simp at ih ⊢,
    have ih2 : red (list.reverse L1) (list.reverse L3 ++ (x, bnot b) :: (x, bnot (bnot b)) :: list.reverse L2),
    { simpa using ih },
    exact red.trans_bnot ih2 }
end

theorem rel.inv : L₁ ≈ L₂ → inv L₁ ≈ inv L₂ :=
λ ⟨L₃, H13, H23⟩, ⟨inv L₃, red.inv H13, red.inv H23⟩

theorem red.inv_append : ∀ {L : list (α × bool)}, red (inv L ++ L) []
| []     := red.refl
| (h::t) := let (x, b) := h in
  have H1 : _ := @red.inv_append t,
  have H2 : inv t ++ (x, bnot b) :: (x, bnot (bnot b)) :: t = inv ((x, b) :: t) ++ (x, b) :: t,
    by simp [inv],
  H2 ▸ red.trans (red.bnot) H1

theorem rel.inv_append : inv L ++ L ≈ [] :=
⟨[], red.inv_append, red.refl⟩

instance : group (free_group α) :=
{ mul := quotient.lift₂ (λ L₁ L₂, ⟦L₁ ++ L₂⟧) $
    λ _ _ _ _ H1 H2, quotient.sound $ rel.append H1 H2,
  mul_assoc := λ x y z, quotient.induction_on₃ x y z $
    λ _ _ _, quotient.sound $ by simp,
  one := ⟦[]⟧,
  one_mul := λ x, quotient.induction_on x $
    λ _, quotient.sound $ setoid.refl _,
  mul_one := λ x, quotient.induction_on x $
    λ _, quotient.sound $ by simp,
  inv := quotient.lift (λ L, ⟦inv L⟧) $
    λ _ _ H, quotient.sound $ rel.inv H,
  mul_left_inv := λ x, quotient.induction_on x $
    λ _, quotient.sound $ rel.inv_append }

@[simp] lemma mul_mk : (⟦L₁⟧ * ⟦L₂⟧ : free_group α) = ⟦L₁ ++ L₂⟧ := rfl

def of (x : α) : free_group α :=
⟦[(x, tt)]⟧

theorem red.nil : red [] L₁ → [] = L₁ :=
begin
  generalize HX : [] = X,
  intro H,
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { refl },
  case red.trans_bnot
  { specialize ih HX,
    subst HX,
    replace ih := congr_arg list.length ih,
    rw list.length_append at ih,
    exact nat.no_confusion ih }
end

theorem red.singleton {xb} : red [xb] L₁ → [xb] = L₁ :=
begin
  generalize HX : [xb] = X,
  intro H,
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { refl },
  case red.trans_bnot
  { specialize ih HX,
    subst HX,
    replace ih := congr_arg list.length ih,
    rw list.length_append at ih,
    exact nat.no_confusion (nat.succ_inj ih) }
end

theorem of.inj {x y : α} (H : of x = of y) : x = y :=
begin
  replace H := quotient.exact H,
  rcases H with ⟨L₁, hx, hy⟩,
  replace hx := red.singleton hx,
  replace hy := red.singleton hy,
  subst hy,
  simpa using hx,
end

section to_group

variables {β : Type v} [group β] (f : α → β) {x y : free_group α}

def to_group.aux : list (α × bool) → β :=
λ L, list.prod $ L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹

def red.to_group {f : α → β} (H : red L₁ L₂) : to_group.aux f L₁ = to_group.aux f L₂ :=
begin
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { refl },
  case red.trans_bnot
  { rw ih,
    cases b; simp [to_group.aux] }
end

def to_group : free_group α → β :=
quotient.lift (to_group.aux f) $ λ L₁ L₂ ⟨L₃, H13, H23⟩,
(red.to_group H13).trans (red.to_group H23).symm

variable {f}

@[simp] lemma to_group.mk : to_group f ⟦L⟧ = list.prod (L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹) :=
rfl

@[simp] lemma to_group.of {x} : to_group f (of x) = f x :=
one_mul _

instance to_group.is_group_hom : is_group_hom (to_group f) :=
⟨λ x y, quotient.induction_on₂ x y $ λ _ _,
by simp [to_group, to_group.aux]⟩

@[simp] lemma to_group.mul : to_group f (x * y) = to_group f x * to_group f y :=
is_group_hom.mul _ _ _

@[simp] lemma to_group.one : to_group f 1 = 1 :=
is_group_hom.one _

@[simp] lemma to_group.inv : to_group f x⁻¹ = (to_group f x)⁻¹ :=
is_group_hom.inv _ _

theorem to_group.unique (g : free_group α → β) [is_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = to_group f x :=
quotient.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t ih, bool.rec_on b
  (show g ((of x)⁻¹ * ⟦t⟧) = to_group f ⟦(x, ff) :: t⟧,
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih, to_group, to_group.aux])
  (show g (of x * ⟦t⟧) = to_group f ⟦(x, tt) :: t⟧,
     by simp [is_group_hom.mul g, hg, ih, to_group, to_group.aux])

theorem to_group.of_eq (x : free_group α) : to_group of x = x :=
eq.symm $ to_group.unique id (λ x, rfl)

end to_group

section map

variables {β : Type v} (f : α → β) {x y : free_group α}

def map.aux (L : list (α × bool)) : list (β × bool) :=
L.map $ λ x, (f x.1, x.2)

theorem red.map (H : red L₁ L₂) : red (map.aux f L₁) (map.aux f L₂) :=
begin
  induction H with L L1 L2 L3 x b H ih,
  case red.refl
  { exact red.refl },
  case red.trans_bnot
  { simp [map.aux] at ih ⊢,
    exact red.trans_bnot ih }
end

theorem rel.map {f : α → β} : L₁ ≈ L₂ → map.aux f L₁ ≈ map.aux f L₂ :=
λ ⟨L₃, H13, H23⟩, ⟨map.aux f L₃, red.map f H13, red.map f H23⟩

def map (x : free_group α) : free_group β :=
x.lift_on (λ L, ⟦map.aux f L⟧) $
λ L₁ L₂ H, quotient.sound $ rel.map H

instance map.is_group_hom : is_group_hom (map f) :=
⟨λ x y, quotient.induction_on₂ x y $ λ L₁ L₂,
quotient.sound $ by simp [map.aux]⟩

variable {f}

@[simp] lemma map.mk : map f ⟦L⟧ = ⟦L.map (λ x, (f x.1, x.2))⟧ :=
rfl

@[simp] lemma map.id : map id x = x :=
have H1 : (λ (x : α × bool), x) = id := rfl,
quotient.induction_on x $ λ L, quotient.sound $ by simp [map.aux, H1]

@[simp] lemma map.id' : map (λ z, z) x = x := map.id

theorem map.comp {γ : Type w} {f : α → β} {g : β → γ} {x} : map g (map f x) = map (g ∘ f) x :=
quotient.induction_on x $ λ L, quotient.sound $ by simp [map.aux]

@[simp] lemma map.of {x} : map f (of x) = of (f x) := rfl

@[simp] lemma map.mul : map f (x * y) = map f x * map f y :=
is_group_hom.mul _ x y

@[simp] lemma map.one : map f 1 = 1 :=
is_group_hom.one _

@[simp] lemma map.inv : map f x⁻¹ = (map f x)⁻¹ :=
is_group_hom.inv _ x

theorem map.unique (g : free_group α → free_group β) [is_group_hom g]
  (hg : ∀ x, g (of x) = of (f x)) {x} :
  g x = map f x :=
quotient.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t ih, bool.rec_on b
  (show g ((of x)⁻¹ * ⟦t⟧) = map f ((of x)⁻¹ * ⟦t⟧),
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih])
  (show g (of x * ⟦t⟧) = map f (of x * ⟦t⟧),
     by simp [is_group_hom.mul g, hg, ih])

def free_group_congr {α β} (e : α ≃ β) : free_group α ≃ free_group β :=
⟨map e, map e.symm,
 λ x, by simp [function.comp, map.comp],
 λ x, by simp [function.comp, map.comp]⟩

theorem map_eq_to_group : map f x = to_group (of ∘ f) x :=
eq.symm $ map.unique _ $ λ x, by simp

end map

section prod

variables [group α] (x y : free_group α)

def prod : α :=
to_group id x

variables {x y}

@[simp] protected lemma prod.quotient.mk : prod ⟦L⟧ = list.prod (L.map $ λ x, cond x.2 x.1 x.1⁻¹) :=
rfl

@[simp] lemma prod.of {x : α} : prod (of x) = x :=
to_group.of

instance prod.is_group_hom : is_group_hom (@prod α _) :=
to_group.is_group_hom

@[simp] lemma prod.mul : prod (x * y) = prod x * prod y :=
to_group.mul

@[simp] lemma prod.one : prod (1:free_group α) = 1 :=
to_group.one

@[simp] lemma prod.inv : prod x⁻¹ = (prod x)⁻¹ :=
to_group.inv

end prod

theorem to_group_eq_prod_map {β : Type v} [group β] {f : α → β} {x} :
  to_group f x = prod (map f x) :=
eq.symm $ to_group.unique (prod ∘ map f) $ λ _, by simp

section sum

variables [add_group α] (x y : free_group α)

def sum : α :=
@prod (multiplicative _) _ x

variables {x y}

@[simp] lemma sum.mk : sum ⟦L⟧ = list.sum (L.map $ λ x, cond x.2 x.1 (-x.1)) :=
rfl

@[simp] lemma sum.of {x : α} : sum (of x) = x :=
prod.of

instance sum.is_group_hom : is_group_hom (@sum α _) :=
prod.is_group_hom

@[simp] lemma sum.sum : sum (x * y) = sum x + sum y :=
prod.mul

@[simp] lemma sum.one : sum (1:free_group α) = 0 :=
prod.one

@[simp] lemma sum.inv : sum x⁻¹ = -sum x :=
prod.inv

end sum

def free_group_empty_equiv_unit : free_group empty ≃ unit :=
{ to_fun    := λ _, (),
  inv_fun   := λ _, 1,
  left_inv  := λ x, quotient.induction_on x $ λ L, match L with [] := rfl end,
  right_inv := λ ⟨⟩, rfl }

def free_group_unit_equiv_unit : free_group unit ≃ int :=
{ to_fun    := λ x, sum $ map (λ _, 1) x,
  inv_fun   := λ x, of () ^ x,
  left_inv  := λ x, quotient.induction_on x $ λ L,
    begin
      induction L with hd tl ih,
      case list.nil
      { refl },
      case list.cons
      { rcases hd with ⟨⟨⟩, _ | _⟩;
        simp [function.comp, gpow_add] at ih ⊢;
        rw ih; refl }
    end,
  right_inv := λ x,
    begin
      dsimp,
      apply int.induction_on x,
      { simp },
      { intros i ih, simp [gpow_add, ih] },
      { intros i ih, simp [gpow_add, ih] }
    end }

theorem useless [group α] (s : set α) :
  set.range (@free_group.to_group s _ _ subtype.val) = group.closure s :=
begin
  apply set.ext,
  intro z,
  split,
  { intro h,
    rcases h with ⟨x, H⟩,
    subst H,
    apply quotient.induction_on x, clear x,
    intro L,
    induction L with hd tl ih,
    case list.nil
    { simp [is_submonoid.one_mem] },
    case list.cons
    { simp at ih ⊢,
      apply is_submonoid.mul_mem,
      { rcases hd with ⟨x, _ | _⟩,
        { simp [is_subgroup.inv_mem (group.subset_closure x.2)] },
        { simp [group.subset_closure x.2] } },
      { assumption } } },
  { intro H,
    induction H with x H x H ih x1 x2 H1 H2 ih1 ih2,
    case group.in_closure.basic
    { existsi (of (⟨x, H⟩ : s)),
      simp },
    case group.in_closure.one
    { existsi (1 : free_group s),
      simp },
    case group.in_closure.inv
    { cases ih with y h,
      existsi y⁻¹,
      simp [h] },
    case group.in_closure.mul
    { cases ih1 with y1 h1,
      cases ih2 with y2 h2,
      existsi y1 * y2,
      simp [h1, h2] } }
end

section reduce

variable [decidable_eq α]

def reduce.step : list (α × bool) → (α × bool) → list (α × bool)
| ((x1,tt)::tl) (x2,tt) := (x2,tt)::(x1,tt)::tl
| ((x1,tt)::tl) (x2,ff) := if x1 = x2 then tl else (x2,ff)::(x1,tt)::tl
| ((x1,ff)::tl) (x2,tt) := if x1 = x2 then tl else (x2,tt)::(x1,ff)::tl
| ((x1,ff)::tl) (x2,ff) := (x2,ff)::(x1,ff)::tl
| [] x := [x]

def reduce.core : list (α × bool) → list (α × bool) → list (α × bool)
| L []       := L
| L (hd::tl) := reduce.core (reduce.step L hd) tl

def reduce (L : list (α × bool)) : list (α × bool) :=
reduce.core [] L.reverse

theorem reduce.step.red : ∀ {L : list (α × bool)} {x b}, red ((x,b)::L) (reduce.step L (x,b))
| []            _  _  := red.refl
| ((x1,tt)::tl) x2 tt := red.refl
| ((x1,tt)::tl) x2 ff := if H : x1 = x2
    then by simp [reduce.step, H]; from red.cons_bnot
    else by simp [reduce.step, H]; from red.refl
| ((x1,ff)::tl) x2 tt := if H : x1 = x2
    then by simp [reduce.step, H]; from red.cons_bnot
    else by simp [reduce.step, H]; from red.refl
| ((x1,ff)::tl) x2 ff := red.refl

theorem reduce.core.red : ∀ {L₁ L₂ : list (α × bool)}, red (L₂.reverse ++ L₁) (reduce.core L₁ L₂)
| L []          := by simp [reduce.core]; from red.refl
| L ((x,b)::tl) := 
  begin
    simp [reduce.core],
    transitivity,
    { exact red.append red.refl reduce.step.red },
    { exact reduce.core.red }
  end

theorem reduce.red : red L (reduce L) :=
by simpa using @reduce.core.red _ _ [] L.reverse

theorem reduce.step.not : ∀ {L₁ : list (α × bool)} {x1 b1 x2 b2},
  (x2, b2) :: (x2, bnot b2) :: L <:+ reduce.step L₁ (x1, b1) → (x2, b2) :: (x2, bnot b2) :: L <:+ L₁
| [] _ _ _ _ ⟨[], H⟩   := list.no_confusion (list.cons.inj H).2
| [] _ _ _ _ ⟨[hd], H⟩ := list.no_confusion (list.cons.inj H).2
| ((x,tt)::tl) _ tt _ _ ⟨[], H⟩ := by simp [reduce.step] at H;
    rcases H with ⟨⟨_, _⟩, ⟨_, _⟩, _⟩; subst_vars;
    from bool.no_confusion H_right_left_right
| ((x,tt)::tl) _ tt _ _ ⟨(x2,b)::tl2, H⟩ := ⟨tl2, (list.cons.inj H).2⟩
| ((x,ff)::tl) _ ff _ _ ⟨[], H⟩ := by simp [reduce.step] at H;
    rcases H with ⟨⟨_, _⟩, ⟨_, _⟩, _⟩; subst_vars;
    from bool.no_confusion H_right_left_right
| ((x,ff)::tl) _ ff _ _ ⟨(x2,b)::tl2, H⟩ := ⟨tl2, (list.cons.inj H).2⟩
| ((x,tt)::tl) x2 ff _ _ ⟨[], H⟩ := if h : x = x2
    then by simp [reduce.step, h] at H; subst H; from list.suffix_cons _ _
    else by simp [reduce.step, h] at H;
      rcases H with ⟨⟨_, _⟩, ⟨_, _⟩, _⟩; subst_vars;
      exfalso; apply h; refl
| ((x,tt)::tl) x2 ff _ _ ⟨(x3,b)::tl2, H⟩ := if h : x = x2
    then by simp [reduce.step, h] at H; subst H;
      existsi (x, tt) :: (x3, b) :: tl2; refl
    else by simp [reduce.step, h] at H; rw ← H.2;
      from list.suffix_append _ _
| ((x,ff)::tl) x2 tt _ _ ⟨[], H⟩ := if h : x = x2
    then by simp [reduce.step, h] at H; subst H; from list.suffix_cons _ _
    else by simp [reduce.step, h] at H;
      rcases H with ⟨⟨_, _⟩, ⟨_, _⟩, _⟩; subst_vars;
      exfalso; apply h; refl
| ((x,ff)::tl) x2 tt _ _ ⟨(x3,b)::tl2, H⟩ := if h : x = x2
    then by simp [reduce.step, h] at H; subst H;
      existsi (x, ff) :: (x3, b) :: tl2; refl
    else by simp [reduce.step, h] at H; rw ← H.2;
      from list.suffix_append _ _

theorem reduce.core.not {x b} (H : (x, b) :: (x, bnot b) :: L <:+ reduce.core L₁ L₂) : (x, b) :: (x, bnot b) :: L <:+ L₁ :=
begin
  induction L₂ with hd tl ih generalizing L₁,
  case list.nil
  { from H },
  case list.cons
  { dsimp [reduce.core] at H,
    cases hd,
    specialize ih H,
    from reduce.step.not ih }
end

theorem reduce.not {x b} (H : [(x, b), (x, bnot b)] <:+: reduce L) : false :=
let ⟨L₁, L₂, H1⟩ := H in
have H2 : L₁ ++ (x, b) :: (x, bnot b) :: L₂ = reduce L,
  by simpa using H1,
list.no_confusion $ list.eq_nil_of_suffix_nil $ reduce.core.not ⟨L₁, H2⟩

theorem reduce.min : red (reduce L₁) L₂ → reduce L₁ = L₂ :=
begin
  generalize HRL : reduce L₁ = RL,
  intro H,
  induction H with L1 L1 L2 L3 x b H ih,
  case red.refl
  { refl },
  case red.trans_bnot
  { specialize ih HRL,
    subst HRL,
    exfalso,
    have H1 : [(x, b), (x, bnot b)] <:+: reduce L₁,
    { rw ih,
      existsi [L2, L3],
      simp },
    from reduce.not H1 }
end

theorem reduce.idem : reduce (reduce L) = reduce L :=
eq.symm $ reduce.min reduce.red

theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := church_rosser reduce.red(red.trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

theorem reduce.rel : L₁ ≈ L₂ → reduce L₁ = reduce L₂ :=
λ ⟨L₃, H13, H23⟩, (reduce.eq_of_red H13).trans
(reduce.eq_of_red H23).symm

theorem reduce.sound (H : ⟦L₁⟧ = ⟦L₂⟧) : reduce L₁ = reduce L₂ :=
reduce.rel $ quotient.exact H

theorem reduce.exact (H : reduce L₁ = reduce L₂) : ⟦L₁⟧ = ⟦L₂⟧ :=
quotient.sound $ ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

theorem reduce.self : ⟦reduce L⟧ = ⟦L⟧ :=
reduce.exact reduce.idem

def to_word : free_group α → list (α × bool) :=
quotient.lift reduce $ λ L₁ L₂, reduce.rel

def to_word.mk {x : free_group α} : ⟦to_word x⟧ = x :=
quotient.induction_on x $ λ L₁, reduce.self

def to_word.inj (x y : free_group α) : to_word x = to_word y → x = y :=
quotient.induction_on₂ x y $ λ L₁ L₂, reduce.exact

instance : decidable_eq (free_group α) :=
function.injective.decidable_eq to_word.inj

end reduce

end free_group
