import set_theory.zfc set_theory.ordinal

universe u

attribute [elab_as_eliminator] well_founded.induction

def Well_order.to_pSet (w : Well_order.{u}) : pSet.{u} :=
pSet.mk w.1 $ well_founded.fix (@is_well_order.wf w.1 w.2 w.3) $ λ x ih,
pSet.mk { y | w.r y x } $ λ p, ih p.1 p.2

theorem Well_order.to_pSet.def (w : Well_order.{u}) (x : w.1) :
  w.to_pSet.func x = pSet.mk { y | w.r y x } (λ p, w.to_pSet.func p.1) :=
well_founded.fix_eq _ _ x

theorem ordinal.to_Set.aux (v w : Well_order.{u}) (e : v.2 ≃o w.2) (x : v.1) :
  (Well_order.to_pSet v).func x ≈ (Well_order.to_pSet w).func (e x) :=
show pSet.equiv
  (well_founded.fix (@is_well_order.wf v.1 v.2 v.3)
    (λ x ih, pSet.mk { y | v.r y x } $ λ p, ih p.1 p.2) x)
  (well_founded.fix (@is_well_order.wf w.1 w.2 w.3)
    (λ x ih, pSet.mk { y | w.r y x } $ λ p, ih p.1 p.2) (e x)),
from well_founded.induction (@is_well_order.wf v.1 v.2 v.3) x $ λ x ih,
by rw [well_founded.fix_eq, well_founded.fix_eq];
from ⟨λ ⟨y, hy⟩, ⟨⟨e y, (order_iso.ord e).1 hy⟩, ih y hy⟩,
λ ⟨y, hy⟩, ⟨⟨e.symm y, by simpa using (order_iso.ord e.symm).1 hy⟩,
  by have := ih (e.symm y) (by simpa using (order_iso.ord e.symm).1 hy); rw [order_iso.apply_inverse_apply] at this; from this⟩⟩

def ordinal.to_Set (o : ordinal.{u}) : Set.{u} :=
quotient.lift_on o (λ w, ⟦Well_order.to_pSet w⟧) $ λ ⟨v1, v2, v3⟩ ⟨w1, w2, w3⟩ ⟨e⟩, quotient.sound
⟨λ x, ⟨e x, ordinal.to_Set.aux _ _ e x⟩,
λ x, ⟨e.symm x, by simpa using ordinal.to_Set.aux ⟨v1, v2, v3⟩ ⟨w1, w2, w3⟩ e (e.symm x)⟩⟩

def pSet.type.setoid (p : pSet.{u}) : setoid p.type :=
⟨λ i j, ⟦p.func i⟧ = ⟦p.func j⟧, λ i, rfl, λ i j, eq.symm, λ i j k, eq.trans⟩

local attribute [instance] pSet.type.setoid

def Set.to_cardinal (s : Set.{u}) : cardinal.{u} :=
quotient.lift_on s (λ p, cardinal.mk $ quotient $ pSet.type.setoid p) $
λ ⟨p1, p2⟩ ⟨q1, q2⟩ H, quotient.sound $ nonempty.intro
{ to_fun := λ x, quotient.lift_on x (λ i, @@quotient.mk (pSet.type.setoid $ pSet.mk q1 q2) (classical.some (H.1 i))) $ λ i j H',
    quotient.sound $
    calc  ⟦q2 (classical.some (H.1 i))⟧
        = ⟦p2 i⟧ : eq.symm (quotient.sound $ classical.some_spec (H.1 i))
    ... = ⟦p2 j⟧ : H'
    ... = ⟦q2 (classical.some (H.1 j))⟧ : quotient.sound (classical.some_spec (H.1 j)),
  inv_fun := λ x, quotient.lift_on x (λ i, @@quotient.mk (pSet.type.setoid $ pSet.mk p1 p2) $ classical.some $ H.2 i) $ λ i j H',
    quotient.sound $
    calc  ⟦p2 (classical.some (H.2 i))⟧
        = ⟦q2 i⟧ : quotient.sound (classical.some_spec (H.2 i))
    ... = ⟦q2 j⟧ : H'
    ... = ⟦p2 (classical.some (H.2 j))⟧ : eq.symm (quotient.sound $ classical.some_spec (H.2 j)),
  left_inv := λ i, quotient.induction_on i $ λ i, quotient.sound $
    calc  ⟦p2 (classical.some (H.2 (classical.some (H.1 i))))⟧
        = ⟦q2 (classical.some (H.1 i))⟧ : quotient.sound (classical.some_spec (H.2 _))
    ... = ⟦p2 i⟧ : eq.symm (quotient.sound $ classical.some_spec (H.1 i)),
  right_inv := λ i, quotient.induction_on i $ λ i, quotient.sound $
    calc  ⟦q2 (classical.some (H.1 (classical.some (H.2 i))))⟧
        = ⟦p2 (classical.some (H.2 i))⟧ : eq.symm (quotient.sound $ classical.some_spec (H.1 _))
    ... = ⟦q2 i⟧ : quotient.sound (classical.some_spec (H.2 i)) }

theorem Well_order.to_pSet.exact (w : Well_order.{u}) (x : w.1) :
  ∀ y, ⟦w.to_pSet.func x⟧ = ⟦w.to_pSet.func y⟧ → x = y :=
well_founded.induction (@is_well_order.wf w.1 w.2 w.3) x $ λ x ih y H,
begin
  replace H := quotient.exact H,
  rw [Well_order.to_pSet.def, Well_order.to_pSet.def] at H,
  letI := w.3,
  rcases is_trichotomous.trichotomous w.2 x y with h | h | h,
  { rcases H.2 ⟨x, h⟩ with ⟨⟨z, hzx⟩, h1⟩,
    specialize ih z hzx x (quotient.sound h1),
    exfalso,
    subst ih,
    exact is_irrefl.irrefl w.r _ hzx },
  { exact h },
  { rcases H.1 ⟨y, h⟩ with ⟨⟨z, hzy⟩, h1⟩,
    specialize ih y h z (quotient.sound h1),
    exfalso,
    subst ih,
    exact is_irrefl.irrefl w.r _ hzy }
end

example (c : cardinal.{u}) : c.ord.to_Set.to_cardinal = c :=
begin
  apply quotient.induction_on c,
  intro c,
  have := cardinal.ord_eq c,
  rcases this with ⟨r, wo, H⟩,
  simp [H, ordinal.type, ordinal.to_Set],
  rw [Set.mk, Set.to_cardinal, quotient.lift_on_beta],
  apply quotient.sound,
  split,
  fapply equiv.mk,
  { fapply quotient.lift,
    { exact id },
    { intros x y H,
      exact Well_order.to_pSet.exact _ _ _ H } },
  { exact quotient.mk },
  { intro x,
    apply quotient.induction_on x,
    intro x,
    refl },
  { intro x, refl }
end

example : ordinal.to_Set 0 = ∅ :=
quotient.sound $ ⟨λ ⟨d⟩, match d with end, λ ⟨d⟩, match d with end⟩

theorem Well_order.to_pSet.sum (v w : Well_order.{u}) (x : v.1) :
  (⟨v.1 ⊕ w.1, sum.lex v.2 w.2, by letI := v.3; letI := w.3; exactI sum.lex.is_well_order⟩ : Well_order).to_pSet.func (sum.inl x) ≈ v.to_pSet.func x :=
begin
  cases v with v1 v2 v3,
  cases w with w1 w2 w3,
  resetI,
  dsimp [Well_order.to_pSet, pSet.func],
  rw [well_founded.fix_eq, well_founded.fix_eq],
  apply well_founded.induction (is_well_order.wf v2) x,
  intros x ih,
  split,
  { intro z,
    rcases z with ⟨z | z, hz | hz | hz⟩,
    fapply exists.intro,
    { refine ⟨z, _⟩,
      assumption },
    dsimp,
    rw [well_founded.fix_eq, well_founded.fix_eq],
    exact ih z (by assumption) },
  intro z,
  cases z with z hz,
  refine ⟨⟨sum.inl z, _⟩, _⟩,
  { constructor,
    assumption },
  dsimp,
  rw [well_founded.fix_eq, well_founded.fix_eq],
  exact ih z (by assumption)
end


example (o : ordinal.{u}) : o.succ.to_Set = insert o.to_Set o.to_Set :=
begin
  apply quotient.induction_on o,
  intro w,
  cases w with w1 w2 w3, resetI,
  apply quotient.sound,
  dsimp [pSet.resp.f, Well_order.to_pSet, pSet.insert],
  split,
  { intro s,
    cases s with s s,
    { existsi (some s),
      exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
        ⟨ulift unit, empty_relation, by apply_instance⟩ s },
    existsi none,
    dsimp,
    rw [well_founded.fix_eq],
    split,
    { intro s,
      rcases s with ⟨s | s, hs | hs | hs⟩,
      { existsi s,
        exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
          ⟨ulift unit, empty_relation, by apply_instance⟩ s },
      exfalso,
      assumption },
    intro s,
    refine ⟨⟨sum.inl s, _⟩, _⟩,
    { constructor },
    exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
      ⟨ulift unit, empty_relation, by apply_instance⟩ s },
  intro s,
  cases s,
  { existsi (sum.inr (ulift.up unit.star)),
    dsimp,
    split,
    { intro s,
      rcases s with ⟨s | s, hs | hs | hs⟩,
      { existsi s,
        exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
          ⟨ulift unit, empty_relation, by apply_instance⟩ s },
      exfalso,
      assumption },
    intro s,
    refine ⟨⟨sum.inl s, _⟩, _⟩,
    { constructor },
    exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
      ⟨ulift unit, empty_relation, by apply_instance⟩ s },
  existsi (sum.inl s),
  exact Well_order.to_pSet.sum (Well_order.mk w1 w2 w3)
    ⟨ulift unit, empty_relation, by apply_instance⟩ s
end

theorem Well_order.to_pSet.subrel (w : Well_order.{u}) (x : w.1) :
  ⟦w.to_pSet.func x⟧ = (@ordinal.typein w.1 w.2 w.3 x).to_Set :=
begin
  letI := w.3,
  apply quotient.sound,
  rw [Well_order.to_pSet.def],
  split;
  { intro y,
    existsi y,
    dsimp,
    apply well_founded.induction (is_well_order.wf (subrel w.r _)) y,
    intros y ih,
    rw [Well_order.to_pSet.def, well_founded.fix_eq],
    split,
    { intro z,
      exact ⟨⟨⟨z.1, is_trans.trans _ _ _ z.2 y.2⟩, z.2⟩, ih ⟨_, _⟩ z.2⟩ },
    intro z,
    exact ⟨⟨z.1, z.2⟩, ih _ z.2⟩ }
end/-
#check cardinal.omega.succ.ord.to_Set
def ordinal.to_Set.inj.aux1 (p : set.range Well_order.to_pSet.{u}) : Well_order.{u+1} :=
{ α := set.range p.1.func,
  r := subrel pSet.mem.{u} _,
  wo :=
  { wf := _ } }



theorem ordinal.to_Set.inj (p q : ordinal.{u}) (H : p.to_Set = q.to_Set) : p = q :=
begin
  revert H,
  apply quotient.induction_on₂ p q,
  intros v w H,
  replace H := quotient.exact H,
  apply quotient.sound,
  suffices : v.2 ≃o w.2,
  { cases v, cases w, constructor, exact this },
  fapply order_iso.mk,
  fapply equiv.mk,
  { intro x,
    exact classical.some (H.1 x) },
  { intro y,
    exact classical.some (H.2 y) },
  { intro x,
    apply Well_order.to_pSet.exact,
    have h1 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (H.2 (classical.some (H.1 x)))),
    have h2 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (H.1 x)),
    rw [h1, h2] },
  { intro y,
    apply Well_order.to_pSet.exact,
    have h1 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (H.1 (classical.some (H.2 y)))),
    have h2 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (H.2 y)),
    rw [← h1, ← h2] },
end-/

example (v w : Well_order.{u}) (t : w.1) (H : v.to_pSet ≈ w.to_pSet.func t) :
  ⟦v⟧ = @ordinal.typein w.1 w.2 w.3 t :=
begin
  apply quotient.sound,
  letI := w.3,
  suffices : v.2 ≃o subrel (w.r) {b : w.α | w.r b t},
  { cases v, constructor, exact this },
  revert v,
  apply well_founded.recursion (is_well_order.wf w.2) t,
  intros t ih v H,
end

example (p q : ordinal.{u}) : p < q ↔ p.to_Set ∈ q.to_Set :=
begin
  apply quotient.induction_on₂ p q,
  intros v w,
  letI := v.3,
  letI := w.3,
  have hv : v = {α := v.α, r := v.r, wo := by apply_instance},
  { cases v, congr },
  have hw : w = {α := w.α, r := w.r, wo := by apply_instance},
  { cases w, congr },
  split,
  { intro e,
    replace e : nonempty (principal_seg v.2 w.2),
    { cases v, cases w, exact e },
    cases e,
    have := congr_arg ordinal.to_Set (ordinal.typein_top e),
    existsi e.top,
    suffices : (_ : pSet) ≈ _,
    { unfold has_equiv.equiv setoid.r at this,
      exact this },
    apply quotient.exact,
    replace this := quotient.sound (quotient.exact this),
    rw ← hv at this, rw ← this, symmetry,
    exact Well_order.to_pSet.subrel _ e.top },
  intro H,
  cases H with t ht,
  change Well_order.to_pSet v ≈ pSet.func (Well_order.to_pSet _) _ at ht,
  suffices : principal_seg v.2 w.2,
  { cases v, cases w, constructor, exact this },
  revert ht,
  apply well_founded.recursion (is_well_order.wf w.2) t,
  intros t ih H,
/-  rw well_founded.fix_eq at hx,
  fapply principal_seg.mk,
  fapply order_embedding.mk,
  fapply function.embedding.mk,
  { intro x,
    exact (classical.some (hx.1 x)).1, },
  { intros x y h,
    have h1 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (hx.1 x)),
    have h2 : ⟦pSet.func (Well_order.to_pSet _) _⟧ = ⟦pSet.func (Well_order.to_pSet _) _⟧ :=
      quotient.sound (classical.some_spec (hx.1 y)),
    apply Well_order.to_pSet.exact,
    rw [h1, h2, h] },
  { intros x y,
    have : Well_order.to_pSet v ≈ pSet.func (Well_order.to_pSet _) _ := hx' },-/
end

--TODO: is ordinal iff transitive and linearly ordered
