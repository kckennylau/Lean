inductive nested : Type
| nest : list nested → nested

namespace nested

@[elab_as_eliminator] protected def cases_on' :
  Π {C : nested → Sort*} (x : nested),
    (Π (a : list nested), C (nest a)) → C x
| C (nest L) ih := ih L

@[simp] lemma cases_on'_def {C : nested → Sort*}
  (L : list nested) (ih : Π (a : list nested), C (nest a)) :
  (nested.cases_on' (nest L) ih : C (nest L)) = ih L :=
nested.cases_on'.equations._eqn_1 C L ih

def mem : nested → nested → Prop
| x (nest L) := x ∈ L

instance : has_mem nested nested := ⟨mem⟩

def to_list : nested → list nested
| (nest L) := L

@[simp] lemma to_list_def (L : list nested) :
  to_list (nest L) = L :=
nested.to_list.equations._eqn_1 L

@[simp] lemma mem_def (x : nested) (L : list nested) :
  x ∈ (nest L) ↔ x ∈ L :=
show mem _ _ ↔ _, by rw nested.mem.equations._eqn_1

theorem mem_sizeof (x y : nested) (H : x ∈ y) :
  sizeof x < sizeof y :=
begin
  cases y with L,
  change sizeof x < nested.sizeof (nest L),
  rw nested.nest.sizeof_spec L,
  rw mem_def at H,
  induction L with hd tl ih,
  { exfalso, simp at H, assumption },
  change sizeof x < 1 + (1 + sizeof hd + sizeof tl),
  cases H with H H,
  { subst H, rw add_comm,
    apply nat.lt_succ_of_le,
    rw [add_comm 1, add_assoc],
    apply nat.le_add_right },
  specialize ih H,
  apply lt_trans ih,
  apply nat.add_lt_add_left,
  rw [add_comm, add_comm 1],
  apply nat.lt_succ_of_le,
  apply nat.le_add_right
end

theorem mem_wf : well_founded (@has_mem.mem nested _ _) :=
@subrelation.wf _ (inv_image nat.lt sizeof) has_mem.mem mem_sizeof $
inv_image.wf _ nat.lt_wf

@[elab_as_eliminator] protected def rec_on
  {C : nested → Sort*} (x : nested)
  (ih : ∀ L : list nested, (∀ z ∈ L, C z) → C (nest L)) : C x :=
well_founded.fix mem_wf
  (λ y, nested.cases_on' y $ λ L ih', ih L $ λ z h, ih' z $ (mem_def z L).2 h) _

@[simp] lemma rec_on_def
  {C : nested → Sort*} (L : list nested)
  (ih : ∀ L : list nested, (∀ z ∈ L, C z) → C (nest L)) :
  (nested.rec_on (nest L) ih : C (nest L))
  = ih _ (λ z HL, nested.rec_on z ih) :=
by unfold nested.rec_on; rw well_founded.fix_eq; simp

instance : decidable_eq nested :=
λ x, nested.rec_on x $ λ L1,
list.rec_on L1 (λ _ y, nested.cases_on' y $ λ L2,
    list.cases_on L2 (is_true rfl) (λ hd tl, is_false $ λ H, by injections)) $ λ hd1 tl1 ih1 ih2 y,
nested.rec_on y $ λ L2,
list.rec_on L2 (λ _, is_false $ λ H, by injections) $ λ hd2 tl2 ih3 ih4,
@decidable_of_decidable_of_iff (hd1 = hd2 ∧ nest tl1 = nest tl2) _
  (@@and.decidable (ih2 _ (or.inl rfl) _) (ih1 (λ z H b, ih2 _ (or.inr H) _) _)) $
⟨λ H, congr_arg nest (by simp [H.1, nest.inj H.2] : hd1 :: tl1 = hd2 :: tl2),
λ H, by split; injections; simp*⟩

instance mem.decidable_rel :
  decidable_rel (@has_mem.mem nested _ _)
| x (nest L) := decidable_of_decidable_of_iff (list.decidable_mem x L) (mem_def x L).symm

end nested
