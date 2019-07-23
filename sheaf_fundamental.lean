import topology.opens

universes v u
open topological_space lattice

variables (X : Type u) [topological_space X]

set_option old_structure_cmd true

structure presheaf : Type (max u (v+1)) :=
(F : ∀ U : opens X, Type v)
(res : Π U V : opens X, V ≤ U → F U → F V)
(res_self : ∀ U x, res U U (le_refl U) x = x)
(res_res : ∀ U V W HWV HVU x, res V W HWV (res U V HVU x) = res U W (le_trans HWV HVU) x)

namespace presheaf

instance : has_coe_to_fun (presheaf.{v} X) :=
⟨_, presheaf.F⟩

end presheaf

variables {X}
structure covering (U : opens X) : Type (u+1) :=
(ι : Type u)
(map : ι → opens X)
(map_le : ∀ i, map i ≤ U)
(exists_of_mem : ∀ x ∈ U, ∃ i, x ∈ map i)
variables (X)

structure sheaf extends presheaf.{v} X : Type (max u (v+1)) :=
(locality : ∀ U : opens X, ∀ s t : F U, ∀ OC : covering U,
  (∀ i : OC.ι, res U (OC.map i) (OC.map_le i) s = res U (OC.map i) (OC.map_le i) t) → s = t)
(gluing : ∀ U : opens X, ∀ OC : covering U, ∀ S : Π i : OC.ι, F (OC.map i),
  (∀ i j : OC.ι, res (OC.map i) (OC.map i ⊓ OC.map j) inf_le_left (S i) =
    res (OC.map j) (OC.map i ⊓ OC.map j) inf_le_right (S j)) →
  ∃ s : F U, ∀ i : OC.ι, res U (OC.map i) (OC.map_le i) s = S i)

def Func (Y : Type v) : sheaf.{(max u v) u} X :=
{ F := λ U, U → Y,
  res := λ U V HVU s v, s ⟨v.1, HVU v.2⟩,
  res_self := λ _ _, funext $ λ ⟨_, _⟩, rfl,
  res_res := λ _ _ _ _ _ _, rfl,
  locality := λ U s t OC H, funext $ λ ⟨u, hu⟩,
    let ⟨i, hui⟩ := OC.exists_of_mem u hu in
    have _ := congr_fun (H i) ⟨u, hui⟩, this,
  gluing := λ U OC S H, ⟨λ u, S (classical.some $ OC.exists_of_mem u.1 u.2)
      ⟨u.1, classical.some_spec $ OC.exists_of_mem u.1 u.2⟩,
    λ i, funext $ λ ⟨u, hu⟩, have _ := congr_fun (H i $ classical.some $ OC.exists_of_mem u $ OC.map_le i hu)
      ⟨u, hu, classical.some_spec $ OC.exists_of_mem u $ OC.map_le i hu⟩, this.symm⟩ }

variables {X}

namespace opens
def covering_res (U V : opens X) (H : V ⊆ U) (OC : covering U) : covering V :=
{ ι := OC.ι,
  map := λ i : OC.ι, V ⊓ OC.map i,
  map_le := λ _, inf_le_left,
  exists_of_mem := λ x hxV, let ⟨i, hi⟩ := OC.exists_of_mem _ (H hxV) in ⟨i, hxV, hi⟩ }
end opens

structure subpresheaf (F : presheaf.{v} X) : Type (max u v) :=
(to_set : Π U : opens X, set (F U))
(res_mem_to_set : ∀ {U V : opens X} (HVU : V ⊆ U) {s : F U}, s ∈ to_set U → F.res U V HVU s ∈ to_set V)

namespace subpresheaf

instance (F : presheaf.{v} X) : has_coe_to_fun (subpresheaf F) :=
⟨_, to_set⟩

instance (F : presheaf.{v} X) : partial_order (subpresheaf F) :=
partial_order.lift to_set (λ ⟨x, hx⟩ ⟨y, hy⟩, mk.inj_eq.mpr) infer_instance

def to_subsheaf {F : presheaf.{v} X} (S : subpresheaf F) : subpresheaf F :=
{ to_set := λ U, { x | ∃ OC : covering.{u} U, ∀ i : OC.ι, F.res U (OC.map i) (OC.map_le i) x ∈ S (OC.map i) },
  res_mem_to_set := λ U V HVU x ⟨OC, hx⟩, ⟨opens.covering_res U V HVU OC,
    λ i, have _ ∈ S ((opens.covering_res U V HVU OC).map i) := S.res_mem_to_set (set.inter_subset_right _ _) (hx i),
    by rwa F.res_res at this ⊢⟩ }

theorem le_to_subsheaf {F : presheaf.{v} X} (S : subpresheaf F) : S ≤ S.to_subsheaf :=
λ U x hx, ⟨{ ι := punit, map := λ _, U, map_le := λ _, le_refl U, exists_of_mem := λ x hxU, ⟨punit.star, hxU⟩ },
λ i, by rwa F.res_self⟩

def to_presheaf {F : presheaf.{v} X} (S : subpresheaf F) : presheaf X :=
{ F := λ U, S U,
  res := λ U V HVU x, ⟨F.res U V HVU x.1, S.2 HVU x.2⟩,
  res_self := λ U x, subtype.eq $ F.res_self U x.1,
  res_res := λ U V W HWV HVU x, subtype.eq $ F.res_res U V W HWV HVU x.1 }

end subpresheaf

structure subsheaf (F : presheaf.{v} X) extends subpresheaf F :=
(mem_of_res_mem : ∀ {U : opens X}, ∀ {s : F U}, ∀ OC : covering.{u} U,
  (∀ i : OC.ι, F.res U (OC.map i) (OC.map_le i) s ∈ to_set (OC.map i)) → s ∈ to_set U)

namespace subsheaf

def to_sheaf {F : sheaf.{v} X} (S : subsheaf F.to_presheaf) : sheaf X :=
{ locality := λ U ⟨s, hs⟩ ⟨t, ht⟩ OC H, subtype.eq $ F.locality U s t OC $ λ i,
    have _ := congr_arg subtype.val (H i), this,
  gluing := λ U OC ss H, let ⟨s, hs⟩ := F.gluing U OC (λ i, (ss i).1)
      (λ i j, have _ := congr_arg subtype.val (H i j), this) in
    ⟨⟨s, S.mem_of_res_mem OC (λ i, show F.res _ _ _ _ ∈ _, by rw hs; exact (ss i).2)⟩,
    λ i, subtype.eq $ (hs i)⟩,
  .. S.to_subpresheaf.to_presheaf }

end subsheaf

def continuous_subsheaf (Y : Type v) [topological_space Y] : subsheaf (Func X Y).to_presheaf :=
{ to_set := λ U, { f | continuous f },
  res_mem_to_set := λ U V HVU s hs, hs.comp $ continuous_induced_rng continuous_induced_dom,
  mem_of_res_mem := λ U s OC H, continuous_iff_continuous_at.2 $ λ ⟨x, hxU⟩,
    let ⟨i, hi⟩ := OC.exists_of_mem x hxU in λ V HV,
    let ⟨t, htV, ⟨u, hu, hut⟩, hxt⟩ := mem_nhds_sets_iff.1 (continuous_iff_continuous_at.1 (H i) ⟨x, hi⟩ HV) in
    mem_nhds_sets_iff.2 ⟨subtype.val ⁻¹' (subtype.val '' t),
      by rintros ⟨y, hy⟩ ⟨z, hzt, hzy⟩; dsimp only at hzy; subst hzy; exact htV hzt,
      ⟨u ∩ OC.map i, is_open_inter hu (OC.map i).2, by rw [← hut, subtype.image_preimage_val]; refl⟩,
      ⟨x, hi⟩, hxt, rfl⟩ }

namespace subpresheaf

variables {X} (F : presheaf X)

instance : has_sup (subpresheaf F) :=
⟨λ S T, ⟨λ U, S U ∪ T U, λ U V HVU s, or.imp (S.2 HVU) (T.2 HVU)⟩⟩

instance : has_inf (subpresheaf F) :=
⟨λ S T, ⟨λ U, S U ∩ T U, λ U V HVU s, and.imp (S.2 HVU) (T.2 HVU)⟩⟩

instance : has_Sup (subpresheaf F) :=
⟨λ SS, ⟨λ U, ⋃ S ∈ SS, to_set S U, λ U V HVU s hs,
let ⟨S, HS, hsS⟩ := set.mem_bUnion_iff.1 hs in set.mem_bUnion_iff.2 ⟨S, HS, S.2 HVU hsS⟩⟩⟩

instance : has_Inf (subpresheaf F) :=
⟨λ SS, ⟨λ U, ⋂ S ∈ SS, to_set S U, λ U V HVU s hs,
set.mem_bInter $ λ S HS, S.2 HVU $ set.mem_bInter_iff.1 hs S HS⟩⟩

instance : has_top (subpresheaf F) :=
⟨⟨λ U, set.univ, λ U V HVU s _, trivial⟩⟩

instance : has_bot (subpresheaf F) :=
⟨⟨λ U, ∅, λ U V HVU s, false.elim⟩⟩

instance subpresheaf.complete_lattice (F : presheaf X) : complete_lattice (subpresheaf F) :=
{ le_sup_left := λ S T U, set.subset_union_left _ _,
  le_sup_right := λ S T U, set.subset_union_right _ _,
  sup_le := λ S1 S2 S3 H13 H23 U, set.union_subset (H13 U) (H23 U),
  inf_le_left := λ S T U, set.inter_subset_left _ _,
  inf_le_right := λ S T U, set.inter_subset_right _ _,
  le_inf := λ S1 S2 S3 H12 H13 U, set.subset_inter (H12 U) (H13 U),
  le_top := λ S U, set.subset_univ _,
  bot_le := λ S U, set.empty_subset _,
  le_Sup := λ SS S HS U, set.subset_bUnion_of_mem HS,
  Sup_le := λ SS S HS U, set.bUnion_subset $ λ T HT, HS T HT U,
  Inf_le := λ SS S HS U, set.bInter_subset_of_mem HS,
  le_Inf := λ SS S HS U, set.subset_bInter $ λ T HT, HS T HT U,
  .. subpresheaf.partial_order F,
  .. subpresheaf.lattice.has_sup F,
  .. subpresheaf.lattice.has_inf F,
  .. subpresheaf.lattice.has_Sup F,
  .. subpresheaf.lattice.has_Inf F,
  .. subpresheaf.lattice.has_top F,
  .. subpresheaf.lattice.has_bot F }

end subpresheaf

namespace subsheaf

variables {X} (F : presheaf X)

instance (F : presheaf.{v} X) : has_coe_to_fun (subsheaf F) :=
⟨_, to_set⟩

instance (F : presheaf.{v} X) : partial_order (subsheaf F) :=
partial_order.lift to_set (λ ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩, mk.inj_eq.mpr) infer_instance

instance : has_inf (subsheaf F) :=
⟨λ S T, ⟨λ U, S U ∩ T U, λ U V HVU s, and.imp (S.2 HVU) (T.2 HVU),
  λ U s OC H, ⟨S.3 OC $ λ i, (H i).1, T.3 OC $ λ i, (H i).2⟩⟩⟩

instance : has_Inf (subsheaf F) :=
⟨λ SS, ⟨λ U, ⋂ S ∈ SS, to_set S U, λ U V HVU s hs,
set.mem_bInter $ λ S HS, S.2 HVU $ set.mem_bInter_iff.1 hs S HS,
λ U s OC H, set.mem_bInter $ λ S HS, S.3 OC $ λ i, set.mem_bInter_iff.1 (H i) S HS⟩⟩

instance : has_top (subsheaf F) :=
⟨⟨λ U, set.univ, λ U V HVU s _, trivial, λ _ _ _ _, trivial⟩⟩

instance subsheaf.semilattice_inf_top (F : presheaf X) : semilattice_inf_top (subsheaf F) :=
{ inf_le_left := λ S T U, set.inter_subset_left _ _,
  inf_le_right := λ S T U, set.inter_subset_right _ _,
  le_inf := λ S1 S2 S3 H12 H13 U, set.subset_inter (H12 U) (H13 U),
  le_top := λ S U, set.subset_univ _,
  .. subsheaf.partial_order F,
  .. subsheaf.lattice.has_inf F,
  .. subsheaf.lattice.has_Inf F,
  .. subsheaf.lattice.has_top F }

theorem Inf_le (SS : set (subsheaf F)) (S : subsheaf F) (HS : S ∈ SS) : Inf SS ≤ S :=
λ U, set.bInter_subset_of_mem HS

theorem le_Inf (SS : set (subsheaf F)) (S : subsheaf F) (HS : ∀ b ∈ SS, S ≤ b) : S ≤ Inf SS :=
λ U, set.subset_bInter $ λ T HT, HS T HT U

end subsheaf

def section_subsheaf (Y : Type v) (π : Y → X) : subsheaf (Func X Y).to_presheaf :=
{ to_set := λ U, { s | ∀ u : U, π (s u) = u.1 },
  res_mem_to_set := λ U V HVU s hs ⟨v, hv⟩, hs ⟨v, _⟩,
  mem_of_res_mem := λ U s OC H ⟨u, hu⟩, let ⟨i, hi⟩ := OC.exists_of_mem u hu in H i ⟨u, hi⟩ }

def continuous_section_subsheaf (Y : Type v) [topological_space Y] (π : Y → X) : subsheaf (Func X Y).to_presheaf :=
continuous_subsheaf Y ⊓ section_subsheaf Y π

structure germ (F : presheaf X) (x : X) :=
(U : opens X)
(hxU : x ∈ U)
(s : F U)

namespace germ

variables (F : presheaf X) (x : X)

instance : setoid (germ F x) :=
{ r := λ g1 g2, ∃ U : opens X, x ∈ U ∧ ∃ H1 : U ≤ g1.U, ∃ H2 : U ≤ g2.U, F.res g1.U U H1 g1.s = F.res g2.U U H2 g2.s,
  iseqv := ⟨λ g1, ⟨g1.U, g1.2, le_refl _, le_refl _, rfl⟩,
    λ g1 g2 ⟨U, hx, H1, H2, H3⟩, ⟨U, hx, H2, H1, H3.symm⟩,
    λ g1 g2 g3 ⟨U, hxU, H1, H2, H3⟩ ⟨V, hxV, H4, H5, H6⟩,
      ⟨U ⊓ V, ⟨hxU, hxV⟩, le_trans inf_le_left H1, le_trans inf_le_right H5,
      calc  F.res g1.U (U ⊓ V) (le_trans inf_le_left H1) g1.s
          = F.res U (U ⊓ V) inf_le_left (F.res g1.U U H1 g1.s) : by rw F.res_res
      ... = F.res U (U ⊓ V) inf_le_left (F.res g2.U U H2 g2.s) : by rw H3
      ... = F.res V (U ⊓ V) inf_le_right (F.res g2.U V H4 g2.s) : by rw [F.res_res, F.res_res]
      ... = F.res V (U ⊓ V) inf_le_right (F.res g3.U V H5 g3.s) : by rw H6
      ... = F.res g3.U (U ⊓ V) (le_trans inf_le_right H5) g3.s : by rw F.res_res⟩⟩ }

end germ

def stalk (F : presheaf X) (x : X) :=
quotient (germ.setoid F x)

def to_stalk (F : presheaf X) (x : X) (U : opens X) (hxU : x ∈ U) (s : F U) : stalk F x :=
⟦⟨U, hxU, s⟩⟧

theorem to_stalk_res (F : presheaf X) (x : X) (U V : opens X) (hxV : x ∈ V) (HVU : V ≤ U) (s : F U) :
  to_stalk F x V hxV (F.res U V HVU s) = to_stalk F x U (HVU hxV) s :=
quotient.sound ⟨V, hxV, le_refl V, HVU, F.res_res _ _ _ _ _ _⟩

def espace_etale (F : presheaf X) : Type (max u v) :=
Σ x : X, stalk F x

def of_espace_etale (F : presheaf X) (x : espace_etale F) : X :=
x.1

def to_espace_etale (F : presheaf X) (U : opens X) (s : F U) (p : U) : espace_etale F :=
⟨p.1, to_stalk F p.1 U p.2 s⟩

instance (F : presheaf X) : topological_space (espace_etale F) :=
{ is_open := λ S, ∀ x ∈ S, ∃ U : opens X, ∃ hxU : sigma.fst x ∈ U, ∃ s : F U, to_stalk F x.1 U hxU s = x.2 ∧
    ∀ p : X, ∀ hpU : p ∈ U, (⟨p, to_stalk F p U hpU s⟩ : espace_etale F) ∈ S,
  is_open_univ := λ ⟨p, g⟩ _, quotient.induction_on g $ λ ⟨U, hpU, s⟩, ⟨U, hpU, s, rfl, λ _ _, trivial⟩,
  is_open_inter := λ S T HS HT x hxST, let ⟨U, hxU, s, hsx, hs⟩ := HS x hxST.1,
    ⟨V, hxV, t, htx, ht⟩ := HT x hxST.2, ⟨W, hxW, HWU, HWV, h⟩ := quotient.exact (hsx.trans htx.symm) in
    ⟨W, hxW, F.res U W HWU s, by rw to_stalk_res; exact hsx,
    λ q hqW, ⟨by rw to_stalk_res; apply hs, by rw [h, to_stalk_res]; apply ht⟩⟩,
  is_open_sUnion := λ SS H x hx, let ⟨t, htSS, hxt⟩ := set.mem_sUnion.1 hx,
    ⟨U, hxU, s, hsx, hs⟩ := H t htSS x hxt in ⟨U, hxU, s, hsx, λ p hpU, set.mem_sUnion_of_mem (hs p hpU) htSS⟩ }

theorem continuous_of_espace_etale (F : presheaf X) : continuous (of_espace_etale F) :=
λ U HU ⟨p, g⟩ hpU, quotient.induction_on g $ λ ⟨V, hpV, s⟩,
⟨⟨U, HU⟩ ⊓ V, ⟨hpU, hpV⟩, F.res V _ inf_le_right s, to_stalk_res _ _ _ _ _ _ _, λ q hqUV, hqUV.1⟩

theorem continuous_to_espace_etale (F : presheaf X) (U : opens X) (s : F U) : continuous (to_espace_etale F U s) :=
λ S HS, is_open_iff_forall_mem_open.2 $ λ q hq, let ⟨V, hqV, t, hts, ht⟩ := HS _ hq,
⟨W, hqW, HWV, HWU, HW⟩ := quotient.exact hts in
⟨subtype.val ⁻¹' W.1,
λ p hpW, show (⟨_, _⟩ : espace_etale F) ∈ S, by erw [← to_stalk_res F p.1 U W hpW HWU, ← HW, to_stalk_res]; apply ht,
continuous_subtype_val _ W.2, hqW⟩

def espace_etale.basic (F : presheaf X) (U : opens X) (s : F U) : opens (espace_etale F) :=
⟨{ x | ∃ hxU : x.1 ∈ U, to_stalk F x.1 U hxU s = x.2 },
λ x ⟨hxU, hx⟩, ⟨U, hxU, s, hx, λ p hpU, ⟨hpU, rfl⟩⟩⟩

structure presheaf.hom (F : presheaf X) (G : presheaf X) :=
(to_fun : Π U : opens X, F U → G U)
(to_fun_res : ∀ U V : opens X, ∀ HVU : V ≤ U, ∀ s : F U, to_fun V (F.res U V HVU s) = G.res U V HVU (to_fun U s))

structure presheaf.equiv (F : presheaf X) (G : presheaf X) :=
(to_fun : Π U : opens X, F U → G U)
(inv_fun : Π U : opens X, G U → F U)
(left_inv : ∀ U : opens X, ∀ s : F U, inv_fun U (to_fun U s) = s)
(right_inv : ∀ U : opens X, ∀ s : G U, to_fun U (inv_fun U s) = s)
(to_fun_res : ∀ U V : opens X, ∀ HVU : V ≤ U, ∀ s : F U, to_fun V (F.res U V HVU s) = G.res U V HVU (to_fun U s))

theorem sheaf.locality' (F : sheaf X) {U : opens X} {s t : F.to_presheaf U}
  (H : ∀ x ∈ U, ∃ V : opens X, ∃ HVU : V ≤ U, x ∈ V ∧ F.res U V HVU s = F.res U V HVU t) :
  s = t :=
F.locality U s t ⟨U, λ p, classical.some $ H p.1 p.2, λ p, classical.some $ classical.some_spec $ H p.1 p.2,
  λ p hp, ⟨⟨p, hp⟩, (classical.some_spec $ classical.some_spec $ H p hp).1⟩⟩ $
λ p, (classical.some_spec $ classical.some_spec $ H p.1 p.2).2

theorem sheaf.locality'' (F : sheaf X) {U : opens X} {s t : F.to_presheaf U}
  (H : ∀ x ∈ U, to_stalk F.to_presheaf x U H s = to_stalk F.to_presheaf x U H t) :
  s = t :=
F.locality' $ λ x hxU, let ⟨V, hxV, HVU, HVU', hv⟩ := quotient.exact (H x hxU) in ⟨V, HVU, hxV, hv⟩

theorem germ.eta (F : presheaf X) (x : X) (g : germ F x) (H) :
  (⟨g.1, H, g.3⟩ : germ F x) = g :=
by cases g; refl

noncomputable def sheaf.glue (F : sheaf X) (U : opens X) (OC : covering U) (S : Π i : OC.ι, F.to_presheaf (OC.map i))
  (H : ∀ i j : OC.ι, F.res (OC.map i) (OC.map i ⊓ OC.map j) inf_le_left (S i) =
    F.res (OC.map j) (OC.map i ⊓ OC.map j) inf_le_right (S j)) :
  F.to_presheaf U :=
classical.some $ F.gluing U OC S H

theorem res_glue (F : sheaf X) (U : opens X) (OC : covering U) (S H i) :
  F.res U (OC.map i) (OC.map_le i) (F.glue U OC S H) = S i :=
classical.some_spec (F.gluing U OC S H) i

theorem glue_eq (F : sheaf X) (U : opens X) (OC : covering U) (S : Π i : OC.ι, F.to_presheaf (OC.map i)) (H s)
  (H2 : ∀ i, F.res U (OC.map i) (OC.map_le i) s = S i) :
  F.glue U OC S H = s :=
F.locality _ _ _ OC $ λ i, by rw [res_glue, H2]

theorem to_stalk_glue (F : sheaf X) {U : opens X} {OC : covering U} {S : Π i : OC.ι, F.to_presheaf (OC.map i)}
  {H p} (i) (H2 : p ∈ OC.map i) :
  to_stalk F.to_presheaf p U (OC.map_le i H2) (F.glue U OC S H) = to_stalk F.to_presheaf p (OC.map i) H2 (S i) :=
by rw ← to_stalk_res; congr' 1; apply res_glue

noncomputable def equiv_continuous_section_espace_etale (F : sheaf X) :
  F.to_presheaf.equiv (continuous_section_subsheaf (espace_etale F.to_presheaf) (of_espace_etale F.to_presheaf)).to_sheaf.to_presheaf :=
{ to_fun := λ U s, ⟨to_espace_etale F.to_presheaf U s, continuous_to_espace_etale F.to_presheaf U s, λ p, rfl⟩,
  inv_fun := λ U s, F.glue U
    ⟨U, λ p, ⟨subtype.val '' (s.1 ⁻¹' (espace_etale.basic F.to_presheaf (quotient.out (s.1 p).2).1 (quotient.out (s.1 p).2).3).1),
        let ⟨V, hv1, hv2⟩ := s.2.1 (espace_etale.basic F.to_presheaf (quotient.out (s.1 p).2).1 (quotient.out (s.1 p).2).3).1
          (espace_etale.basic F.to_presheaf (quotient.out (s.1 p).2).1 (quotient.out (s.1 p).2).3).2 in
        by rw [← hv2, subtype.image_preimage_val]; exact is_open_inter hv1 U.2⟩,
      λ p q ⟨r, hr, hrq⟩, hrq ▸ r.2,
      λ p hpU, ⟨⟨p, hpU⟩, ⟨p, hpU⟩, ⟨(quotient.out (s.1 ⟨p, hpU⟩).2).2,
        by dsimp only [to_stalk]; rw germ.eta; exact quotient.out_eq _⟩, rfl⟩⟩
    (λ p, F.res (quotient.out (s.1 p).2).1 _ (λ q ⟨r, ⟨hsr1, hsr2⟩, hrq⟩, hrq ▸ s.2.2 r ▸ hsr1) (quotient.out (s.1 p).2).3)
    (λ p q, F.locality'' $ λ r ⟨⟨u, ⟨hsu1, hsu2⟩, hur⟩, ⟨v, ⟨hsv1, hsv2⟩, hvr⟩⟩,
      have huv : u = v, from subtype.eq $ hur.trans hvr.symm,
      have hsu : (s.1 u).1 = u.1, from s.2.2 u,
      begin
        clear_, iterate 4 { erw to_stalk_res }; substs huv hur; cases u with u hu; dsimp only at *,
        generalize : equiv_continuous_section_espace_etale._match_3 F U s p u _ = h1,
        generalize : equiv_continuous_section_espace_etale._match_3 F U s q u _ = h2,
        revert h1 h2, rw ← hsu, intros, erw [hsu2, hsv2]
      end),
  left_inv := λ U s, glue_eq _ _ _ _ _ _ $ λ p, F.locality'' $ λ q ⟨u, ⟨hsu1, hsu2⟩, huq⟩,
    by clear_; erw [to_stalk_res, to_stalk_res]; subst huq; exact hsu2.symm,
  right_inv := λ U s, subtype.eq $ funext $ λ p, sigma.eq (s.2.2 p).symm $ begin
    dsimp only [to_espace_etale],
    generalize : to_espace_etale._proof_1 U p = h1,
    generalize : (s.2.2 p).symm = h2,
    revert h1 h2, rw ← s.2.2 p, intros, dsimp only,
    erw to_stalk_glue F, swap 3, exact p, swap,
    { refine ⟨p, ⟨(quotient.out (s.1 p).2).2, _⟩, (s.2.2 p).symm⟩,
      dsimp only [to_stalk], rw [germ.eta, quotient.out_eq] },
    erw to_stalk_res, dsimp only [to_stalk], rw [germ.eta, quotient.out_eq]
  end,
  to_fun_res := λ U V HVU s, subtype.eq $ funext $ λ p, sigma.eq rfl $ to_stalk_res _ _ _ _ _ _ _ }
