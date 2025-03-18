import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory Limits

namespace Guardedlean

class LexCategory.{v,u} (C : Type u) extends Category.{v,u} C where
   hasFiniteLimits : Limits.HasFiniteLimits C

instance (C : Type u) [LC : LexCategory.{v,u} C] : Limits.HasFiniteLimits C := LC.hasFiniteLimits
instance (C : Type u) [CC : Category.{v,u} C] [lC : Limits.HasFiniteLimits C] : LexCategory C where
  hasFiniteLimits := lC

@[nolint checkUnivs]
def Lex.{v,u} := Bundled LexCategory.{v,u}

instance : CoeSort Lex (Type u) :=
  ⟨Bundled.α⟩

instance str (C : Lex.{v, u}) : LexCategory.{v, u} C :=
  Bundled.str C

structure LexFunctor.{v₁,u₁,v₂,u₂} (C : Type u₁) [LC : LexCategory.{v₁} C]
   (D : Type u₂) [LD : LexCategory.{v₂} D] extends Functor C D where
   preservesFiniteLimits : PreservesFiniteLimits toFunctor

instance (C : Type u₁) [LC : LexCategory.{v₁} C]
   (D : Type u₂) [LD : LexCategory.{v₂} D] (F : LexFunctor C D)
    : PreservesFiniteLimits F.toFunctor := F.preservesFiniteLimits

def LexFunctor.mk'.{v₁,u₁,v₂,u₂} {C : Type u₁} [LC : LexCategory.{v₁} C]
   {D : Type u₂} [LD : LexCategory.{v₂} D] (F : C ⥤ D) [preserves : PreservesFiniteLimits F]
   : LexFunctor C D
   where
     toFunctor := F
     preservesFiniteLimits := by infer_instance

noncomputable abbrev LexFunctor.preserves {C : Type u} [LC : LexCategory C]
   {D : Type} [LD : LexCategory.{w} D] (F : LexFunctor.{w} C D) {J : Type} [sJ : SmallCategory J] [fJ : FinCategory J]
            {K : J ⥤ C} {c : Limits.Cone K} (l : Limits.IsLimit c) : Limits.IsLimit (F.mapCone c) :=
   Classical.choice $ (F.preservesFiniteLimits.preservesFiniteLimits J).preservesLimit.preserves l

def LexFunctor.id (C : Type u₁) [LC : LexCategory.{v₁} C]
  : LexFunctor.{v₁,u₁,v₁,u₁} C C where
    toFunctor := Functor.id C
    preservesFiniteLimits := inferInstance

@[ext]
lemma LexFunctor.ext {C : Type u} [LC : LexCategory.{w} C]
   {D : Type} [LD : LexCategory.{w} D] {F G : LexFunctor C D}
   (e : F.toFunctor = G.toFunctor): F = G := by
      cases F
      cases G
      subst e
      congr

instance LexFunctor.category (A B : Lex.{v,u}): Category.{max v u} (LexFunctor.{v,u,v,u} A B) where
   Hom F G := NatTrans F.toFunctor G.toFunctor
   id F := NatTrans.id F.toFunctor
   comp η ε := NatTrans.vcomp η ε


def LexFunctor.iso {C D : Lex} {F G : LexFunctor C D} (eF : F.toFunctor ≅ G.toFunctor) : F ≅ G where
  hom := eF.hom
  inv := eF.inv
  inv_hom_id := by
    have e := eF.inv_hom_id
    congr
  hom_inv_id := by
    have e := eF.hom_inv_id
    congr


def isoOfEq {C : Type u} [Category.{v} C] {X Y : C} (e : X = Y) : X ≅ Y := e ▸ Iso.refl X
instance Lex.bicategory : Bicategory.{max v u,max v u} Lex.{v, u} where
  Hom C D := LexFunctor C D
  id C := LexFunctor.mk' (Functor.id C)
  comp F G := LexFunctor.mk' (Functor.comp F.toFunctor G.toFunctor)
      (preserves := comp_preservesFiniteLimits F.toFunctor G.toFunctor)
  homCategory C D := LexFunctor.category C D
  whiskerLeft {_} {_} {_} F _ _ η := whiskerLeft F.toFunctor η
  whiskerRight {_} {_} {_} _ _ η H := whiskerRight η H.toFunctor
  associator {A} {B} {C} {D} F G H := LexFunctor.iso (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor {A} {B} F := LexFunctor.iso (Functor.leftUnitor F.toFunctor)
  rightUnitor {A} {B} F := LexFunctor.iso (Functor.rightUnitor F.toFunctor)

  id_whiskerLeft {A} {B} {F} {G} η := by
    simp only [Functor.id, LexFunctor.mk', whiskerLeft, LexFunctor.iso, Functor.leftUnitor,LexFunctor.category]
    congr
    simp only [Functor.comp_obj, LexFunctor.category, NatTrans.vcomp_eq_comp, NatTrans.comp_app,
      Category.comp_id, Category.id_comp]
  comp_whiskerLeft {A} {B} {C} {D} {F} {G} {H} {I} η := by
    simp only [Functor.id, LexFunctor.mk', whiskerLeft, Functor.comp_obj, LexFunctor.iso,
      Functor.associator]
    congr
    simp only [Functor.comp_obj, LexFunctor.category, NatTrans.vcomp_eq_comp, NatTrans.comp_app,
      Category.comp_id, Category.id_comp]
  id_whiskerRight {A} {B} {F} {G} η := by
    simp only [Functor.id, LexFunctor.mk', LexFunctor.category, NatTrans.vcomp_eq_comp,
      whiskerRight, NatTrans.id_app', CategoryTheory.Functor.map_id]
    congr
  comp_whiskerRight {A} {B} {C} {D} {F} {G} {H} {I} η := by
    simp only [Functor.id, LexFunctor.mk', whiskerRight]
    congr
    simp only [Functor.comp_obj, LexFunctor.category, NatTrans.vcomp_eq_comp, NatTrans.comp_app,
      Functor.map_comp]
  whiskerRight_id {A} {B} {F} {G} η := by
    simp only [Functor.id, LexFunctor.mk', LexFunctor.category, NatTrans.vcomp_eq_comp,
      whiskerRight]
    congr
    simp only [Functor.comp_obj, LexFunctor.iso, Functor.rightUnitor_hom_app, NatTrans.comp_app,
      Functor.rightUnitor_inv_app, Category.comp_id, Category.id_comp]
  whiskerRight_comp {A} {B} {C} {D} {F} {G} {H} {I} η := by
    simp only [Functor.id, LexFunctor.mk', whiskerRight, Functor.comp_map, Functor.comp_obj]
    congr
    simp only [Functor.comp_obj, LexFunctor.category, NatTrans.vcomp_eq_comp, LexFunctor.iso,
      Functor.associator_inv_app, NatTrans.comp_app, Functor.associator_hom_app, Category.comp_id,
      Category.id_comp]

  whisker_assoc {A} {B} {C} {D} {F} {G} {H} {I} η := by
    simp only [Functor.id, LexFunctor.mk', whiskerRight, Functor.comp_obj, whiskerLeft_app]
    congr
    simp only [Functor.comp_obj, LexFunctor.category, NatTrans.vcomp_eq_comp, LexFunctor.iso,
      Functor.associator_hom_app, NatTrans.comp_app, whiskerLeft_app, Functor.associator_inv_app,
      Category.comp_id, Category.id_comp]
  whisker_exchange {A} {B} {C} {F} {G} {H} {I} η θ := by
    simp only [whiskerLeft,whiskerRight]
    simp only [LexFunctor.category,NatTrans.vcomp]
    congr
    simp only [NatTrans.naturality]
  pentagon {A} {B} {C} {D} {E} {F} {G} {H} {I} := by
    simp only [LexFunctor.mk', whiskerRight, LexFunctor.iso, whiskerLeft]
    simp only [LexFunctor.category,NatTrans.vcomp]
    congr
    simp only [Functor.comp_obj, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
  triangle {A} {B} {C} {F} {G} := by
    simp only [LexFunctor.mk', LexFunctor.iso]
    rw [<-Functor.triangle F.toFunctor G.toFunctor]
    rfl

instance Lex.bicategory.strict : Bicategory.Strict Lex.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl
