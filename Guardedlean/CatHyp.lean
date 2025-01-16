import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Order.Category.HeytAlg
import Guardedlean.Logic
import Guardedlean.CategoryTheory.Lex
import Guardedlean.CategoryTheory.Bicategory.Opposite

open CategoryTheory

namespace Guardedlean

def Hyperdoctrine.precompose_map₂_id
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 (F: U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : Hyperdoctrine.HypNat (NatTrans.id F)
  = NatTrans.id (@HypFun C _ u _ _ _ _ _ _ F _)
 := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, Functor.comp_obj, HypNat, precompose_map₂,
     whiskerRight_twice, whiskerRight_app, Functor.op_obj, NatTrans.op_app, NatTrans.id_app', op_id,
     Functor.comp_map, CategoryTheory.Functor.map_id, NatTrans.id_app]
   simp only [CategoryStruct.id, HypFun, precompose, Functor.comp_obj, Functor.op_obj]

def Hyperdoctrine.precompose_map₂_comp
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {F G H: U ⥤ T} [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [pbG:PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 [pbH:PreservesChosenLimitsOfShape Limits.WalkingCospan H]
 (η : NatTrans F G) (θ : NatTrans G H)
 : Hyperdoctrine.HypNat (NatTrans.vcomp η θ)
  = NatTrans.vcomp (Hyperdoctrine.HypNat θ) (@Hyperdoctrine.HypNat C _ u _ _ _ _ _ _ _ _ _ _ η)
 := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, Functor.comp_obj, HypNat, precompose_map₂,
     whiskerRight_twice, whiskerRight_app, Functor.op_obj, NatTrans.op_app, NatTrans.comp_app,
     op_comp, Functor.comp_map, Functor.map_comp]

def Hyperdoctrine.precompose_map₂_whisker_left
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {V : Type u₅} [Category.{v₅} V] [Limits.HasFiniteLimits V]
 (F : U ⥤ T) {G H: T ⥤ V} [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [pbG:PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 [pbH:PreservesChosenLimitsOfShape Limits.WalkingCospan H]
 (η : NatTrans G H)
 : HypNat (whiskerLeft F η) = whiskerRight (HypNat η) (@HypFun C _ u _ _ _ _ _ _ F _)
  := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, HypFun, precompose_map, Functor.comp_obj, HypNat,
     precompose_map₂, whiskerRight_twice, whiskerRight_app, Functor.op_obj, NatTrans.op_app,
     whiskerLeft_app, Functor.comp_map]
def Hyperdoctrine.precompose_map₂_whisker_right
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {V : Type u₅} [Category.{v₅} V] [Limits.HasFiniteLimits V]
 {F G : U ⥤ T} (H: T ⥤ V) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [pbG:PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 [pbH:PreservesChosenLimitsOfShape Limits.WalkingCospan H]
 (η : NatTrans F G)
 : HypNat (whiskerRight η H) = whiskerLeft (@HypFun C _ u _ _ _ _ _ _ H _) (HypNat η)
  := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, HypFun, precompose, Functor.comp_obj,
     Functor.comp_map, precompose_map, Functor.op_obj, HypNat, precompose_map₂, whiskerRight_twice,
     whiskerRight_app, NatTrans.op_app, whiskerLeft_app, Functor.op_map, Quiver.Hom.unop_op]

def Hyperdoctrine.precompose_map₂_associator
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {V : Type u₅} [Category.{v₅} V] [Limits.HasFiniteLimits V]
 {W : Type u₆} [Category.{v₆} W] [Limits.HasFiniteLimits W]
 (F: U ⥤ T) (G: T ⥤ V) (H: V ⥤ W) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [pbG:PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 [pbH:PreservesChosenLimitsOfShape Limits.WalkingCospan H]
 : @HypNat C _ u _ _ _ _ _ _ _ _ _ _ ((Functor.associator F G H).hom) = (Functor.associator (HypFun H) (HypFun G) (HypFun F)).hom
  := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, HypFun, precompose, Functor.comp_obj,
     Functor.comp_map, precompose_map, Functor.op_obj, HypNat, precompose_map₂, whiskerRight_twice,
     whiskerRight_app, NatTrans.op_app, Functor.associator_hom_app, op_id,
     CategoryTheory.Functor.map_id, NatTrans.id_app]

def Hyperdoctrine.precompose_map₂_leftUnitor
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 (F: U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : @HypNat C _ u _ _ _ _ _ _ _ _ _ _ ((Functor.leftUnitor F).hom) = (Functor.leftUnitor (HypFun F)).hom
 := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, HypFun, precompose, precompose_map,
     Functor.comp_obj, Functor.op_obj, Functor.id_obj, Functor.comp_map, Functor.id_map, HypNat,
     precompose_map₂, whiskerRight_twice, whiskerRight_app, NatTrans.op_app,
     Functor.leftUnitor_hom_app, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]

def Hyperdoctrine.precompose_map₂_rightUnitor
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 (F: U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : @HypNat C _ u _ _ _ _ _ _ _ _ _ _ ((Functor.rightUnitor F).hom) = (Functor.rightUnitor (HypFun F)).hom
 := by
   apply NatTrans.ext
   funext P
   apply NatTrans.ext
   funext X
   simp only [category, NatTrans.vcomp_eq_comp, HypFun, precompose, precompose_map,
     Functor.comp_obj, Functor.op_obj, Functor.id_obj, Functor.comp_map, Functor.id_map, HypNat,
     precompose_map₂, whiskerRight_twice, whiskerRight_app, NatTrans.op_app,
     Functor.rightUnitor_hom_app, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]

-- This instance exists but is marked noncomputable
instance finCategoryWalkingCospan : FinCategory Limits.WalkingCospan where
  fintypeHom j j' := sorry

def Hyp (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{v₂,u₂})
   : Pseudofunctor (Opposite12 Lex.{v₃,u₃}) Cat.{max u₂ v₂ u₃,max v₁ u₁ v₂ u₂ v₃ u₃} where
     obj T := Bundled.mk (Hyperdoctrine C u T.unop12) (str:=Hyperdoctrine.category C u T.unop12)
     map F := Hyperdoctrine.HypFun F.unop12.toFunctor
     map₂ η := Hyperdoctrine.HypNat η.unop12
     mapId _ := Iso.refl _
     mapComp _ _ := Iso.refl _
     map₂_id F := Hyperdoctrine.precompose_map₂_id F.unop12.toFunctor
     map₂_comp η θ := Hyperdoctrine.precompose_map₂_comp θ.unop12 η.unop12
     map₂_whisker_left F _ _ η := Hyperdoctrine.precompose_map₂_whisker_right F.unop12.toFunctor η.unop12
     map₂_whisker_right η H := Hyperdoctrine.precompose_map₂_whisker_left H.unop12.toFunctor η.unop12
     map₂_associator F G H := Hyperdoctrine.precompose_map₂_associator H.unop12.toFunctor G.unop12.toFunctor F.unop12.toFunctor
     map₂_left_unitor F := Hyperdoctrine.precompose_map₂_leftUnitor F.unop12.toFunctor
     map₂_right_unitor F := Hyperdoctrine.precompose_map₂_rightUnitor F.unop12.toFunctor

--TODO find this as ... something more OOP
def Hyp'
  (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{v₂,u₂})
  : CategoryTheory.Functor (Opposite12 Lex.{v₃,u₃}) Cat.{max u₂ v₂ u₃,max v₁ u₁ v₂ u₂ v₃ u₃} where
    obj T := Bundled.mk (Hyperdoctrine C u T.unop12) (str:=Hyperdoctrine.category C u T.unop12)
    map F := Hyperdoctrine.HypFun F.unop12.toFunctor
    map_id _ := rfl
    map_comp _ _ := rfl
