import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory

namespace Guardedlean

section PreservesChosen
open Limits
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

class PreservesChosenLimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cone K}, IsLimit c → IsLimit (F.mapCone c)
class PreservesChosenLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesChosenLimit K F := by infer_instance
class PreservesChosenFiniteLimits (F : C ⥤ D) where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesChosenLimitsOfShape J F := by infer_instance
instance idPreservesChosenLimits (C : Type u) [Category.{v} C] : PreservesChosenFiniteLimits (Functor.id C) where
  preservesFiniteLimits _ _ _ := {
    preservesLimit := {
      preserves := λ p => p
    }
  }
instance compPreservesChosenFiniteLimits {C : Type u} [Category.{v} C]
  {D : Type u} [Category.{v} D] {E : Type u} [Category.{v} E]
  (F : C ⥤ D) [Fp : PreservesChosenFiniteLimits F]
  (G : D ⥤ E) [Gp : PreservesChosenFiniteLimits G] : PreservesChosenFiniteLimits (Functor.comp F G) where
  preservesFiniteLimits _ _ _ := {
    preservesLimit := {
      preserves := λ p =>
        ((Gp.preservesFiniteLimits _).preservesLimit.preserves ((Fp.preservesFiniteLimits _).preservesLimit.preserves p))
    }
  }

abbrev PreservesChosenFiniteLimits.preserves {C : Type u} [LC : Category C]
   {D : Type} [LD : Category D] {F : Functor C D} [PF : PreservesChosenFiniteLimits F]
    {J : Type} [sJ : SmallCategory J] [fJ : FinCategory J]
            {K : J ⥤ C} {c : Limits.Cone K} (l : Limits.IsLimit c) : Limits.IsLimit (F.mapCone c) :=
   (PF.preservesFiniteLimits J).preservesLimit.preserves l

instance PreservesChosenLimit.subsingleton {C : Type u} [LC : Category C]
   {D : Type} [LD : Category D] {F : Functor C D}
   (J : Type) [SmallCategory J] [FinCategory J]
   (K : J ⥤ C) : Subsingleton (PreservesChosenLimit K F) :=
    ⟨by intro PF PG; cases PF; cases PG; congr; apply Subsingleton.allEq⟩

instance PreservesChosenLimitsOfShape.subsingleton {C : Type u} [LC : Category C]
   {D : Type} [LD : Category D] {F : Functor C D}
   (J : Type) [SmallCategory J] [FinCategory J]
   : Subsingleton (PreservesChosenLimitsOfShape J F) :=
    ⟨by intro PF PG; cases PF; cases PG; congr; apply Subsingleton.allEq⟩

instance PreservesChosenFiniteLimits.subsingleton {C : Type u} [LC : Category C]
   {D : Type} [LD : Category D] {F : Functor C D}
   : Subsingleton (PreservesChosenFiniteLimits F) :=
    ⟨by intro PF PG; cases PF; cases PG; congr; funext _ _ _; apply Subsingleton.allEq⟩

end PreservesChosen
