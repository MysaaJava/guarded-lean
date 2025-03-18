import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Order.Category.HeytAlg
import Guardedlean.CategoryTheory.Lex
import Guardedlean.CatHyp
import Guardedlean.Logic

open CategoryTheory Limits

namespace Guardedlean

structure Inv {A : Type u} {B : Type v} (f : A → B) where
  inv : B → A
  inv_hom : ∀ x : A, inv (f x) = x
  hom_inv : ∀ x : B, f (inv x) = x

--TODO add as parameter that the categories reached by u have an initial element
structure DependentRightAdjoint
  --{C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
  {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
  {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
  (P : FirstOrderHyperdoctrine U) (Q : FirstOrderHyperdoctrine T)
  (L: T ⥤ U) [pbF:PreservesLimitsOfShape Limits.WalkingCospan L] where
  R : NatTrans (L.op ⋙ P.P ⋙ HeytAsCat) (Q.P ⋙ HeytAsCat)
  preservesUnit : ∀ X : T, (R.app ⟨X⟩).obj (((L.op ⋙ P.P).obj ⟨X⟩).str.top) = (Q.P.obj ⟨X⟩).str.top
  preservesTruth (X : T) (x : ((L.op ⋙ P.P ⋙ HeytAsCat).obj ⟨X⟩).α) :
    Inv (
      λ (f : ((((L.op ⋙ P.P ⋙ HeytAsCat).obj ⟨X⟩).str.Hom) (((L.op ⋙ P.P).obj ⟨X⟩).str.top) x)) =>
         (preservesUnit X) ▸ ((R.app ⟨X⟩).map f)
      )


structure Grothendieck {C : Type u₁} [Category.{v₁} C] (F : Functor C Cat.{v₂,u₂}) : Type _ where
  α : C
  str : F.obj α

structure Grothendieck.Hom {C : Type u₁} [Category.{v₁} C] (F : Functor C Cat.{v₂,u₂}) (A B : Grothendieck F): Type _ where
  f : A.α ⟶ B.α
  θ : (F.map f).obj A.str ⟶ B.str

instance Grothendieck.category {C : Type u₁} [Category.{v₁} C] (F : Functor C Cat.{v₂,u₂}) : Category (Grothendieck F) where
  Hom := Grothendieck.Hom F
  id A := ⟨𝟙 A.α, (F.map_id A.α) ▸ 𝟙 A.str⟩
  comp X Y := ⟨X.f ≫ Y.f, (F.map_comp X.f Y.f) ▸ (((F.map Y.f).map X.θ) : (((F.map X.f) ≫ (F.map Y.f)).obj _) ⟶ _) ≫ Y.θ⟩
  id_comp f := sorry
  comp_id := sorry
  assoc := sorry

structure CreatesDependentRightAdjoints (D : Type u) [Category D]
  (F : D ⥤ (Grothendieck (Hyp' HeytAlg HeytAsCat))) where
  createsDependentRightAdjoints {A B : D} (f : A ⟶ B) :
    DependentRightAdjoint ((F.obj A).str) (F.obj B).str (Quiver.Hom.unop12 (F.map f).f).toFunctor
