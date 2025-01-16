import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.Basic
import Guardedlean.Logic
import Guardedlean.DependentRightAdjoint
import Guardedlean.ToT.FirstOrder

universe u

open CategoryTheory

namespace Guardedlean

abbrev HypFO := Hyp' HeytAlg HeytAsCat

instance : Limits.HasFiniteLimits ToT := sorry

def ToT' : Grothendieck HypFO :=  ⟨⟨⟨ToT,⟨inferInstance⟩⟩⟩,ToT.hyperdoctrine⟩
def Set' : Grothendieck HypFO :=  ⟨⟨⟨Type u,⟨inferInstance⟩⟩⟩,HypType.hyperdoctrine⟩

-- Global sections hyperdoctrine mophism
def GlobalSectionsF : ToT ⥤ Type u where
  obj X := {x : ((n : ℕ) → X.set n) //  ∀ n : ℕ, X.restrict n (x (n+1)) = x n}
  map F ξ := {
    val := λ n => F.f n (ξ.val n)
    property := λ n => by rw [F.restrictF,ξ.property]
  }
instance : PreservesChosenLimitsOfShape Limits.WalkingCospan GlobalSectionsF := sorry
instance : PreservesChosenFiniteLimits GlobalSectionsF := sorry
instance : PreservesChosenFiniteLimits ToT.ofSet := sorry

def GlobalSectionsFL : LexFunctor ToT (Type u) := ⟨GlobalSectionsF,inferInstance⟩

instance (α : Type u) [LexCategory α] : LexCategory (Opposite α) := sorry

def GlobalSectionsFO : ToTᵒᵖ ⥤ (Type u)ᵒᵖ := Functor.op GlobalSectionsF
def GlobalSectionsFLO : LexFunctor (Opposite ToT) (Opposite (Type u)) := ⟨GlobalSectionsFO,inferInstance⟩

def GlobalSections : Grothendieck.Hom HypFO Set' ToT' where
  f := Quiver.Hom.op12 GlobalSectionsFL
  θ := {
    app A := {
      obj φ := λ a => ∀ n, φ n A
    }
  }






-- Δ := ToT.ofSet

def GlobalSectionsRight
  : DependentRightAdjoint ToT.hyperdoctrine HypType.hyperdoctrine ToT.ofSet
  where
    R := {
      app X := _
    }
    preservesUnit := sorry
    preservesTruth := sorry
