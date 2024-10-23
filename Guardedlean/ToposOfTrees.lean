import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Guardedlean.ToT
import Guardedlean.Lemmas

open CategoryTheory

namespace Guardedlean



abbrev ToposOfTrees := ℕᵒᵖ ⥤ Type

/- A representation of an object in the topos of trees that is simpler
   than matlib's. -/


def G : ToposOfTrees ⥤ ToT where
  obj X := {
    set := λ n => X.obj (Opposite.op n),
    restrict := λ n => X.map (makeOpArrow (Nat.le_add_right n 1))
  }
  map {X Y} f := {
    setMorph := λ n x => f.app (Opposite.op n) x
    restrictMorph := λ n => by {
      simp
      rw [Function.comp_def, Function.comp_def,<-Function.comp_def,<-Function.comp_def]
      symm
      apply (f.naturality (makeOpArrow (Nat.le_add_right n 1)))
    }
  }

theorem ToTMorphism.restrictMorphLift {X Y : ToT} (η : X ⟶ Y) : ∀ n k m, (eq : n + k = m) →
    (Y.iterRestrict n k m eq) ∘ (η.setMorph m) = (η.setMorph n) ∘ (X.iterRestrict n k m eq) := by {
      intro n
      intro k
      induction k generalizing n with
      | zero =>
        intro m eq
        funext x
        simp
        rw [ToT.iterRestrictZero,ToT.iterRestrictZero]
        subst eq
        rfl
      | succ k hk =>
          intro m eq
          funext x
          simp [ToT.iterRestrict]
          rw [compDefExt (η.setMorph n)]
          rw [<-η.restrictMorph]
          simp
          congr
          rw [compDefExt (Y.iterRestrict (n+1) k m _),compDefExt (η.setMorph (n+1))]
          rw [hk]
    }

def F : ToT ⥤ ToposOfTrees := {
  obj := λ o => {
    map := λ {n m} f x =>
      have eq : m.unop + (n.unop - m.unop) = n.unop := by
        rw [Nat.add_sub_cancel']
        exact f.unop.down.down
      ToT.iterRestrict o m.unop (n.unop - m.unop) n.unop (by omega) x
    map_id := by
      intro o
      funext xw
      simp
      unfold ToT.iterRestrict
      rfl
    map_comp := by
      intro m n p f g
      funext x
      simp
      symm
      simp at x
      rw [ToT.iterRestrictComp o (Opposite.unop n) (Opposite.unop m) (Opposite.unop p) _ _ _ _ x]
      congr
      apply unmakeOpArrow at f
      apply unmakeOpArrow at g
      omega
  },
  map := λ {X Y} η => {
    app := λ n x => η.setMorph n.unop x
    naturality := λ {m n} p => by {
      simp
      funext x
      simp
      rw [compDefExt (η.setMorph (Opposite.unop n))]
      rw [<-ToTMorphism.restrictMorphLift]
      simp
    }
  }
}

def TTooTTequivalence : ToT ≌ ToposOfTrees := {
  functor := F
  inverse := G
  unitIso := {
    hom := {
      app := λ X => {
        setMorph := λ n x => x
        restrictMorph := λ n => by {
          simp
          rw [<-Function.id_def,<-Function.id_def,Function.comp_id,Function.id_comp]
          funext x
          unfold F G
          simp
          unfold ToT.iterRestrict
          rfl
        }
      }
    }
    inv := {
      app := sorry
    }
  }
  counitIso := {
    hom := sorry
    inv := sorry
  }
  functor_unitIso_comp := by {
    simp
    sorry
  }
}
