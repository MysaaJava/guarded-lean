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

-- TODO extract proof of X.set = Y.set ∧ X.restrict = Y.restrict => X = Y
lemma ToT.iterRestrictNatMapping (X : ToposOfTrees) (n k m : ℕ) (eq : m + k = n)
    (f : Opposite.op n ⟶ Opposite.op m) (x : X.obj (Opposite.op n))
  : (F.obj (G.obj X)).map f x = X.map f x := by {

    induction k generalizing n m with
    | zero =>
      simp at eq
      subst eq
      unfold F G
      simp
      rw [ToT.iterRestrictZero]
      simp
      have ef : f = (𝟙 (Opposite.op m)) := by rfl
      rw [ef, X.map_id]
      simp
    | succ k₀ hk =>
      subst eq
      have f₀ : Opposite.op (m + k₀) ⟶ Opposite.op m := makeOpArrow (by omega)
      have f₁ : Opposite.op (m + (k₀ + 1)) ⟶ Opposite.op (m + k₀) := makeOpArrow (by omega)
      have ef : f = f₁ ≫ f₀ := by congr --Both sides are hidden props
      rw [ef,X.map_comp]
      simp
      rw [<- hk _ _ rfl]
      apply congrArg

      unfold F G
      simp
      have e' : ({ set := fun n => X.obj (Opposite.op n), restrict := fun n => X.map (makeOpArrow (by omega)) }
        : ToT).iterRestrict (m + k₀) (m + (k₀ + 1) - (m + k₀)) (m + (k₀ + 1)) (by omega) x =
        ({ set := fun n => X.obj (Opposite.op n), restrict := fun n => X.map (makeOpArrow (by omega)) }
        : ToT).iterRestrict (m + k₀) 1 (m + (k₀ + 1)) (by omega) x := by {congr;omega}
      rw [e']
      unfold ToT.iterRestrict
      simp
      rw [ToT.iterRestrictZero]
      simp
      congr
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
      app := λ X => {
        setMorph := λ n x => x
        restrictMorph := λ n => by {
          funext x
          simp
          unfold F G
          simp
          unfold ToT.iterRestrict
          simp
          rw [ToT.iterRestrictZero]
        }
      }
    }
  }
  counitIso := {
    hom := {
      app := λ X => {
        app := λ n x => x
        naturality := λ n m f => by {
          funext x
          simp
          rw [ToT.iterRestrictNatMapping X _ (Opposite.unop n-Opposite.unop m)]
          apply unmakeOpArrow at f
          omega
        }
      }
    }
    inv := {
      app := λ X => {
        app := λ n x => x
        naturality := λ n m f => by {
          funext x
          simp
          rw [ToT.iterRestrictNatMapping X _ (Opposite.unop n - Opposite.unop m)]
          apply unmakeOpArrow at f
          omega
        }
      }
    }
  }
  functor_unitIso_comp := by {
    intro X
    simp
    congr
  }
}
