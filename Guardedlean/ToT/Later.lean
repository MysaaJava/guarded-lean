import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Types
import Guardedlean.ToT.Basic
import Guardedlean.ToT.CartesianClosed

open CategoryTheory

namespace Guardedlean

-- LATER
def ToT.Later : ToT ⥤ ToT where
  obj X := {
    set := fun
          | 0 => Unit
          | n+1 => X.set n
    restrict := fun
          | 0, _ => ()
          | n+1, x => X.restrict n x
  }
  map {X Y} f := {
    f := fun
      | 0,_ => ()
      | n+1,x => f.f n x
    restrictF := λ n x => by {
      cases n
      case zero => rfl
      case succ k => apply f.restrictF k x
    }
  }
  map_id X := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => rfl
    case succ k => rfl
  })
  map_comp {X Y Z} f g := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => rfl
    case succ k => rfl
  })

def ToT.Earlier : ToT ⥤ ToT where
  obj X := {
    set := λ n => X.set (n+1)
    restrict := λ n => X.restrict (n+1)
  }
  map {X Y} f := {
    f := λ n => f.f (n+1)
    restrictF := λ n => f.restrictF (n+1)
  }
  map_id X := ToT.Hom.ext (by simp only [CategoryStruct.id,implies_true])
  map_comp {X Y Z} f g := ToT.Hom.ext (by simp only [CategoryStruct.comp, implies_true])

@[simp]
def LaterUnfold (X : ToT) (n : ℕ): (ToT.Later.obj X).set (n+1) = X.set n := by rfl
@[simp]
def LaterUnfold0 (X : ToT) : (ToT.Later.obj X).set 0 = Unit := by rfl
@[simp]
def LaterUnfoldRestrict0 (X : ToT) (x:X.set 0): (ToT.Later.obj X).restrict 0 x = () := by rfl
@[simp]
def LaterUnfoldRestrictN (X : ToT) (n : ℕ) (x:X.set (n+1)): (ToT.Later.obj X).restrict (n+1) x = X.restrict n x := by rfl
@[simp]
def EarlierUnfold (X : ToT) (n : ℕ): (ToT.Earlier.obj X).set (n) = X.set (n+1) := by rfl
@[simp]
def EarlierUnfoldRestrict (X : ToT) (n : ℕ) (x : X.set (n+1+1)): (ToT.Earlier.obj X).restrict n x = X.restrict (n + 1) x := by rfl

def ToT.LaterEarlierAdj : ToT.Earlier ⊣ ToT.Later where
  unit := {
    app := λ X => {
      f := λ n x => match n with | 0 => () | _+1 => x
      restrictF := λ n x => by {
        cases n
        case zero => simp only [Functor.comp_obj, LaterUnfoldRestrict0]
        case succ k => simp only [Functor.comp_obj, LaterUnfoldRestrictN, EarlierUnfoldRestrict,
          Functor.id_obj]
      }
    }
    naturality := λ {X Y} f => ToT.Hom.ext (λ n x => by {
      cases n
      case zero => simp only [Earlier, Later, Nat.reduceAdd, Functor.comp_obj, Functor.id_obj,
        Functor.id_map, unfoldComp, Functor.comp_map]
      case succ k => simp only [Earlier, Later, Nat.reduceAdd, Functor.comp_obj,
        Functor.id_obj, Functor.id_map, unfoldComp, Functor.comp_map]
    })
  }
  counit := {
    app := λ X => {
      f := λ n x => x
      restrictF := λ n x => by simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, EarlierUnfoldRestrict,
          LaterUnfoldRestrictN]
    }
    naturality := λ {X Y} f => ToT.Hom.ext (λ n x => by simp only [Earlier,Later,Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, Functor.comp_map, unfoldComp,
        Functor.id_map])
  }
  right_triangle_components Y := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => cases x;simp only [Later, Nat.reduceAdd, Functor.id_obj, Functor.comp_obj,
      unfoldComp]
    case succ n => simp only [Later, Nat.reduceAdd, Functor.id_obj, Earlier, Functor.comp_obj,
      unfoldComp,CategoryStruct.id,id_eq];
  })
  left_triangle_components X := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => simp only [Earlier,Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, unfoldComp, CategoryStruct.id,id_eq]
    case succ n => simp only [Earlier,Functor.id_obj, Functor.comp_obj, unfoldComp, CategoryStruct.id,id_eq]
  })

def ToT.next (A : ToT) : A ⟶ ToT.Later.obj A where
  f
   | 0, _ => ()
   | n+1, a => A.restrict n a
  restrictF := by
               intro n x
               simp
               induction n with
               | zero => simp only [ToT.Later]
               | succ m _ => simp only [ToT.Later]

private def fixpval {Γ A : ToT} (f : MonoidalCategory.tensorObj Γ (ToT.Later.obj A) ⟶ A): (n : Nat) →  Γ.set n → A.set n
  | 0, γ => f.f 0 (γ, ())
  | n+1, γ => f.f (n+1) (γ, fixpval f n (Γ.restrict n γ))

private def fixp {Γ X : ToT} (f : MonoidalCategory.tensorObj Γ (ToT.Later.obj X) ⟶ X) : Γ ⟶ X where
  f := fixpval f
  restrictF n γ := by {
    induction n with
    | zero => simp only [fixpval, Function.comp_apply];apply f.restrictF 0
    | succ m p => simp only [fixpval,f.restrictF,prodRestrict]
                  simp only [ToT.Later]
                  rw [<-p]
                  congr
                  rw [<-p]
  }

def fixpoint {X : ToT} (f : ToT.Later.obj X ⟶ X) : ToT.one ⟶ X :=
  fixp ((MonoidalCategoryStruct.leftUnitor (ToT.Later.obj X)).hom ≫ f)

def fixpointfix (X : ToT) (f : ToT.Later.obj X ⟶ X):
  fixpoint f = fixpoint f ≫ ToT.next X ≫ f := by
  {
    apply ToT.Hom.ext; intros n x;
    cases n with
    | zero =>
      simp only [ToT.unfoldComp]
      rfl
    | succ n =>
      cases x
      simp only [ToT.one, ToT.next, ToT.unfoldComp, (fixpoint f).restrictF]
      simp only [fixpoint, fixp, ToT.one, fixpval, ToT.unfoldComp]
      apply congrArg
      -- e: the monoidal structure is just Prod under one abstraction
      have e : ∀ ξ ψ, (MonoidalCategory.leftUnitor (ToT.Later.obj X)).hom.f (n + 1) (ξ, ψ) = ψ := λ ξ ψ => by rfl
      rw [e]
  }
