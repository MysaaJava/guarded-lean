import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Guardedlean.Logic
import Guardedlean.Categories
import Guardedlean.DependentRightAdjoint
import Guardedlean.ToT.FirstOrder
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

universe u

open CategoryTheory

namespace Guardedlean

abbrev HypFO := Hyp' HeytAlg HeytAsCat
abbrev HypF := Hyp HeytAlg HeytAsCat

instance : Limits.HasFiniteLimits ToT := sorry

@[simp]
def ToTL : Lex := ⟨ToT,⟨inferInstance⟩⟩
@[simp]
def SetL : Lex := ⟨Type u,⟨inferInstance⟩⟩

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

def GlobalSectionsFL : LexFunctor ToTL SetL := ⟨GlobalSectionsF,inferInstance⟩


noncomputable section
-- Δ := ToT.ofSet

def GlobalSectionsRight
  : DependentRightAdjoint ToT.hyperdoctrine HypType.hyperdoctrine ToT.ofSet
  where
    R := {
      app X := sorry
      naturality := sorry
    }
    preservesUnit := sorry
    preservesTruth := sorry

instance : Category.{v₂, u₂} PUnit.{u₂ + 1} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

@[simp]
def toTerminalCategory {M : Type u₁} [Bicategory.{w₁,v₁} M]: Pseudofunctor M Cat.{v₂,u₂} where
  obj X := ⟨PUnit,inferInstance⟩
  map f := Functor.id PUnit
  map₂ η := NatTrans.id (Functor.id PUnit)
  mapId X := Iso.refl _
  mapComp f g := Iso.refl _


def fromTerminalFunctor {X : Type u₁} [Category.{v₁} X]:
  X ≃ (PUnit ⟶ X) where
    toFun x := λ _ => x
    invFun x := x .unit
    left_inv x := by rfl
    right_inv x := by rfl

structure HyperdoctrineModel (M : Type u₁) [Bicategory.{v₁,w₁} M] where
  A : Pseudofunctor M Lex.{v₂,u₂}
  θ : OplaxNatTrans (@toTerminalCategory (Opposite12 M)).toOplax
    (Pseudofunctor.comp (Pseudofunctor.op12 A) (Hyp HeytAlg HeytAsCat)).toOplax


section M0
@[aesop safe cases]
inductive M0 where
  | T : M0
  | S : M0

instance M0.quiver: Quiver M0 where
  Hom := fun
    | .T,.T => Unit -- id_T
    | .S,.S => Unit -- id_S
    | .T,.S => Unit -- γ
    | .S,.T => Empty

@[aesop safe unfold]
abbrev γ : M0.T ⟶ M0.S := ()
@[aesop safe unfold]
abbrev idT : M0.T ⟶ M0.T := ()
@[aesop safe unfold]
abbrev idS : M0.S ⟶ M0.S := ()

--lemma test : (M0.S ⟶ M0.T) = Discrete Empty := rfl

attribute [aesop safe cases] Discrete
--attribute [simp] M0.quiver
attribute [aesop safe unfold] M0.quiver Category.toCategoryStruct instBicategoryOfPosetalBicategoryOnCategory
  Bicategory.toCategoryStruct CategoryStruct.toQuiver Quiver.Hom PosetalBicategoryOnCategory.toCategory

@[aesop safe unfold]
instance : Category M0 where
  id := fun
    | .T => idT
    | .S => idS
  comp := @fun
    | .T,.T,.T,(),() => idT
    | .T,.T,.S,(),() => γ
    | .T,.S,.S,(),() => γ
    | .S,.S,.S,(),() => idS

instance : Preorder Empty where
  le a b := True
  le_refl a := ⟨⟩
  le_trans a b c _ _ := ⟨⟩

set_option profiler true
--XXX This noncomputable is needed or else, a strange error pops up
@[aesop safe unfold]
noncomputable instance : PosetalBicategoryOnCategory M0 where
  homPoset := fun
    | .T,.T => by simp[Quiver.Hom];infer_instance
    | .T,.S =>  by simp[Quiver.Hom];infer_instance
    | .S,.T =>  by simp[Quiver.Hom];infer_instance
    | .S,.S =>  by simp[Quiver.Hom];infer_instance
  whiskerLeft := by aesop_cat
  whiskerRight := by aesop_cat

set_option maxHeartbeats 1200000
noncomputable def modelFunctor : Pseudofunctor M0 Lex where
  obj := fun
    | .T => ToTL
    | .S => SetL
  map := @fun
    | .T,.T,() => LexFunctor.id _
    | .T,.S,() => by simp;exact GlobalSectionsFL
    | .S,.S,() => LexFunctor.id _
  map₂ := @fun
    | .T,.T,(),(),_ => NatTrans.id _
    | .T,.S,(),(),_ => NatTrans.id _
    | .S,.S,(),(),_ => NatTrans.id _
  mapId := fun
    | .T => eqToIso rfl
    | .S => eqToIso rfl
  mapComp := @fun
    | .T,.T,.T,(),() => eqToIso rfl
    | .T,.T,.S,(),() => eqToIso rfl
    | .T,.S,.S,(),() => eqToIso rfl
    | .S,.S,.S,(),() => eqToIso rfl
  map₂_associator := @fun
    | .T,.T,.T,.T,(),(),() => eqToIso rfl
    | .T,.T,.T,.S,(),(),() => eqToIso rfl
    | .T,.T,.S,.S,(),(),() => eqToIso rfl
    | .T,.S,.S,.S,(),(),() => eqToIso rfl
    | .S,.S,.S,.S,(),(),() => eqToIso rfl

def fromTerminalFunctor' (X : Cat.{v,u}):
  X ≃ (⟨PUnit,inferInstance⟩ ⟶ X) where
    toFun x := {
      obj _ := x
      map _ := 𝟙 x
    }
    invFun x := x.obj .unit
    left_inv x := by rfl
    right_inv x := by
      simp only
      obtain ⟨px,x_id,x_comp⟩ := x
      congr
      funext a b c
      exact Eq.symm (x_id .unit)

noncomputable def natrans : OplaxNatTrans (@toTerminalCategory (Opposite12 M0)).toOplax
    (Pseudofunctor.comp (Pseudofunctor.op12 modelFunctor) (Hyp HeytAlg HeytAsCat)).toOplax
    where
      app := fun
        | ⟨.T⟩ => (fromTerminalFunctor' _).toFun ToT.hyperdoctrine
        | ⟨.S⟩ => (fromTerminalFunctor' _).toFun HypType.hyperdoctrine
      naturality := @fun
        | ⟨.S⟩,⟨.S⟩,⟨⟨.unit⟩⟩ => by
            simp?
            simp? [fromTerminalFunctor']
            rw [<-Cat.id_eq_id ⟨PUnit,_⟩]
            rw [@Category.id_comp Cat _ ⟨PUnit,_⟩]
            --have e : (modelFunctor.op12.map (Opposite12.op12 sorry)) = 𝟙 _ := sorry
            unfold Pseudofunctor.op12 modelFunctor
            simp?
            have e' (X : Lex) : (X ⟶ X)ᵒᵖ¹²
              = Quiver.Hom (Opposite12.op12 X) (Opposite12.op12 X)
              := rfl
            specialize e' SetL

            have e : @Opposite12.op12 (SetL ⟶ SetL) (LexFunctor.id SetL) =
              e' ▸ (@CategoryStruct.id (Opposite12 Lex) _ (Opposite12.op12 SetL))
               := sorry




             ▸ NatTrans.id
            rw [e]
            --have e2 := congrArg ((Hyp HeytAlg HeytAsCat).map) e
            --apply cast (congrArg (λ ξ => _ ≫ (Hyp HeytAlg HeytAsCat).map ξ) e)
            --let F : PUnit ⥤ Cat := { obj := fun x => HypType.hyperdoctrine, map := fun {X Y} x => 𝟙 HypType.hyperdoctrine, map_id := _, map_comp := _};
            unfold Hyp
            simp only
            exact NatTrans.id
        | ⟨.S⟩,⟨.T⟩,⟨⟨.unit⟩⟩ => sorry
        | ⟨.T⟩,⟨.T⟩,⟨⟨.unit⟩⟩ => sorry

#exit
        (by
            simp? []
            simp only [toTerminalCategory, Pseudofunctor.toOplax_toPrelaxFunctor,
              Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj]

            apply (@fromTerminalFunctor' _).toFun sorry
            sorry
            --simp [toTerminalCategory,modelFunctor,Cat]
            --simp [Quiver.Hom]
        )

      naturality := sorry

end M0
