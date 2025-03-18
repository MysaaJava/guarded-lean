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

open CategoryTheory Limits

namespace Guardedlean

abbrev HypFO := Hyp' HeytAlg HeytAsCat
abbrev HypF := Hyp HeytAlg HeytAsCat

instance : HasBinaryProducts ToT where
instance : HasTerminal ToT where
instance : HasEqualizers ToT where

instance : HasFiniteLimits ToT := inferInstance

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

def GlobalSectionsOne : GlobalSectionsF.obj X ≅ (ToT.one ⟶ X) where
  hom gX := {
    f n _ := gX.val n
    restrictF n _ := gX.property n
  }
  inv fX := {
    val n := fX.f n ⟨()⟩
    property n := fX.restrictF n ⟨()⟩
  }

instance : PreservesLimitsOfShape (Discrete WalkingPair) GlobalSectionsF where
  preservesLimit {K} := {
    preserves {c} cL := Nonempty.intro {
      lift s x := GlobalSectionsOne.inv (cL.lift ⟨ToT.one,
        mapPair (GlobalSectionsOne.hom (s.π.app ⟨.left⟩ x))
        (GlobalSectionsOne.hom (s.π.app ⟨.right⟩ x))⟩)
      fac s j := funext $ λ x => Subtype.ext $ funext $ λ n =>
        let fac := cL.fac ⟨ToT.one,
          mapPair (GlobalSectionsOne.hom (s.π.app ⟨.left⟩ x))
          (GlobalSectionsOne.hom (s.π.app ⟨.right⟩ x))⟩
        match j with
        | ⟨.left⟩ => congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) (fac ⟨.left⟩)
        | ⟨.right⟩ => congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) (fac ⟨.right⟩)
      uniq s m mc := funext $ λ x => Subtype.ext $ funext $ λ n =>
        let uniq := cL.uniq ⟨ToT.one,
          mapPair (GlobalSectionsOne.hom (s.π.app ⟨.left⟩ x))
          (GlobalSectionsOne.hom (s.π.app ⟨.right⟩ x))⟩
          (GlobalSectionsOne.hom (m x)) (by
            intro j
            match j with
            | ⟨.left⟩ => rw [<-congrFun (mc ⟨.left⟩) x];congr
            | ⟨.right⟩ => rw [<-congrFun (mc ⟨.right⟩) x];congr
          )
        congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) uniq
    }
  }
instance : PreservesLimitsOfShape (Discrete.{0} PEmpty) GlobalSectionsF where
  preservesLimit := {
    preserves cL := Nonempty.intro {
      lift _ _ := GlobalSectionsOne.inv (cL.lift ⟨ToT.one,⟨λ z => PEmpty.elim z.as,λ z => PEmpty.elim z.as⟩⟩)
      fac _ z := PEmpty.elim z.as
      uniq _ m _ := funext $ λ x => Subtype.ext $ funext $ λ n =>
        let uniq := cL.uniq ⟨ToT.one,⟨λ z => PEmpty.elim z.as,λ z => PEmpty.elim z.as⟩⟩
          (GlobalSectionsOne.hom (m x))
          (λ z => PEmpty.elim z.as)
        congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) uniq
    }
  }
instance : PreservesLimitsOfShape WalkingParallelPair GlobalSectionsF where
  preservesLimit {K} := {
    preserves {c} cL := Nonempty.intro {
      lift s x := GlobalSectionsOne.inv (cL.lift ⟨ToT.one,
        (diagramIsoParallelPair ((Functor.const WalkingParallelPair).obj ToT.one)).hom ≫ (
        parallelPairHom _ _ _ _
          (GlobalSectionsOne.hom ⟨λ n => (s.π.app .zero x).val n,λ n => (s.π.app .zero x).property n⟩)
          (GlobalSectionsOne.hom ⟨λ n => (s.π.app .one x).val n,λ n => (s.π.app .one x).property n⟩)
          (by have e := (s.π.naturality .left);aesop_cat)
          (by have e := (s.π.naturality .right);aesop_cat)
        ) ≫ (diagramIsoParallelPair K).inv⟩)
      fac s j := funext $ λ x => Subtype.ext $ funext $ λ n =>
        let fac := cL.fac ⟨ToT.one,
          (diagramIsoParallelPair ((Functor.const WalkingParallelPair).obj ToT.one)).hom ≫ (
          parallelPairHom _ _ _ _
            (GlobalSectionsOne.hom ⟨λ n => (s.π.app .zero x).val n,λ n => (s.π.app .zero x).property n⟩)
            (GlobalSectionsOne.hom ⟨λ n => (s.π.app .one x).val n,λ n => (s.π.app .one x).property n⟩)
            (by have e := (s.π.naturality .left);aesop_cat)
            (by have e := (s.π.naturality .right);aesop_cat)
          ) ≫ (diagramIsoParallelPair K).inv⟩
        match j with
        | .zero => congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) (fac .zero)
        | .one => congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) (fac .one)
      uniq s m mc := funext $ λ x => Subtype.ext $ funext $ λ n =>
        let uniq := cL.uniq ⟨ToT.one,
          (diagramIsoParallelPair ((Functor.const WalkingParallelPair).obj ToT.one)).hom ≫ (
          parallelPairHom _ _ _ _
            (GlobalSectionsOne.hom ⟨λ n => (s.π.app .zero x).val n,λ n => (s.π.app .zero x).property n⟩)
            (GlobalSectionsOne.hom ⟨λ n => (s.π.app .one x).val n,λ n => (s.π.app .one x).property n⟩)
            (by have e := (s.π.naturality .left);aesop_cat)
            (by have e := (s.π.naturality .right);aesop_cat)
          ) ≫ (diagramIsoParallelPair K).inv⟩
          (GlobalSectionsOne.hom (m x)) (by
            intro j
            match j with
            | .zero => simp;rw [<-congrFun (mc .zero) x];congr
            | .one => simp;rw [<-congrFun (mc .one) x];congr
          )
        congrArg (λ ξ => (GlobalSectionsOne.inv ξ).val n) uniq
    }
  }
instance : PreservesFiniteProducts GlobalSectionsF where
  preserves n := preservesShape_fin_of_preserves_binary_and_terminal GlobalSectionsF n
instance GlobalSectionsPreserves : PreservesFiniteLimits GlobalSectionsF :=
 preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts GlobalSectionsF

def GlobalSectionsFL : LexFunctor ToTL SetL := ⟨GlobalSectionsF,GlobalSectionsPreserves⟩


noncomputable section
-- Δ := ToT.ofSet

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

--set_option profiler true
@[aesop safe unfold]
noncomputable instance : PosetalBicategoryOnCategory M0 where
  homPoset := fun
    | .T,.T => by simp[Quiver.Hom];infer_instance
    | .T,.S =>  by simp[Quiver.Hom];infer_instance
    | .S,.T =>  by simp[Quiver.Hom];infer_instance
    | .S,.S =>  by simp[Quiver.Hom];infer_instance
  whiskerLeft := by aesop_cat
  whiskerRight := by aesop_cat

set_option maxHeartbeats 400000
noncomputable def model2Functor : TwoFunctor M0 Lex where
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
  map₂_whisker_left := @fun
    | .T,.T,.T,(),(),(),⟨⟨⟨⟩⟩⟩ => by rfl
    | .T,.T,.S,(),(),(),⟨⟨⟨⟩⟩⟩ => by rfl
    | .T,.S,.S,(),(),(),⟨⟨⟨⟩⟩⟩ => by rfl
    | .S,.S,.S,(),(),(),⟨⟨⟨⟩⟩⟩ => by rfl
  map₂_whisker_right := @fun
    | .T,.T,.T,(),(),⟨⟨⟨⟩⟩⟩,() => by rfl
    | .T,.T,.S,(),(),⟨⟨⟨⟩⟩⟩,() => by rfl
    | .T,.S,.S,(),(),⟨⟨⟨⟩⟩⟩,() => by rfl
    | .S,.S,.S,(),(),⟨⟨⟨⟩⟩⟩,() => by rfl

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

lemma fromTerminalFunctorComp {X : Cat.{v,u}} {Y : Cat.{v,u}} (F : X ⟶ Y) (x : X):
  ((fromTerminalFunctor' X) x) ≫ F = (fromTerminalFunctor' Y) (F.obj x) := by
   obtain ⟨⟨Fo,Fm⟩,Fi,Fc⟩ := F
   simp [fromTerminalFunctor',CategoryStruct.comp,Functor.comp]
   congr
   funext a b f
   apply Fi

def fromTerminalNatTrans {X : Cat.{v,u}} (x y : X):
  (x ⟶ y) ≃ ((fromTerminalFunctor' X) x ⟶ (fromTerminalFunctor' X) y) where
    toFun f := {
      app := fun .unit => f
      naturality := @fun .unit .unit ⟨⟩ => by simp [fromTerminalFunctor']
    }
    invFun η := η.app .unit
    left_inv := by aesop_cat
    right_inv := by aesop_cat

-- This is Γ*
def GlobalSectionsFLF --: (HypF.obj SetL) ⟶ (HypF.obj TotL) -- TODO: type this (universes)
  := (HypF.map (Quiver.Hom.op GlobalSectionsFL))

def Cat.homext {A B : Cat} {F G : A ⟶ B} (eq : ∀ x : A, F.obj x = G.obj x)
  (eqM : ∀ x y : A, ∀ f : x ⟶ y, F.map f = eq x ▸ eq y ▸ G.map f):
  (F = G) := by
    obtain ⟨⟨Fo,Fm⟩,_,_⟩ := F
    obtain ⟨⟨Go,Gm⟩,_,_⟩ := G
    cases show Fo = Go by funext x; exact eq x
    congr
    funext x y f
    exact eqM x y f

def GlobalSectionsRespect : ToT.hyperdoctrine ⟶ GlobalSectionsFLF.obj HypType.hyperdoctrine where
  app X := {
    obj (φ : ToTPred (X.unop)) := λ x => ∀ n, φ.val n (x.val n)
    map {φ ψ : ToTPred (X.unop)} η := .up $ .up $ λ φp x n => η.down.down n (φp.val n) (x n)
  }
  naturality {X Y} f := by
    apply Cat.homext
    · intro x y f'
      rfl
    · intro x
      rfl

noncomputable def natrans : OplaxNatTrans (@toTerminalCategory (Opposite12 M0)).toOplax
    (Pseudofunctor.comp (Pseudofunctor.op12 model2Functor.toPseudofunctor) (Hyp HeytAlg HeytAsCat)).toOplax
    where
      app := fun
        | ⟨.T⟩ => (fromTerminalFunctor' _).toFun ToT.hyperdoctrine
        | ⟨.S⟩ => (fromTerminalFunctor' _).toFun HypType.hyperdoctrine
      naturality := @fun
        | ⟨.S⟩,⟨.S⟩,⟨()⟩ => by
            simp only [toTerminalCategory, Pseudofunctor.toOplax_toPrelaxFunctor,
              Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, unop_op12,
              Equiv.toFun_as_coe, Prefunctor.comp_map]
            rw [(by rfl :
              (Hyp HeytAlg HeytAsCat).map ((Pseudofunctor.op12 model2Functor.toPseudofunctor).map
               (@Opposite.op (M0.S ⟶ M0.S) ())) = 𝟙 _)]
            rw [<-Cat.id_eq_id ⟨PUnit,_⟩]
            rw [@Category.id_comp Cat _ ⟨PUnit,_⟩]
            simp only [Category.comp_id]
            apply CategoryStruct.id
        | ⟨.T⟩,⟨.T⟩,⟨()⟩ => by
            simp only [toTerminalCategory, Pseudofunctor.toOplax_toPrelaxFunctor,
              Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, unop_op12,
              Equiv.toFun_as_coe, Prefunctor.comp_map]
            rw [(by rfl :
              (Hyp HeytAlg HeytAsCat).map ((Pseudofunctor.op12 model2Functor.toPseudofunctor).map
               (@Opposite.op (M0.T ⟶ M0.T) ())) = 𝟙 _)]
            rw [<-Cat.id_eq_id ⟨PUnit,_⟩]
            rw [@Category.id_comp Cat _ ⟨PUnit,_⟩]
            simp only [Category.comp_id]
            apply CategoryStruct.id
        | ⟨.S⟩,⟨.T⟩,⟨()⟩ => by
            simp only [toTerminalCategory, Pseudofunctor.toOplax_toPrelaxFunctor,
              Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, unop_op12,
              Equiv.toFun_as_coe, Prefunctor.comp_map]
            rw [(by rfl :
              (Hyp HeytAlg HeytAsCat).map ((Pseudofunctor.op12 model2Functor.toPseudofunctor).map
               (@Opposite.op (M0.T ⟶ M0.S) ())) = GlobalSectionsFLF)]
            rw [<-Cat.id_eq_id ⟨PUnit,_⟩]
            rw [@Category.id_comp Cat _ ⟨PUnit,_⟩]
            rw [fromTerminalFunctorComp]
            apply (fromTerminalNatTrans ToT.hyperdoctrine (GlobalSectionsFLF.obj HypType.hyperdoctrine)).toFun
            exact GlobalSectionsRespect

end M0
