import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Order.Category.HeytAlg
import Guardedlean.Logic
import Guardedlean.CategoryTheory.Lex
import Guardedlean.CategoryTheory.Bicategory.Opposite

open CategoryTheory

namespace Guardedlean

def Hyp (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{v₂,u₂})
   : Pseudofunctor (Opposite1 Lex.{v₃,u₃}) Cat.{v₂,u₂} where
     obj := sorry
     map := sorry
     map₂ := sorry
     mapId := sorry
     mapComp := sorry


def Hyp (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{v₂,u₂})
   : Pseudofunctor (Opposite1 Lex.{v₃,u₃}) Cat.{v₂,u₂} where
  obj T := Bundled.mk (Hyperdoctrine C u T.unop1)
  map {T U} F := {
    obj := λ P => HyperdoctrineFunctor C u T.unop1 U.unop1 F.unop1
    map := sorry
  }

/-
-- TODO Hyperdoctrine is not most generic as Beck-Chevalley is asked on every pullback instead of
-- only on a specific class of them
class CatHyperdoctrine (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat) (T : Type u₂) [Category.{v₂} T] where

  F : Catᵒᵖ ⥤ Cat
  F :

  -- Adjunctions
  leftAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  leftAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (leftAdj f) (u.map (P.map ⟨f⟩))
  rightAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  rightAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (u.map (P.map ⟨f⟩)) (rightAdj f)

  -- Beck-Chevalley property : The right/left mate of an identity from a pullback is inversible
  -- id is casted id as k ≫ f = h ≫ g
  leftBeckChevalley (L J K : T) (f : K ⟶ L) (g : J ⟶ L) (pb : Limits.LimitCone (Limits.cospan f g)):
     let k := pb.cone.π.app .left;let h := pb.cone.π.app .right;
     let id : u.map (P.map (.op f)) ≫ u.map (P.map (.op k)) ⟶ u.map (P.map (.op g)) ≫ u.map (P.map (.op h))
        := ((Functor.comp P u).map_comp f.op k.op) ▸ ((Functor.comp P u).map_comp g.op h.op) ▸
        cast (congrArg (fun ξ => (P ⋙ u).map (f.op ≫ k.op) ⟶ (P ⋙ u).map ξ.op) (Limits.PullbackCone.condition pb.cone)) (𝟙 ((Functor.comp P u).map (f.op ≫ k.op)))
     IsIso ((mateEquiv (leftAdjunction f) (leftAdjunction h)).invFun id)

  rightBeckChevalley (L J K : T) (f : K ⟶ L) (g : J ⟶ L) (pb : Limits.LimitCone (Limits.cospan f g)):
     let k := pb.cone.π.app .left;let h := pb.cone.π.app .right;
     let id : u.map (P.map (.op f)) ≫ u.map (P.map (.op k)) ⟶ u.map (P.map (.op g)) ≫ u.map (P.map (.op h))
        := ((P ⋙ u).map_comp f.op k.op) ▸ ((P ⋙ u).map_comp g.op h.op) ▸
        cast (congrArg (fun ξ => (P ⋙ u).map (f.op ≫ k.op) ⟶ (P ⋙ u).map ξ.op) (Limits.PullbackCone.condition pb.cone)) (𝟙 ((P ⋙ u).map (f.op ≫ k.op)))
     IsIso ((mateEquiv (rightAdjunction g) (rightAdjunction k)).toFun id)
-/
