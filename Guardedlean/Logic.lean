import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Bicategory.Adjunction
import Mathlib.CategoryTheory.Bicategory.Basic
import Guardedlean.Lemmas
import Guardedlean.CategoryTheory.«Bicategory.Mate»

open CategoryTheory
open CategoryTheory.Bicategory

namespace Guardedlean

class PreHyperdoctrine (C : Type u₁) [Bicategory.{v₁} C] (T : Type u₂) [Category.{v₂} T] where
  -- P : Tᵒᵖ ⥤ C
  -- Cannot use functor as C is a bicategory => CategoryStruct, and not a Category
  P : Prefunctor Tᵒᵖ C
  P_map_id : ∀ X : Tᵒᵖ, P.map (𝟙 X) = 𝟙 (P.obj X) := by aesop_cat
  P_map_comp : ∀ {X Y Z : Tᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z), P.map (f ≫ g) = P.map f ≫ P.map g := by aesop_cat

  leftAdj {A B : T} (f : A ⟶ B) : P.obj ⟨A⟩ ⟶ P.obj ⟨B⟩
  leftAdjunction {A B : T} (f : A ⟶ B) : Bicategory.Adjunction (leftAdj f) (P.map ⟨f⟩)

  rightAdj {A B : T} (f : A ⟶ B) : P.obj ⟨A⟩ ⟶ P.obj ⟨B⟩
  rightAdjunction {A B : T} (f : A ⟶ B) : Bicategory.Adjunction (P.map ⟨f⟩) (rightAdj f)

class Hyperdoctrine (C : Type u₁) [Bicategory.{v₁} C] (T : Type u₂) [Category.{v₂} T]
  extends PreHyperdoctrine C T where
  hflC : True
  -- Frobenius :


  --beck-chevalley : The right/left mate is inversible
  leftBeckChevalley (L J K I : T) (f : K ⟶ L) (g : J ⟶ L) (k : I ⟶ K) (h : I ⟶ J)
      (η : (Bicategory.homCategory (P.obj ⟨L⟩) (P.obj ⟨I⟩)).Hom ((P.map ⟨f⟩) ≫ (P.map ⟨k⟩)) ((P.map ⟨g⟩) ≫ (P.map ⟨h⟩)))
     : IsIso (Mate.left (leftAdjunction f) (leftAdjunction h) (P.map ⟨g⟩) (P.map ⟨k⟩) η)

  rightBeckChevalley (L J K I : T) (f : K ⟶ L) (g : J ⟶ L) (k : I ⟶ K) (h : I ⟶ J)
      (ε : (Bicategory.homCategory (P.obj ⟨L⟩) (P.obj ⟨I⟩)).Hom ((P.map ⟨f⟩) ≫ (P.map ⟨k⟩)) ((P.map ⟨g⟩) ≫ (P.map ⟨h⟩)))
     : IsIso (Mate.right (rightAdjunction g) (rightAdjunction k) (P.map ⟨h⟩) (P.map ⟨f⟩) ε)
