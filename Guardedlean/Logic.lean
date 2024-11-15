import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Basic
import Guardedlean.Lemmas
import Guardedlean.CategoryTheory.«Bicategory.Mate»

open CategoryTheory
open CategoryTheory.Bicategory

namespace Guardedlean

class Hyperdoctrine (C : Type u₁) [Bicategory.{v₁} C] (T : Type u₂) [Category.{v₂} T] where

  -- P : Tᵒᵖ ⥤ C
  -- Cannot use functor as C is a bicategory => CategoryStruct, and not a Category
  P : Prefunctor Tᵒᵖ C
  P_map_id : ∀ X : Tᵒᵖ, P.map (𝟙 X) = 𝟙 (P.obj X) := by aesop_cat
  P_map_comp : ∀ {X Y Z : Tᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z), P.map (f ≫ g) = P.map f ≫ P.map g := by aesop_cat

  -- Adjunctions
  leftAdj {A B : T} (f : A ⟶ B) : P.obj ⟨A⟩ ⟶ P.obj ⟨B⟩
  leftAdjunction {A B : T} (f : A ⟶ B) : Bicategory.Adjunction (leftAdj f) (P.map ⟨f⟩)
  rightAdj {A B : T} (f : A ⟶ B) : P.obj ⟨A⟩ ⟶ P.obj ⟨B⟩
  rightAdjunction {A B : T} (f : A ⟶ B) : Bicategory.Adjunction (P.map ⟨f⟩) (rightAdj f)

  -- Beck-Chevalley property : The right/left mate of an identity from a pullback is inversible
  leftBeckChevalley (L J K : T) (f : K ⟶ L) (g : J ⟶ L) (pb : Limits.LimitCone (Limits.cospan f g)):
     let k := pb.cone.π.app .left;let h := pb.cone.π.app .right;
     let id : P.map (.op f) ≫ P.map (.op k) ⟶ P.map (.op g) ≫ P.map (.op h)
        := (P_map_comp f.op k.op) ▸ (P_map_comp g.op h.op) ▸
        cast (congrArg (fun ξ => P.map (f.op ≫ k.op) ⟶ P.map ξ.op) (Limits.PullbackCone.condition pb.cone)) (𝟙 (P.map (f.op ≫ k.op)))
     IsIso (Mate.left (leftAdjunction f) (leftAdjunction h) (P.map ⟨g⟩) (P.map ⟨k⟩) id)

  rightBeckChevalley (L J K : T) (f : K ⟶ L) (g : J ⟶ L) (pb : Limits.LimitCone (Limits.cospan f g)):
     let k := pb.cone.π.app .left;let h := pb.cone.π.app .right;
     let id : P.map (.op f) ≫ P.map (.op k) ⟶ P.map (.op g) ≫ P.map (.op h)
        := (P_map_comp f.op k.op) ▸ (P_map_comp g.op h.op) ▸
        cast (congrArg (fun ξ => P.map (f.op ≫ k.op) ⟶ P.map ξ.op) (Limits.PullbackCone.condition pb.cone)) (𝟙 (P.map (f.op ≫ k.op)))
     IsIso (Mate.right (rightAdjunction g) (rightAdjunction k) (P.map ⟨h⟩) (P.map ⟨f⟩) id)

/-
(0) T has finite products and terminal object 1,
=> T is Cartesian

(5') for each t : X --+ Y in T, t* has adjoints
=> We have the adjunction ∀f ⊢ P(f) ⊢ ∃f in C for every morphism f of T
(5'') then the morphism Z,t*rp 3 t ‘ * & p is an isomorphism
=> Beck-Chevalley

(1) P is an indexed category over T (“a T-category”) <=> P : Tᵒᵖ ⟶ Cat
=> P : Tᵒᵖ ⟶ C, and Objects of C are Categories & 1-morphisms of C are functors <=> C is sub-bicategory of Cat
(2) for each object X of T, the fibre P ( X ) is Cartesian closed, and furthermore,
=> Objects of C are Cartesian Closed
(3) has finite coproducts and an initial object O x ,
=> Objects of C are complete categories
(4)for each morphism t of T, the “inverse image’.’ functor t* preserves the structure of (2),(3)
=> 1-morphisms of C preserve the structures
|---> C is a sub-bicategory of complete categories

-/
