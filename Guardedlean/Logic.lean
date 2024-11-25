import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Order.Category.HeytAlg

open CategoryTheory

namespace Guardedlean

-- TODO Hyperdoctrine is not most generic as Beck-Chevalley is asked on every pullback instead of
-- only on a specific class of them
class Hyperdoctrine (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat) (T : Type u₂) [Category.{v₂} T] where

  P : Tᵒᵖ ⥤ C

  -- Adjunctions
  leftAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  leftAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (leftAdj f) (u.map (P.map ⟨f⟩))
  rightAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  rightAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (u.map (P.map ⟨f⟩)) (rightAdj f)

  -- Beck-Chevalley property : The right/left mate of an identity from a pullback is inversible
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

instance : HasForget₂ HeytAlg Preord :=
   let _ := HasForget₂.trans HeytAlg BddDistLat DistLat
   let _ := HasForget₂.trans HeytAlg DistLat Lat
   let _ := HasForget₂.trans HeytAlg Lat PartOrd
   HasForget₂.trans HeytAlg PartOrd Preord

abbrev FirstOrderHyperdoctrine (T : Type u) [Category.{v} T] :=
   Hyperdoctrine HeytAlg (forget₂ HeytAlg Preord ⋙ preordToCat) T
