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

private def rightMate {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I)
    (η : (Bicategory.homCategory L I).Hom (f ≫ k) (g ≫ h)) :
    (Bicategory.homCategory K J).Hom (k ≫ h') (f' ≫ g) :=
        (Bicategory.leftUnitor (k ≫ h')).inv ≫
        (Bicategory.whiskerRight (fAdj.unit) (k ≫ h')) ≫
        ((Bicategory.associator f' f (k ≫ h')).hom) ≫
        (Bicategory.whiskerLeft f' (Bicategory.associator f k h').inv) ≫
        (Bicategory.whiskerLeft f' (Bicategory.whiskerRight η h')) ≫
        (Bicategory.whiskerLeft f' (Bicategory.associator g h h').hom) ≫
        ((Bicategory.associator f' g (h ≫ h')).inv) ≫
        (Bicategory.whiskerLeft (f' ≫ g) (hAdj.counit)) ≫
        ((Bicategory.rightUnitor (f' ≫ g)).hom)

private def leftMate {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I)
    (ε : (Bicategory.homCategory K J).Hom (k ≫ h') (f' ≫ g)) :
    (Bicategory.homCategory L I).Hom (f ≫ k) (g ≫ h) :=
        ((Bicategory.rightUnitor (f ≫ k)).inv) ≫
        (Bicategory.whiskerLeft (f ≫ k) (hAdj.unit)) ≫
        ((Bicategory.associator f k (h' ≫ h)).hom) ≫
        (Bicategory.whiskerLeft f (Bicategory.associator k h' h).inv) ≫
        (Bicategory.whiskerLeft f (Bicategory.whiskerRight ε h)) ≫
        (Bicategory.whiskerLeft f (Bicategory.associator f' g h).hom) ≫
        ((Bicategory.associator f f' (g ≫ h)).inv) ≫
        (Bicategory.whiskerRight (fAdj.counit) (g ≫ h)) ≫
        (Bicategory.leftUnitor (g ≫ h)).hom



def mate {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I) :
    (Bicategory.homCategory L I).Hom (f ≫ k) (g ≫ h) ≅ (Bicategory.homCategory K J).Hom (k ≫ h') (f' ≫ g) where
        hom η := rightMate fAdj hAdj g k η
        inv ε := leftMate fAdj hAdj g k ε
        hom_inv_id := by {
          funext X
          simp only [leftMate,rightMate,types_comp_apply]
          trans
              (ρ_ (f ≫ k)).inv ⊗≫
              (f ≫ k) ◁ hAdj.unit ⊗≫
              f ◁ fAdj.unit ▷ (k ≫ h' ≫ h) ⊗≫
              ((f ≫ f') ◁ (X ▷ (h' ≫ h) ⊗≫ g ◁ hAdj.counit ▷ h) ≫
              fAdj.counit ▷ (g ≫ 𝟙 J ≫ h)) ⊗≫
              g ◁ (λ_ h).hom
          bicategory
          trans
              (ρ_ (f ≫ k)).inv ⊗≫
              (f ≫ k) ◁ hAdj.unit ⊗≫
              (rightZigzag fAdj.unit fAdj.counit) ▷ (k ≫ h' ≫ h) ⊗≫
              X ▷ (h' ≫ h) ⊗≫
              g ◁ hAdj.counit ▷ h ⊗≫
              g ◁ (λ_ h).hom
          rw [whisker_exchange fAdj.counit (X ▷ (h' ≫ h) ⊗≫ g ◁ hAdj.counit ▷ h)]
          bicategory
          rw [fAdj.right_triangle]
          trans
              (ρ_ (f ≫ k)).inv ⊗≫
              ((f ≫ k) ◁ hAdj.unit ≫ X ▷ (h' ≫ h)) ⊗≫
              g ◁ hAdj.counit ▷ h ⊗≫
              g ◁ (λ_ h).hom
          bicategory
          rw [whisker_exchange X hAdj.unit]
          simp only [whiskerLeft_rightUnitor_inv, Bicategory.Adjunction.right_triangle,
            Bicategory.whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, types_id_apply]
          bicategory
        }
        inv_hom_id := by {
          funext X
          simp only [leftMate,rightMate,types_comp_apply]
          trans
            (λ_ (k ≫ h')).inv ⊗≫
            fAdj.unit ▷ (k ≫ h') ⊗≫
            (f' ≫ f) ◁ (k ◁ hAdj.unit ▷ h') ⊗≫
            ((f' ◁ (f ◁ X ⊗≫ fAdj.counit ▷ g)) ▷ (h ≫ h') ≫
            (f' ≫ 𝟙 L ≫ g) ◁ hAdj.counit) ⊗≫
            (ρ_ (f' ≫ g)).hom
          bicategory
          rw [<-whisker_exchange (f' ◁ (f ◁ X ⊗≫ fAdj.counit ▷ g)) hAdj.counit]
          trans
            (λ_ (k ≫ h')).inv ⊗≫
            fAdj.unit ▷ (k ≫ h') ⊗≫
            (f' ≫ f ≫ k) ◁ (leftZigzag hAdj.unit hAdj.counit) ⊗≫
            f' ◁ f ◁ X ⊗≫
            f' ◁ fAdj.counit ▷ g ⊗≫
            (ρ_ (f' ≫ g)).hom
          bicategory
          rw [hAdj.left_triangle]
          trans
            (λ_ (k ≫ h')).inv ⊗≫
            (fAdj.unit ▷ (k ≫ h') ≫ (f' ≫ f) ◁ X) ⊗≫
            f' ◁ fAdj.counit ▷ g ⊗≫
            (ρ_ (f' ≫ g)).hom
          bicategory
          rw [<-whisker_exchange fAdj.unit X]
          trans
            X ⊗≫
            (leftZigzag fAdj.unit fAdj.counit) ▷ g ⊗≫
            f' ◁ (ρ_ g).hom
          bicategory
          rw [fAdj.left_triangle]
          simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc,
            whiskerLeft_rightUnitor, types_id_apply]
          bicategory
        }



class Hyperdoctrine (C : Type u₁) [Bicategory.{v₁} C] (T : Type u₂) [Category.{v₂} T]
  extends PreHyperdoctrine C T where
  hflC : True
  -- Frobenius :


  --beck-chevalley
  -- for every pullback in C : J --f--> I <--g-- K // J <--p-- . --q--> K
  -- for every φ ∈ P(J)
  leftBeckChevalley (L J K I : T) (f : K ⟶ L) (g : J ⟶ L) (k : I ⟶ K) (h : I ⟶ J)
      (η : (Bicategory.homCategory (P.obj ⟨L⟩) (P.obj ⟨I⟩)).Hom ((P.map ⟨f⟩) ≫ (P.map ⟨k⟩)) ((P.map ⟨g⟩) ≫ (P.map ⟨h⟩)))
     : IsIso (rightMate (leftAdjunction f) (leftAdjunction h) (P.map ⟨g⟩) (P.map ⟨k⟩) η)

  --
