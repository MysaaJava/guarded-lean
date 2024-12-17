import Mathlib.CategoryTheory.Types
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction

/-!
# Mate 2-morphism in a Bicategory

TODO make explanation of mates

## Main definitions

* `Bicategory.Mate`: equivalence between the left homset and the right homset
* `Bicategory.Mate.left`: the left mate of a right adjoints adjunction pair
* `Bicategory.Mate.right`: the right mate of a left adjoints adjunction pair

# TODO
Copy file structure and proofs from .lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Mates.lean
-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

def Mate.left {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I)
    (η : (f ≫ k) ⟶ (g ≫ h)) : (k ≫ h') ⟶ (f' ≫ g) :=
        (λ_ (k ≫ h')).inv ⊗≫
        (fAdj.unit) ▷ (k ≫ h') ⊗≫
        f' ◁ η ▷ h' ⊗≫
        (f' ≫ g) ◁ (hAdj.counit) ⊗≫
        (ρ_ (f' ≫ g)).hom

def Mate.right {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I)
    (ε : (k ≫ h') ⟶ (f' ≫ g)) : (f ≫ k) ⟶ (g ≫ h) :=
        (ρ_ (f ≫ k)).inv ⊗≫
        (f ≫ k) ◁ (hAdj.unit) ⊗≫
        f ◁ ε ▷ h ⊗≫
        (fAdj.counit) ▷ (g ≫ h) ⊗≫
        (λ_ (g ≫ h)).hom


def Mate {C : Type u} [Bicategory.{v} C] {L J K I : C}
    {f' : K ⟶ L} {f : L ⟶ K} (fAdj : Bicategory.Adjunction f' f)
    {h' : I ⟶ J} {h : J ⟶ I} (hAdj : Bicategory.Adjunction h' h)
    (g : L ⟶ J) (k : K ⟶ I) :
    Iso ((Bicategory.homCategory L I).Hom (f ≫ k) (g ≫ h)) ((Bicategory.homCategory K J).Hom (k ≫ h') (f' ≫ g)) where
        hom η := Mate.left fAdj hAdj g k η
        inv ε := Mate.right fAdj hAdj g k ε
        hom_inv_id := by {
          funext X
          simp only [Mate.left,Mate.right,types_comp_apply]
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
          trans
              X ⊗≫
              g ◁ (rightZigzag hAdj.unit hAdj.counit) ⊗≫
              g ◁ (λ_ h).hom
          bicategory
          rw [hAdj.right_triangle]
          simp only [whiskerLeft_rightUnitor_inv, Bicategory.Adjunction.right_triangle,
            Bicategory.whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc, types_id_apply]
          bicategory
        }
        inv_hom_id := by {
          funext X
          simp only [Mate.left,Mate.right,types_comp_apply]
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

end Bicategory

end CategoryTheory
