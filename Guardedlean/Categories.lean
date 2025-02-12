
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Guardedlean.Lemmas

open CategoryTheory

namespace Guardedlean

section Nat
/--- The Category ℕ ---/

lemma ℕ.catInductionK (P : (a b : ℕ) → (a ⟶ b) → Prop)
  (zero : ∀ a, P a a (𝟙 a))
  (init : ∀ a (f : a ⟶ a+1), P a (a+1) f)
  (comp : ∀ a b c (f : a ⟶ b) (g : b ⟶ c), P a b f → P b c g → P a c (f ≫ g))
  : ∀ k a b (_ : a+k=b) f, P a b f := by {
    apply ℕsumInduction
    intros a b e f
    simp at e; cases e;
    apply zero
    intros a b e f
    cases e
    apply init
    intros a b pa pb x y e f
    cases e
    have f₁ := @makeArrow x (x+a) (by omega)
    have f₂ := @makeArrow (x+a) (x+(a+b)) (by omega)
    specialize pa x (x+a) rfl f₁
    specialize pb (x+a) (x+(a+b)) (by omega) f₂
    have eqf : f = f₁ ≫ f₂ := rfl
    rw [eqf]
    apply comp _ _ _ _ _ pa pb
  }
lemma ℕ.catInduction (P : (a b : ℕ) → (a ⟶ b) → Prop)
  (zero : ∀ a, P a a (𝟙 a))
  (init : ∀ a (f : a ⟶ a+1), P a (a+1) f)
  (comp : ∀ a b c (f : a ⟶ b) (g : b ⟶ c), P a b f → P b c g → P a c (f ≫ g))
  : ∀ a b f, P a b f := by {
    intro a b f
    have feq := unmakeArrow f
    apply ℕ.catInductionK P zero init comp (b-a) a b (by omega) f
  }
end Nat

section BicategoryOnCategory
class BicategoryOnCategory (C : Type u) extends Category C where
  homCategory : (A B : C) → Category (A ⟶ B)
  whiskerLeft {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h
  whiskerRight {a b c : C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h
  whiskerLeft_id : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
    aesop_cat
  whiskerLeft_comp :
    ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
    aesop_cat
  id_whiskerLeft :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerLeft (𝟙 a) η = Eq.symm (id_comp f) ▸ Eq.symm (id_comp g) ▸ η := by aesop_cat
  comp_whiskerLeft :
    ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
      whiskerLeft (f ≫ g) η =
        Eq.symm (assoc f g h) ▸ Eq.symm (assoc f g h') ▸ whiskerLeft f (whiskerLeft g η) := by aesop_cat
  id_whiskerRight : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by aesop_cat
  comp_whiskerRight :
    ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by aesop_cat
  whiskerRight_id :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerRight η (𝟙 b) = Eq.symm (comp_id f) ▸ Eq.symm (comp_id g) ▸ η := by aesop_cat
  whiskerRight_comp :
    ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
      whiskerRight η (g ≫ h) =
        assoc f g h ▸ assoc f' g h ▸ whiskerRight (whiskerRight η g) h
    := by aesop_cat
  whisker_assoc :
    ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
      whiskerRight (whiskerLeft f η) h =
        assoc f g h ▸ assoc f g' h ▸ whiskerLeft f (whiskerRight η h) := by
    aesop_cat
  -- exchange law of left and right whiskerings:
  whisker_exchange :
    ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := by
    aesop_cat


instance (C : Type u) [boc : BicategoryOnCategory C] : Bicategory C where
    homCategory A B := boc.homCategory A B
    whiskerLeft f g h η := boc.whiskerLeft f η
    whiskerRight η h := boc.whiskerRight η h
    associator f g h := @eqToIso _ (boc.homCategory _ _) _ _ (boc.assoc f g h)
    leftUnitor f := @eqToIso _ (boc.homCategory _ _) _ _ (boc.id_comp f)
    rightUnitor f := @eqToIso _ (boc.homCategory _ _) _ _ (boc.comp_id f)
    whiskerLeft_id := boc.whiskerLeft_id
    whiskerLeft_comp := boc.whiskerLeft_comp
    id_whiskerLeft := by
      intros a b f g η
      simp only [eqToIso.hom, eqToIso.inv]
      rw [boc.id_whiskerLeft]
      rw [<-@congrArg_cast_hom_left _ (boc.homCategory a b),<-@congrArg_cast_hom_right _ (boc.homCategory a b)]
      rw [rectocast (λ x => (boc.homCategory a b).Hom x _)]
      rw [rectocast (λ x => (boc.homCategory a b).Hom _ x)]
      exact boc.id_comp g
    comp_whiskerLeft := by
      intros a b c d f g h h' η
      simp only [eqToIso.inv, eqToIso.hom]
      rw [boc.comp_whiskerLeft]
      rw [<-@congrArg_cast_hom_left _ (boc.homCategory a d),<-@congrArg_cast_hom_right _ (boc.homCategory a d)]
      rw [rectocast (λ x => (boc.homCategory a d).Hom x _)]
      rw [rectocast (λ x => (boc.homCategory a d).Hom _ x)]
      exact boc.assoc f g h'
    whiskerRight_id := by
      intros a b f g η
      simp only [eqToIso.hom, eqToIso.inv]
      rw [boc.whiskerRight_id]
      rw [<-@congrArg_cast_hom_left _ (boc.homCategory a b),<-@congrArg_cast_hom_right _ (boc.homCategory a b)]
      rw [rectocast (λ x => (boc.homCategory a b).Hom x _)]
      rw [rectocast (λ x => (boc.homCategory a b).Hom _ x)]
      exact boc.comp_id g
    whiskerRight_comp := by
      intros a b c d f f' η g h
      simp only [eqToIso.inv, eqToIso.hom]
      rw [boc.whiskerRight_comp]
      rw [<-@congrArg_cast_hom_left _ (boc.homCategory a d),<-@congrArg_cast_hom_right _ (boc.homCategory a d)]
      rw [rectocast (λ x => (boc.homCategory a d).Hom x _)]
      rw [rectocast (λ x => (boc.homCategory a d).Hom _ x)]
      exact Eq.symm (boc.assoc f' g h)
    id_whiskerRight := boc.id_whiskerRight
    comp_whiskerRight := boc.comp_whiskerRight
    whisker_exchange := boc.whisker_exchange
    whisker_assoc := by
      intros a b c d f g g' η h
      simp only [eqToIso.inv, eqToIso.hom]
      rw [boc.whisker_assoc]
      unfold eqToHom Eq.mpr
      rw [rectocast (λ x => (boc.homCategory a d).Hom x _)]
      rw [rectocast (λ x => (boc.homCategory a d).Hom _ x)]
      rw [rectocast (λ x => x)]
      rw [rectocast (λ x => x)]
      simp only [Category.assoc, congrArg_cast_hom_right, congrArg_cast_hom_left, Category.comp_id]
    pentagon := by
      intros a b c d e f g h i
      simp only [eqToIso.hom, eqToHom_trans]
      unfold eqToHom Eq.mpr
      repeat rw [rectocast (λ x => x)]
      have e1 := @cast_poly2 (a ⟶ d) (f ≫ g ≫ h) ((f ≫ g) ≫ h)
        (λ ξ => (boc.homCategory a d).Hom ξ (f ≫ g ≫ h))
        (λ ξ => (boc.homCategory a e).Hom (ξ ≫ i) ((f ≫ g ≫ h) ≫ i))
        (λ {ξ} η => boc.whiskerRight η i) (Eq.symm (boc.assoc f g h)) ((boc.homCategory a d).id _)
      repeat rw [rectocast (λ x => x)] at e1
      rw [e1]
      rw [boc.id_whiskerRight]
      have e2 := @cast_poly2 (b ⟶ e) (g ≫ h ≫ i) ((g ≫ h) ≫ i)
        (λ ξ => (boc.homCategory b e).Hom ξ (g ≫ h ≫ i))
        (λ ξ => (boc.homCategory a e).Hom (f ≫ ξ) (f ≫ g ≫ h ≫ i))
        (λ {ξ} η => boc.whiskerLeft f η) (Eq.symm (boc.assoc g h i)) ((boc.homCategory b e).id (g≫h≫i))
      repeat rw [rectocast (λ x => x)] at e2
      rw [e2]
      rw [boc.whiskerLeft_id]
      simp only [Category.assoc, congrArg_cast_hom_left, Category.comp_id, eqToHom_trans]
    triangle := by
      intros a b c f g
      simp only [eqToIso.hom]
      unfold eqToHom Eq.mpr
      repeat rw [rectocast (λ x => x)]
      have e1 := @cast_poly2 (b ⟶ c) g (𝟙 b ≫ g)
        (λ ξ => (boc.homCategory b c).Hom ξ g)
        (λ ξ => (boc.homCategory a c).Hom (f ≫ ξ) (f ≫ g))
        (λ {ξ} η => boc.whiskerLeft f η) (Eq.symm (boc.id_comp g)) ((boc.homCategory b c).id g)
      repeat rw [rectocast (λ x => x)] at e1
      rw [e1]
      rw [boc.whiskerLeft_id]
      have e2 := @cast_poly2 (a ⟶ b) f (f ≫ 𝟙 b)
        (λ ξ => (boc.homCategory a b).Hom ξ f)
        (λ ξ => (boc.homCategory a c).Hom (ξ ≫ g) (f ≫ g))
        (λ {ξ} η => boc.whiskerRight η g) (Eq.symm (boc.comp_id f)) ((boc.homCategory a b).id f)
      repeat rw [rectocast (λ x => x)] at e2
      rw [e2]
      rw [boc.id_whiskerRight]
      simp only [Category.comp_id, Category.id_comp, congrArg_cast_hom_left, eqToHom_trans]


instance (C : Type u)
  [boc : BicategoryOnCategory C]
  : Bicategory.Strict C where

end BicategoryOnCategory
