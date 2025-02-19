
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
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

section PosetalBicategoryOnCategory
class PosetalBicategoryOnCategory (C : Type u) extends Category C where
  homPoset (A B : C) : Preorder (A ⟶ B)
  whiskerLeft {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≤ h) : (f ≫ g) ≤ (f ≫ h)
  whiskerRight {a b c : C} {f g : a ⟶ b} (η : f ≤ g) (h : b ⟶ c) : (f ≫ h) ≤ (g ≫ h)

instance (C : Type u) [pboc : PosetalBicategoryOnCategory C]: Bicategory C where
  toCategoryStruct := pboc.toCategoryStruct
  homCategory A B := (pboc.homPoset A B).smallCategory
  whiskerLeft f g h η := ⟨⟨pboc.whiskerLeft f η.down.down⟩⟩
  whiskerRight η h := ⟨⟨pboc.whiskerRight η.down.down h⟩⟩
  associator f g h := @eqToIso _ (pboc.homPoset _ _).smallCategory _ _ (pboc.assoc f g h)
  leftUnitor f := @eqToIso _ (pboc.homPoset _ _).smallCategory _ _ (pboc.id_comp f)
  rightUnitor f := @eqToIso _ (pboc.homPoset _ _).smallCategory _ _ (pboc.comp_id f)

instance (C : Type u) [pboc : PosetalBicategoryOnCategory C] : Bicategory.Strict C where

class PseudofunctorFromPosetalOnCategoryToStrictBicategory
  (C : Type u) [pboc : PosetalBicategoryOnCategory C]
  (D : Type v) [bd : Bicategory D] [bsd : Bicategory.Strict D]
  extends Functor C D where
  map₂ {A B : C} {f g : A ⟶ B} (e : (pboc.homPoset A B).le f g) : map f ⟶ map g
  map₂_id {A B : C} (f : A ⟶ B) : map₂ ((pboc.homPoset A B).le_refl f) = 𝟙 (map f)
    := by aesop_cat
  map₂_comp {A B : C} {f g h : A ⟶ B} (e₁ : (pboc.homPoset A B).le f g)
   (e₂ : (pboc.homPoset A B).le g h):
   map₂ ((pboc.homPoset A B).le_trans _ _ _ e₁ e₂) = (map₂ e₁) ≫ (map₂ e₂)
    := by aesop_cat
  map₂_whisker_left {A B B': C} {f : A ⟶ B} {g h : B ⟶ B'}
    (e : (pboc.homPoset B B').le g h)
    : map₂ (pboc.whiskerLeft f e) =
    cast (Eq.symm (congrArg (λ ξ => ξ ⟶ map (f ≫ h)) (map_comp f g))) (
    cast (Eq.symm (congrArg (λ ξ => (map f) ≫ (map g) ⟶ ξ) (map_comp f h))) (
    (bd.whiskerLeft (map f) (map₂ e))))
    := by aesop_cat
  map₂_whisker_right {A B B': C} {f g: A ⟶ B} {h : B ⟶ B'}
    (e : (pboc.homPoset A B).le f g)
    : map₂ (pboc.whiskerRight e h) =
    cast (Eq.symm (congrArg (λ ξ => ξ ⟶ map (g ≫ h)) (map_comp f h))) (
    cast (Eq.symm (congrArg (λ ξ => (map f) ≫ (map h) ⟶ ξ) (map_comp g h))) (
    (bd.whiskerRight (map₂ e) (map h))))
    := by aesop_cat

/-
def PosetalBicategoryOnCategory.mkPseudofunctor
  (C : Type u) [pboc : PosetalBicategoryOnCategory C]
  (D : Type u) [bd : Bicategory D] [bds : Bicategory.Strict D]
  (F : PseudofunctorFromPosetalOnCategoryToStrictBicategory C D)
  : Pseudofunctor C D where
    obj x := F.obj x
    map f := F.map f
    map₂ P := F.map₂ P.down.down
    mapId x := eqToIso (F.map_id x)
    mapComp f g := eqToIso (F.map_comp f g)
    map₂_id f := F.map₂_id f
    map₂_comp f g := F.map₂_comp f g
    map₂_whisker_left := F.map₂_whisker_left
    map₂_whisker_right := F.map₂_whisker_right
    map₂_associator {a b c d} f g h := by
      rw [bds.associator_eqToIso (F.map f) (F.map g) (F.map h)]
      simp
      --unfold eqToHom Eq.mpr Bicategory.associator instBicategoryOfPosetalBicategoryOnCategory
      --unfold Preorder.smallCategory
      have e
        := @cast_poly2 (a ⟶ d) ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
        (λ ξ => ((f ≫ g) ≫ h) ⟶ ξ)
        (λ ξ => (F.map ((f ≫ g) ≫ h)) ⟶ (F.map ξ))
        (λ {ξ} η => F.map₂ η.down.down) (Category.assoc f g h) (𝟙 ((f ≫ g) ≫ h))
      rw [rectocast (λ x => x)] at e
      rw [rectocast (λ x => x)] at e
      unfold eqToHom Eq.mpr
      rw [rectocast (λ x => x)]
      rw [e]
      rw [F.map₂_id]
      simp only [Functor.map_comp, Category.assoc, congrArg_cast_hom_right, eqToHom_naturality,
        Category.comp_id, congrArg_cast_hom_left]
-/

end PosetalBicategoryOnCategory

section TwoFunctor
open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃
variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C] [Bicategory.Strict C]


structure TwoFunctor (B : Type u₁) [Bicategory.{w₁,v₁} B] [Bicategory.Strict B]
 (C : Type u₂) [Bicategory.{w₂,v₂} C] [bsd : Bicategory.Strict C]
  extends PrelaxFunctor B C where
  map_id (a : B) : map (𝟙 a) = 𝟙 (obj a) := by aesop_cat
  map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) = map f ≫ map g := by aesop_cat
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) =
        cast (congrArg (λ ξ => ξ ⟶ (map (f ≫ h))) (Eq.symm (map_comp f g)))
        (cast (congrArg (λ ξ => map f ≫ map g ⟶ ξ) (Eq.symm (map_comp f h)))
         (map f ◁ map₂ η)) := by aesop_cat
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) =
      cast (congrArg (λ ξ => ξ ⟶ (map (g ≫ h))) (Eq.symm (map_comp f h)))
      (cast (congrArg (λ ξ => map f ≫ map h ⟶ ξ) (Eq.symm (map_comp g h)))
        (map₂ η ▷ map h)) := by aesop_cat

initialize_simps_projections TwoFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace TwoFunctor
attribute [simp, reassoc, to_app] map₂_whisker_left map₂_whisker_right

set_option maxHeartbeats 300000
def toPseudofunctor (F : TwoFunctor B C) : Pseudofunctor B C where
  obj := F.obj
  map := F.map
  map₂ := F.map₂
  mapId a := eqToIso (F.map_id a)
  mapComp f g := eqToIso (F.map_comp f g)

  map₂_whisker_left {a b c} f {g h} η := by
    simp only [map₂_whisker_left, cast_cast, eqToIso.hom, eqToIso.inv]
    rw [conj_eqToHom_iff_heq']
    apply cast_heq
  map₂_whisker_right {a b c} {f g} η h := by
    simp only [map₂_whisker_right, cast_cast, eqToIso.hom, eqToIso.inv]
    rw [conj_eqToHom_iff_heq']
    apply cast_heq
  map₂_associator {a b c d} f g h := by
    repeat rw [Strict.associator_eqToIso]
    simp only [eqToIso.hom, eqToHom_whiskerRight, eqToIso.inv, whiskerLeft_eqToHom, eqToHom_trans]
    unfold eqToHom Eq.mpr
    repeat rw [rectocast (λ x => x)]
    have e := @cast_poly2 (a ⟶ d) (f ≫ g ≫ h) ((f ≫ g) ≫ h)
        (λ ξ => ξ ⟶ (f ≫ g ≫ h)) (λ ξ => F.map ξ ⟶ F.map (f ≫ g ≫ h))
        (λ ξ => F.map₂ ξ) (Eq.symm (Strict.assoc f g h)) (𝟙 (f ≫ g ≫ h))
    repeat rw [rectocast (λ x => x)] at e
    rw [e,F.map₂_id]
  map₂_left_unitor {a b} f := by
    repeat rw [Strict.leftUnitor_eqToIso]
    simp only [eqToIso.hom, eqToHom_whiskerRight, eqToHom_trans]
    unfold eqToHom Eq.mpr
    repeat rw [rectocast (λ x => x)]
    have e := @cast_poly2 (a ⟶ b) f (𝟙 a ≫ f)
        (λ ξ => ξ ⟶ f) (λ ξ => F.map ξ ⟶ F.map f)
        (λ ξ => F.map₂ ξ) (Eq.symm (Strict.id_comp f)) (𝟙 f)
    repeat rw [rectocast (λ x => x)] at e
    rw [e,F.map₂_id]
  map₂_right_unitor {a b} f := by
    repeat rw [Strict.rightUnitor_eqToIso]
    simp only [eqToIso.hom, whiskerLeft_eqToHom, eqToHom_trans]
    unfold eqToHom Eq.mpr
    repeat rw [rectocast (λ x => x)]
    have e := @cast_poly2 (a ⟶ b) f (f ≫ 𝟙 b)
        (λ ξ => ξ ⟶ f) (λ ξ => F.map ξ ⟶ F.map f)
        (λ ξ => F.map₂ ξ) (Eq.symm (Strict.comp_id f)) (𝟙 f)
    repeat rw [rectocast (λ x => x)] at e
    rw [e,F.map₂_id]

end TwoFunctor
