
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
