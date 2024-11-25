import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Guardedlean.Logic
import Guardedlean.ToT.Later

universe u
namespace Guardedlean

def ToTPred (Γ : ToT) : Type u
  := {φ : (n : Nat) → (γ : Γ.set n) → Prop // ∀ n γ, φ (n+1) γ → φ n (Γ.restrict n γ)}

def ToTPred.iterProp (Γ : ToT) (φ : ToTPred Γ) (n k m : ℕ) (e : n + k = m) (γ : Γ.set m)
  : φ.val m γ → φ.val n (Γ.iterRestrict n k m e γ) := by {
    induction k generalizing n m γ
    case zero =>
      simp only [add_zero] at e; subst e
      simp only [ToT.iterRestrictZero, imp_self]
    case succ k₀ hk =>
      intro p
      rw [Γ.iterRestrictCast n n (k₀ + 1) (1 + k₀) m m rfl (by omega) rfl]
      simp only
      rw [<-ToT.iterRestrictComp Γ (n+k₀) m n 1 k₀ (by omega) (by omega)]
      subst e
      rw [Γ.iterRestrictCast (n+k₀) (n+k₀) 1 1 (n+(k₀+1)) (n+k₀+1) rfl rfl (by omega)]
      rw [ToT.iterRestrictOne Γ (n+k₀)]
      simp only
      apply hk n (n+k₀) rfl (Γ.restrict (n + k₀) γ)
      apply φ.prop
      exact p
  }

instance (Γ : ToT) : LE (ToTPred Γ) where
  le φ ψ := ∀ n γ, (φ.val n γ) → (ψ.val n γ)

instance (Γ : ToT) : HeytingAlgebra (ToTPred Γ) where
  le φ ψ := ∀ n γ, (φ.val n γ) → (ψ.val n γ)
  le_refl := by simp only [imp_self, implies_true]
  le_trans φ ψ ξ a b n γ p := b n γ (a n γ p)
  le_antisymm φ ψ a b := by {
    apply Subtype.ext
    funext n γ
    exact propext ⟨a n γ,b n γ⟩ -- (a <-> b) <-> (a = b)
  }
  sup φ ψ := {
    val := λ n γ => φ.val n γ ∨ ψ.val n γ
    property := λ n γ p => Or.rec (λ x => .inl (φ.property n γ x)) (λ x => .inr (ψ.property n γ x)) p
  }
  le_sup_left φ ψ n γ a := .inl a
  le_sup_right φ ψ n γ a := .inr a
  sup_le φ ψ ξ a b n γ p := Or.rec (λ x => a n γ x) (λ x => b n γ x) p
  inf φ ψ := {
    val := λ n γ => φ.val n γ ∧ ψ.val n γ
    property := by
      intro n γ
      simp
      intro  p q
      constructor
      . exact φ.property n γ p
      . exact ψ.property n γ q
  }
  inf_le_left φ ψ n γ p := p.left
  inf_le_right φ ψ n γ p := p.right
  le_inf φ ψ ξ a b n γ p := ⟨a n γ p, b n γ p⟩
  top := {
    val := λ n γ => true
    property := by
      intro n _
      simp only [imp_self]
  }
  le_top a φ n p := by simp only
  himp φ ψ := {
    val := λ n γ => ∀ m, (p : m ≤ n) → φ.val m (Γ.iterRestrict m (n-m) n (by omega) γ) → ψ.val m (Γ.iterRestrict m (n-m) n (by omega) γ)
    property := by
      intro n γ q m p r
      specialize q m (by omega)
      rw [Γ.iterRestrictCast m m (n + 1 - m) (1 + (n - m)) (n+1) (n+1) rfl (by omega) rfl] at q
      rw [<-ToT.iterRestrictOne,ToT.iterRestrictComp] at *
      apply q
      exact r
  }
  le_himp_iff a b c := by
    constructor
    · intro h n x p
      obtain ⟨pa,pb⟩ := p
      specialize h n x pa n (le_refl n)
      have e : Γ.iterRestrict n (n - n) n (by omega) x = x := by {
        trans (Γ.iterRestrict n 0 n (by omega) x)
        · congr;omega
        · apply ToT.iterRestrictZero
      }
      rw [e] at h
      exact h pb
    · intro h n x p m e q
      apply h
      constructor
      · exact ToTPred.iterProp _ _ _ _ _ _ _ p
      · exact q
  bot := {
    val := λ n γ => false
    property := by
      intro n _
      simp only [Bool.false_eq_true, imp_self]
  }
  bot_le a n γ p := by simp only [Bool.false_eq_true] at p
  compl φ := {
    val := λ n γ => ∀ m, (p : m ≤ n) → φ.val m (Γ.iterRestrict m (n-m) n (by omega) γ) → false
    property := by {
      intro n γ q m p r
      specialize q m (by omega)
      rw [Γ.iterRestrictCast m m (n + 1 - m) (1 + (n - m)) (n+1) (n+1) rfl (by omega) rfl] at q
      rw [<-ToT.iterRestrictOne,ToT.iterRestrictComp] at *
      apply q
      exact r
    }
  }
  himp_bot := by simp only [Bool.false_eq_true, imp_false, implies_true]

instance : FirstOrderHyperdoctrine ToT where
  P := {
    obj := λ ⟨Γ⟩ => {
      α :=  ToTPred Γ
    }
    map := λ {X Y} f => {
      toFun := λ φ => {
        val := λ n x => φ.val n (f.unop.f n x)
        property := by {
          intro n γ a
          rw [<-f.unop.restrictF]
          apply φ.prop
          exact a
        }
      }
      map_sup' := λ φ ψ => by constructor
      map_inf' := λ φ ψ => by constructor
      map_bot' := by constructor
      map_himp' := λ φ ψ => by {
        simp at *;congr;funext n y;simp;constructor
        · intros h m e p
          rw [<-f.unop.iterRestrictF]
          apply h m e
          rw [f.unop.iterRestrictF]
          exact p
        · intro h m e p
          rw [f.unop.iterRestrictF]
          apply h m e
          rw [<-f.unop.iterRestrictF]
          exact p
      }
    }
  }
  rightAdj {Γ Δ} f := {-- ToTPred A ⥤ ToTPred B (With ToTPred X seen as a preorder category)
    obj := λ φ => {
      val := λ n γ => ∀ (m : ℕ) (p : m ≤ n) (δ : Γ.set m), (f.f m δ = Δ.iterRestrict m (n-m) n (by omega) γ) → φ.val m δ
      property := by
        intro n γ p m e δ h
        apply p m (by omega)
        rw [h,<-ToT.iterRestrictOne,ToT.iterRestrictComp]
        apply ToT.iterRestrictCast Δ _ _ _ _ _ _ rfl (by omega) rfl (by omega) γ
    }
    map := λ {φ ψ} F => {
      down := {
        down := by {
          simp only
          intro n γ h m e δ p
          exact F.down.down m δ (h m e δ p)
        }
      }
    }
    map_comp := λ {φ ψ ξ} F G => by constructor
    map_id := λ φ => by constructor
  }
  rightAdjunction {Γ Δ} f := {
    unit := {
      app := λ φ => by {
        simp only [CategoryTheory.Functor.comp_obj, preordToCat_obj, CategoryTheory.Cat.of_α] at φ

        intro n γ
        intro m p δ

        sorry
      }
    }
    counit := sorry
  }
  leftAdj {Γ Δ} f := {-- ToTPred A ⥤ ToTPred B (With ToTPred X seen as a preorder category)
    obj := λ φ => {
      val := λ n γ => ∃ (δ : Γ.set n), (f.f n δ = γ) ∧ φ.val n δ
      property := by
        intro n γ ⟨δ,⟨p,q⟩⟩
        exists Γ.restrict n δ
        constructor
        · subst p
          exact Eq.symm (f.restrictF n δ)
        · exact φ.prop _ _ q
    }
    map := λ {φ ψ} F => {
      down := {
        down := by {
          simp only
          intro n γ ⟨δ,⟨p,q⟩⟩
          simp only
          exact ⟨δ,⟨p,F.down.down n δ q⟩⟩
        }
      }
    }
    map_comp := λ {φ ψ ξ} F G => by constructor
  }
  leftAdjunction := sorry
  leftBeckChevalley := sorry
  rightBeckChevalley := sorry
