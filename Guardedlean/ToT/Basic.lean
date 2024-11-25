import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Guardedlean.Lemmas

open CategoryTheory

namespace Guardedlean

universe u

structure ToT : Type (u+1) where
  set : ℕ → Type u
  restrict : ∀ n, set (n + 1) → set n

structure ToT.Hom (X Y : ToT) where
  f : (n: ℕ) → (X.set n) → (Y.set n)
  restrictF: ∀ (n : ℕ) (x : X.set (n+1)),
    Y.restrict n (f (n+1) x) = f n (X.restrict n x)

instance : Category ToT where
  Hom := ToT.Hom
  id X := ⟨λ _ => id,λ _ _ => by rfl⟩
  comp {X Y Z} u v := ⟨λ n x => v.f n (u.f n x),λ n x => by simp only [v.restrictF, u.restrictF]⟩

--TODO are those removable
@[simp]
lemma ToT.unfoldComp (X Y Z : ToT) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : X.set n):
  (f ≫ g).f n x = g.f n (f.f n x) := by rfl

def ToT.iterRestrict (o : ToT) (n k m : ℕ) (e : n + k = m) (x : o.set m) : o.set n := match k with
  | 0 =>
    have e' : n = m := e
    e' ▸ x
  | k₀ + 1 =>
    have eq : n + 1 + k₀ = m := by omega
    o.restrict n (o.iterRestrict (n + 1) k₀ m eq x)
def ToT.iterRestrictCast (o : ToT) (n n' k k' m m' : ℕ) (en : n = n') (ek : k = k') (em : m = m') (e : n + k = m)
  (x : o.set m) :
  o.iterRestrict n k m e x = en ▸ o.iterRestrict n' k' m' (by omega) (em ▸ x)
  := by subst en ek em;simp only
@[simp]
def ToT.iterRestrictZero (o : ToT) (n m : ℕ) (e : n = m) (x : o.set m) : o.iterRestrict n 0 m e x = e ▸ x := by rfl
@[simp]
def ToT.iterRestrictOne (o: ToT) (n : ℕ) (x : o.set (n+1)) :
   o.iterRestrict n 1 (n+1) (by omega) x = o.restrict n x := by simp only [iterRestrict]
@[simp]
def ToT.iterRestrictComp (o : ToT) (n m p k q : ℕ) (e₁ : n + k = m) (e₂ : p + q = n) (x : o.set m) :
    o.iterRestrict p q n e₂ (o.iterRestrict n k m e₁ x) = o.iterRestrict p (k + q) m (by omega) x := by
    induction q generalizing p with
    | zero =>
      rw [ToT.iterRestrictZero]
      subst e₂
      simp only [Nat.add_zero]
    | succ q₀ hr =>
      unfold ToT.iterRestrict
      simp only [Nat.add_eq]
      rw [hr]

theorem ToT.Hom.ext {X Y : ToT} {f g : ToT.Hom X Y}
  (e : (n : ℕ) → (x : X.set n) → f.f n x = g.f n x) : f = g := by {
    cases f;cases g
    congr
    funext n x
    apply e
  }
theorem ToT.Hom.iterRestrictF {X Y : ToT} (η : ToT.Hom X Y) :
    ∀ n k m, (eq : n + k = m) → (x : X.set m) →
    Y.iterRestrict n k m eq (η.f m x) = η.f n (X.iterRestrict n k m eq x) := by {
      intro n
      intro k
      induction k generalizing n with
      | zero =>
        intro m eq x
        subst m
        rfl
      | succ k hk =>
          intro m eq x
          simp only [ToT.iterRestrict]
          rw [hk,η.restrictF]
    }

/--- Functor to Set ---/
def ToT.ofSet : Type ⥤ ToT where
  obj X := ⟨λ _ => X,λ _ x => x⟩
  map {X Y} f := ⟨λ n x => f x,by simp only [implies_true]⟩

def ToT.const {A : ToT} {B : Type} (b : B) : A ⟶ ToT.ofSet.obj B :=
  ⟨λ _ _ => b,λ n => by simp only [ofSet, implies_true]⟩
