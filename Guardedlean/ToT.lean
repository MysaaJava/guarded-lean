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

structure ToT where
  set : ℕ → Type
  restrict : ∀ n, set (n + 1) → set n

structure ToTMorphism (X Y : ToT) where
  setMorph : (n: ℕ) → (X.set n) → (Y.set n)
  restrictMorph: ∀ n,
    (Y.restrict n) ∘ (setMorph (n+1)) = (setMorph n) ∘ (X.restrict n)

instance : Category ToT where
  Hom := ToTMorphism
  id X := {
    setMorph := λ _n => id,
    restrictMorph := λ _n => by {rw [Function.id_comp, Function.comp_id]}
  }
  comp {X Y Z} u v := {
    setMorph := λ n => (v.setMorph n) ∘ (u.setMorph n),
    restrictMorph := by {
      intro n
      simp
      rw [← comp_assoc, v.restrictMorph n, comp_assoc, u.restrictMorph n, comp_assoc]
    }
  }

def ToT.iterRestrict (o : ToT) (n k m : ℕ) (e : n + k = m) (x : o.set m) : o.set n := match k with
  | 0 =>
    have e' : n = m := e
    e' ▸ x
  | k₀ + 1 =>
    have eq : n + 1 + k₀ = m := by omega
    o.restrict n (o.iterRestrict (n + 1) k₀ m eq x)

def ToT.iterRestrictZero (o : ToT) (n m : ℕ) (e : n = m) (x : o.set m) : o.iterRestrict n 0 m e x = e ▸ x := by
  unfold ToT.iterRestrict
  simp

def ToT.iterRestrictComp (o : ToT) (n m p k q : ℕ) (e₁ : n + k = m) (e₂ : p + q = n) (x : o.set m) :
    o.iterRestrict p q n e₂ (o.iterRestrict n k m e₁ x) = o.iterRestrict p (k + q) m (by omega) x := by
    induction q generalizing p with
    | zero =>
      rw [ToT.iterRestrictZero]
      subst e₂
      simp
    | succ q₀ hr =>
      unfold ToT.iterRestrict
      simp
      rw [hr]
theorem ToTMorphism.extentionnality (X Y : ToT) (f g : ToTMorphism X Y)
  (e : f.setMorph = g.setMorph) : f = g := by {
    cases f;cases g
    congr
  }
theorem ToTMorphism.restrictMorphLift {X Y : ToT} (η : X ⟶ Y) : ∀ n k m, (eq : n + k = m) →
    (Y.iterRestrict n k m eq) ∘ (η.setMorph m) = (η.setMorph n) ∘ (X.iterRestrict n k m eq) := by {
      intro n
      intro k
      induction k generalizing n with
      | zero =>
        intro m eq
        funext x
        simp
        rw [ToT.iterRestrictZero,ToT.iterRestrictZero]
        subst eq
        rfl
      | succ k hk =>
          intro m eq
          funext x
          simp [ToT.iterRestrict]
          rw [compDefExt (η.setMorph n)]
          rw [<-η.restrictMorph]
          simp
          congr
          rw [compDefExt (Y.iterRestrict (n+1) k m _),compDefExt (η.setMorph (n+1))]
          rw [hk]
    }

/--- CCC ---/
def ToT.one : ToT := {
  set := λ _ => Unit,
  restrict := λ _ x => x
}

def ToT.toOne (X : ToT) : ToTMorphism X ToT.one := {
  setMorph := λ n _ => (),
  restrictMorph := by {
    intro n
    funext x
    unfold ToT.one
    simp
  }
}

private lemma ToT_hasTerminal : CategoryTheory.Limits.HasTerminal ToT := by {
  have e : ∀ (Y : ToT), Nonempty (Y ⟶ ToT.one) := λ Y => Nonempty.intro (ToT.toOne Y)
  have f : ∀ (Y : ToT), Subsingleton (Y ⟶ ToT.one) := by {
    intro Y
    apply Subsingleton.intro
    intro a b
    match a,b with | {setMorph:=as,restrictMorph:=_},{setMorph:=bs,restrictMorph:=_} => {
      congr
      apply funext
      intro n
      apply funext
      intro x
      cases (as n x)
      cases (bs n x)
      rfl
    }

  }
  apply CategoryTheory.Limits.hasTerminal_of_unique ToT.one
}

def ToT_prod (A B : ToT) : ToT where
  set := fun n => (A.set n) × (B.set n)
  restrict := fun n x => (A.restrict n (Prod.fst x), B.restrict n (Prod.snd x))

instance (X Y : ToT) : Limits.HasLimit (CategoryTheory.Limits.pair X Y) where
  exists_limit := Nonempty.intro {
    cone := {
      pt := ToT_prod X Y,
      π := {
        app := λ a => match a with
        | {as:=.left} => {
          setMorph := λ n x => Prod.fst x
          restrictMorph := λ n => funext (λ x => rfl)
        }
        | {as:=.right} => {
          setMorph := λ n x => Prod.snd x
          restrictMorph := λ n => funext (λ x => rfl)
        },
        naturality := λ a b f => by {
          simp
          match f with | .up (.up x) => {
          have e : a = b := by {cases a;cases b;simp at x;simp;apply x}
          subst e
          rfl
          }
        }
      }
    },
    isLimit := {
      lift := λ s =>
        let π₁ := (s.π.app {as := Limits.WalkingPair.left})
        let π₂ := (s.π.app {as := Limits.WalkingPair.right})
      {
          setMorph := λ n x => Prod.mk (π₁.setMorph n x) (π₂.setMorph n x),
          restrictMorph := by {
            intro n;simp;funext x;simp
            unfold ToT_prod;simp;
            exact And.intro
             (congrFun (π₁.restrictMorph n) x)
             (congrFun (π₂.restrictMorph n) x)
          }
      },
      fac := λ s =>
        by {
          intro j
          match j with | {as := jj} => {
            cases jj
            rfl
            rfl
          }
        },
      uniq := λ s m e => by {
        simp
        apply ToTMorphism.extentionnality
        simp
        funext n x
        have e₁ := e {as := Limits.WalkingPair.left}
        have e₂ := e {as := Limits.WalkingPair.right}
        clear e;simp at e₁ e₂
        rw [<-e₁,<-e₂]
        unfold CategoryStruct.comp Category.toCategoryStruct instCategoryToT
        rfl
      }
    }
  }

private lemma ToT_hasBinaryProduct : CategoryTheory.Limits.HasBinaryProducts ToT := by {
    apply CategoryTheory.Limits.hasBinaryProducts_of_hasLimit_pair
}
