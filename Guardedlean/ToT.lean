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

@[simp]
lemma ToT.unfoldId (X : ToT) (n : ℕ) (x : X.set n) : (CategoryStruct.id X).setMorph n x = x := by rfl
@[simp]
lemma ToT.unfoldComp (X Y Z : ToT) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : X.set n):
  (f ≫ g).setMorph n x = g.setMorph n (f.setMorph n x) := by rfl

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

private def ToT_terminal : CategoryTheory.Limits.LimitCone (CategoryTheory.Functor.empty ToT) := {
  cone := {
    pt := ToT.one,
    π := ⟨λ X => (match X with | {as := Xa} => Xa.rec),by {simp}⟩
  },
  isLimit := {
    lift := λ s => ToT.toOne s.pt,
    fac := λ s X => match X with | {as := Xa} => Xa.rec,
    uniq := λ s f e => by {
      match f with | {setMorph := fs, restrictMorph := _} => {
        congr
      }
    }
  }
}

def ToT_prod (A B : ToT) : ToT where
  set := fun n => (A.set n) × (B.set n)
  restrict := fun n x => (A.restrict n (Prod.fst x), B.restrict n (Prod.snd x))

private def ToT_2prod (X Y : ToT) : Limits.LimitCone (CategoryTheory.Limits.pair X Y) := {
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

def ToT.cut (A : ToT) (n : ℕ) : ToT where
  set m := PProd (m ≤ n) (A.set m)
  restrict m x := match x with | ⟨h,x₀⟩ => ⟨Nat.le_of_succ_le h, A.restrict m x₀⟩

private def ToT.exp (X : ToT) : ToT ⥤ ToT where
  obj Y := {
    set := λ n => ToTMorphism (X.cut n) Y
    restrict := λ n f => {
      setMorph := λ m y => match y with | ⟨h,y₀⟩ => f.setMorph m ⟨by omega,y₀⟩
      restrictMorph := λ m => by {
        funext x
        simp only [Function.comp_apply]
        simp[ToT.cut]
        obtain ⟨e,x₀⟩ := x
        simp only
        exact congrFun (f.restrictMorph m) ⟨by omega,x₀⟩
      }
    }
  }
  map {A B} f := {
    setMorph := λ n g => {
      setMorph := λ m x =>f.setMorph m (g.setMorph m x)
      restrictMorph := by {
        intro m
        funext x
        obtain ⟨e,x₀⟩ := x
        have e' := congrFun (g.restrictMorph m) ⟨e,x₀⟩
        have e'' := congrFun (f.restrictMorph m) (g.setMorph (m + 1) ⟨e, x₀⟩)
        simp_all only [Function.comp_apply]
      }
    }
    restrictMorph := by {
      intro n
      funext g
      simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply,
        ToTMorphism.mk.injEq]
      funext m
      funext x
      obtain ⟨e,x₀⟩ := x
      simp only
    }
  }
  map_id A := by congr
  map_comp {A B C} f g := by congr

@[simp]
lemma expIterRestrict (A X : ToT) (n k m p : ℕ) (e : n + k = m) (e' : p ≤ n) (f : (X.exp.obj A).set m) (x : X.set p) :
  ((X.exp.obj A).iterRestrict n k m e f).setMorph p ⟨e',x⟩ = f.setMorph p ⟨by omega,x⟩ := by {
    induction k generalizing n m p
    case zero =>
      subst e
      simp only [Nat.add_zero]
      rw [ToT.iterRestrictZero]
    case succ k₀ hr =>
      unfold ToT.iterRestrict
      simp only
      delta ToT.exp
      simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply]
      apply hr
  }

instance : MonoidalCategory ToT := CategoryTheory.monoidalOfChosenFiniteProducts ToT_terminal ToT_2prod

@[simp]
lemma prodRestrict (A B : ToT) (n : ℕ) (x : A.set (n+1) × B.set (n+1)) :
 (MonoidalCategory.tensorObj A B).restrict n x = (A.restrict n (Prod.fst x), B.restrict n (Prod.snd x)) := by rfl

@[simp]
lemma whiskerMorph (X A B : ToT) (f : A ⟶ B) (m : ℕ) (x : X.set m) (a : A.set m):
  (MonoidalCategory.whiskerLeft X f).setMorph m (x,a) = (x,f.setMorph m a) := by rfl

instance : MonoidalClosed ToT where
  closed X := {
    rightAdj := ToT.exp X
    adj := {
      unit := {
        app := λ Y => {
          setMorph := λ n y => {
            setMorph := λ m x => match x with | ⟨e,x₀⟩ => (x₀,Y.iterRestrict m (n-m) n (by omega) y)
            restrictMorph := by {
              intro m
              funext y
              obtain ⟨e,y₀⟩ := y
              simp only [MonoidalCategory.tensorLeft_obj, Function.comp_apply]
              unfold ToT.cut
              simp only [prodRestrict]
              apply congrArg (fun ξ => (X.restrict m y₀,ξ))
              calc
                Y.restrict m (Y.iterRestrict (m + 1) (n - (m + 1)) n _ y) = Y.iterRestrict m (n - (m + 1) + 1) n _ y
                := Y.iterRestrictComp (m+1) n m (n-(m+1)) 1 (by omega) (by omega) y
                _ = Y.iterRestrict m (n - m) n _ y := by congr;omega
            }
          }
          restrictMorph := by {
            intro n
            funext x
            simp only [Functor.comp_obj, MonoidalCategory.tensorLeft_obj, Functor.id_obj, Function.comp_apply]
            unfold ToT.exp
            simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply,
              ToTMorphism.mk.injEq]
            funext m
            funext y
            obtain ⟨e,y₀⟩ := y
            simp only
            symm
            apply (congrArg (fun z => (y₀,z)))
            calc
              Y.iterRestrict m (n - m) n _ (Y.restrict n x) = Y.iterRestrict m (1+(n-m)) (n+1) _ x
              := (Y.iterRestrictComp n (n+1) m 1 (n-m) (by omega) (by omega) x)
              _ = Y.iterRestrict m ((n+1)- m) (n+1) _ x := by congr;omega
          }
        }
        naturality := by {
          intros A B f
          apply ToTMorphism.extentionnality
          funext n
          funext x
          simp only [Functor.comp_obj, MonoidalCategory.tensorLeft_obj, Functor.id_obj,
            Functor.id_map, ToT.unfoldComp, Functor.comp_map, MonoidalCategory.tensorLeft_map]
          apply ToTMorphism.extentionnality
          funext m
          funext y
          obtain ⟨e,y₀⟩ := y
          simp only
          unfold ToT.exp
          simp only [whiskerMorph]
          apply (congrArg (fun z => (y₀,z)))
          apply (congrFun (ToTMorphism.restrictMorphLift f m (n-m) n _) x)
        }
      }
      counit := {
        app := λ Y => {
          setMorph := λ n x => match x with | ⟨x₀,⟨f,_⟩⟩ => f n ⟨by rfl,x₀⟩
          restrictMorph := by {
            intros n
            funext x
            obtain ⟨x₀,⟨f,e⟩⟩ := x
            apply congrFun (e n)
          }
        }
        naturality := λ A B f => by rfl
      }
      left_triangle_components := by {
        intro Y
        apply ToTMorphism.extentionnality
        simp only [Functor.id_obj, MonoidalCategory.tensorLeft_obj, Functor.comp_obj,
          MonoidalCategory.tensorLeft_map]
        funext n
        funext z
        obtain ⟨x,y⟩ := z
        simp only [ToT.unfoldComp, whiskerMorph, Nat.sub_self, ToT.unfoldId]
        rw [Y.iterRestrictZero]
      }
      right_triangle_components := by {
        intro Y
        apply ToTMorphism.extentionnality
        funext n
        funext x
        obtain ⟨fx,rx⟩ := x
        simp only [Functor.id_obj, Functor.comp_obj, MonoidalCategory.tensorLeft_obj,
          ToT.unfoldComp, ToT.unfoldId]
        apply ToTMorphism.extentionnality
        funext m
        funext x
        obtain ⟨e,x₀⟩ := x
        delta ToT.exp
        simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply]
        apply expIterRestrict Y X m (n-m) n m (by omega) (by rfl) ⟨fx,rx⟩ x₀
      }
    }
  }




--instance : CartesianClosed ToT := _
