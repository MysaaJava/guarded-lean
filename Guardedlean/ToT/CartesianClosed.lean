import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Types
import Guardedlean.ToT.Basic

open CategoryTheory

namespace Guardedlean

/--- CCC ---/
def ToT.one : ToT := ⟨λ _ => Unit, λ _ x => x⟩

def ToT.toOne (X : ToT) : X ⟶ ToT.one := ⟨λ n _ => (),λ n x => by rfl⟩

instance : CategoryTheory.ChosenFiniteProducts ToT where
  terminal := {
    cone := {
      pt := ToT.one,
      π := ⟨λ X => (match X with | {as := Xa} => Xa.rec),by simp only [Functor.const_obj_obj,
        Functor.const_obj_map, Category.id_comp, IsEmpty.forall_iff, implies_true]⟩
    },
    isLimit := {
      lift := λ s => ToT.toOne s.pt,
      fac := λ s X => match X with | {as := Xa} => Xa.rec,
      uniq := λ s f e => by {
        match f with | ⟨fs,_⟩ => congr
      }
    }
  }
  product X Y := {
    cone := {
      pt := {
        set := fun n => (X.set n) × (Y.set n)
        restrict := fun n x => (X.restrict n (Prod.fst x), Y.restrict n (Prod.snd x))
      }
      π := {
        app := λ a => match a with
        | ⟨.left⟩ => ⟨λ n x => Prod.fst x,λ n x => by rfl⟩
        | ⟨.right⟩ => ⟨λ n x => Prod.snd x,λ n x => by rfl⟩
        naturality := λ a b f => by {
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Limits.pair_obj_left,
            Limits.pair_obj_right, Category.id_comp]
          match f with | .up (.up x) => {
          have e : a = b := by {cases a;cases b;simp only at x;simp only [Discrete.mk.injEq];apply x}
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
          f := λ n x => Prod.mk (π₁.f n x) (π₂.f n x),
          restrictF := λ n x => by {
              simp only [Functor.const_obj_obj, Limits.pair_obj_left, Limits.pair_obj_right,
                Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as, cast_eq]
              congr
              apply π₁.restrictF
              apply π₂.restrictF
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
      uniq := λ s m e => ToT.Hom.ext (λ n x => by {
        have e₁ := e ⟨.left⟩
        have e₂ := e ⟨.right⟩
        clear e;
        simp only [Limits.pair_obj_left, Functor.const_obj_obj, Limits.pair_obj_right,
          Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as, cast_eq,
          Limits.BinaryFan.π_app_left, Limits.BinaryFan.π_app_right] at *
        rw [<-e₁,<-e₂]
        rfl
      })
    }
  }

def ToT.cut (A : ToT) (n : ℕ) : ToT where
  set m := PProd (m ≤ n) (A.set m)
  restrict m x := match x with | ⟨h,x₀⟩ => ⟨Nat.le_of_succ_le h, A.restrict m x₀⟩

private def ToT.exp (X : ToT) : ToT ⥤ ToT where
  obj Y := {
    set := λ n => ToT.Hom (X.cut n) Y
    restrict := λ n f => {
      f := λ m y => match y with | ⟨h,y₀⟩ => f.f m ⟨by omega,y₀⟩
      restrictF := λ m ⟨e,x₀⟩ => by {
        simp only [cut]
        apply f.restrictF m
      }
    }
  }
  map {A B} f := {
    f := λ n g => {
      f := λ m x => f.f m (g.f m x)
      restrictF := λ m ⟨e,x₀⟩ => by {
        simp only
        rw [f.restrictF,g.restrictF]
      }
    }
    restrictF := λ n g => by {
      simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply,
        ToT.Hom.mk.injEq]
      funext m
      funext x
      obtain ⟨e,x₀⟩ := x
      simp only
    }
  }

@[simp]
lemma expIterRestrict (A X : ToT) (n k m p : ℕ) (e : n + k = m) (e' : p ≤ n) (f : (X.exp.obj A).set m) (x : X.set p) :
  ((X.exp.obj A).iterRestrict n k m e f).f p ⟨e',x⟩ = f.f p ⟨by omega,x⟩ := by {
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

instance : MonoidalCategory ToT := CategoryTheory.ChosenFiniteProducts.instMonoidalCategory ToT

@[simp]
lemma prodRestrict (A B : ToT) (n : ℕ) (x : A.set (n+1) × B.set (n+1)) :
 (MonoidalCategory.tensorObj A B).restrict n x = (A.restrict n (Prod.fst x), B.restrict n (Prod.snd x)) := by rfl

@[simp]
lemma whiskerMorph (X A B : ToT) (f : A ⟶ B) (m : ℕ) (x : X.set m) (a : A.set m):
  (MonoidalCategory.whiskerLeft X f).f m (x,a) = (x,f.f m a) := by rfl

instance : MonoidalClosed ToT where
  closed X := {
    rightAdj := ToT.exp X
    adj := {
      unit := {
        app := λ Y => {
          f := λ n y => {
            f := λ m x => match x with | ⟨e,x₀⟩ => (x₀,Y.iterRestrict m (n-m) n (by omega) y)
            restrictF := λ m ⟨e,y₀⟩ => by {
              simp only [MonoidalCategory.tensorLeft_obj, prodRestrict]
              apply congrArg (fun ξ => (X.restrict m y₀,ξ))
              calc
                Y.restrict m (Y.iterRestrict (m + 1) (n - (m + 1)) n _ y) = Y.iterRestrict m (n - (m + 1) + 1) n _ y
                := Y.iterRestrictComp (m+1) n m (n-(m+1)) 1 (by omega) (by omega) y
                _ = Y.iterRestrict m (n - m) n _ y := by congr;omega
            }
          }
          restrictF := λ n x => by {
            simp only [ToT.exp, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Functor.comp_obj,
              MonoidalCategory.tensorLeft_obj, Functor.id_obj, ToT.Hom.mk.injEq]
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
        naturality := λ A B f =>
          ToT.Hom.ext (λ n x =>
          ToT.Hom.ext (λ m ⟨e,y₀⟩ => by {
          simp only [MonoidalCategory.tensorLeft_obj, Functor.id_obj, ToT.exp, Int.reduceNeg, id_eq,
            Int.Nat.cast_ofNat_Int, Functor.comp_obj, Functor.id_map, ToT.unfoldComp,
            Functor.comp_map, prodRestrict, MonoidalCategory.tensorLeft_map, whiskerMorph]
          congr
          apply ToT.Hom.iterRestrictF
        }))
      }
      counit := {
        app := λ Y => {
          f := λ n x => match x with | ⟨x₀,⟨f,_⟩⟩ => f n ⟨by rfl,x₀⟩
          restrictF := λ n ⟨x₀,⟨f,e⟩⟩ => by {
            simp only [Functor.id_obj, e, ToT.cut, ToT.exp, Int.reduceNeg, id_eq,
              Int.Nat.cast_ofNat_Int, Functor.comp_obj, MonoidalCategory.tensorLeft_obj,
              prodRestrict]
          }
        }
        naturality := λ A B f => by rfl
      }
      left_triangle_components := λ Y => ToT.Hom.ext (λ n ⟨x,y⟩ => by {
        simp only [MonoidalCategory.tensorLeft_obj, Functor.id_obj, Functor.comp_obj,
          MonoidalCategory.tensorLeft_map, prodRestrict, ToT.unfoldComp, whiskerMorph, Nat.sub_self,
          ToT.iterRestrictZero,CategoryStruct.id,id_eq]
      })
      right_triangle_components := λ Y =>
        ToT.Hom.ext (λ n ⟨fx,rx⟩ =>
        ToT.Hom.ext (λ m ⟨e,x₀⟩ => by {
        simp only [Functor.id_obj, ToT.exp, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int,
          Functor.comp_obj, MonoidalCategory.tensorLeft_obj, prodRestrict, ToT.unfoldComp]
        apply expIterRestrict
      }))
    }
  }
