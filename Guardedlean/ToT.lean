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
      simp only [Nat.add_zero, add_zero]
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




--instance : CartesianClosed ToT := _

-- LATER
def ToT.Later : ToT ⥤ ToT where
  obj X := {
    set := fun
          | 0 => Unit
          | n+1 => X.set n
    restrict := fun
          | 0, _ => ()
          | n+1, x => X.restrict n x
  }
  map {X Y} f := {
    f := fun
      | 0,_ => ()
      | n+1,x => f.f n x
    restrictF := λ n x => by {
      cases n
      case zero => rfl
      case succ k => apply f.restrictF k x
    }
  }
  map_id X := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => rfl
    case succ k => rfl
  })
  map_comp {X Y Z} f g := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => rfl
    case succ k => rfl
  })

def ToT.Earlier : ToT ⥤ ToT where
  obj X := {
    set := λ n => X.set (n+1)
    restrict := λ n => X.restrict (n+1)
  }
  map {X Y} f := {
    f := λ n => f.f (n+1)
    restrictF := λ n => f.restrictF (n+1)
  }
  map_id X := ToT.Hom.ext (by simp only [CategoryStruct.id,implies_true])
  map_comp {X Y Z} f g := ToT.Hom.ext (by simp only [CategoryStruct.comp, implies_true])

@[simp]
def LaterUnfold (X : ToT) (n : ℕ): (ToT.Later.obj X).set (n+1) = X.set n := by rfl
@[simp]
def LaterUnfold0 (X : ToT) : (ToT.Later.obj X).set 0 = Unit := by rfl
@[simp]
def LaterUnfoldRestrict0 (X : ToT) (x:X.set 0): (ToT.Later.obj X).restrict 0 x = () := by rfl
@[simp]
def LaterUnfoldRestrictN (X : ToT) (n : ℕ) (x:X.set (n+1)): (ToT.Later.obj X).restrict (n+1) x = X.restrict n x := by rfl
@[simp]
def EarlierUnfold (X : ToT) (n : ℕ): (ToT.Earlier.obj X).set (n) = X.set (n+1) := by rfl
@[simp]
def EarlierUnfoldRestrict (X : ToT) (n : ℕ) (x : X.set (n+1+1)): (ToT.Earlier.obj X).restrict n x = X.restrict (n + 1) x := by rfl

def ToT.LaterEarlierAdj : Adjunction ToT.Earlier ToT.Later where
  unit := {
    app := λ X => {
      f := λ n x => match n with | 0 => () | _+1 => x
      restrictF := λ n x => by {
        cases n
        case zero => simp only [Functor.comp_obj, LaterUnfoldRestrict0]
        case succ k => simp only [Functor.comp_obj, LaterUnfoldRestrictN, EarlierUnfoldRestrict,
          Functor.id_obj]
      }
    }
    naturality := λ {X Y} f => ToT.Hom.ext (λ n x => by {
      cases n
      case zero => simp only [Earlier, Later, Nat.reduceAdd, Functor.comp_obj, Functor.id_obj,
        Functor.id_map, unfoldComp, Functor.comp_map]
      case succ k => simp only [Earlier, Later, Nat.reduceAdd, Functor.comp_obj,
        Functor.id_obj, Functor.id_map, unfoldComp, Functor.comp_map]
    })
  }
  counit := {
    app := λ X => {
      f := λ n x => x
      restrictF := λ n x => by simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, EarlierUnfoldRestrict,
          LaterUnfoldRestrictN]
    }
    naturality := λ {X Y} f => ToT.Hom.ext (λ n x => by simp only [Earlier,Later,Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, Functor.comp_map, unfoldComp,
        Functor.id_map])
  }
  right_triangle_components Y := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => cases x;simp only [Later, Nat.reduceAdd, Functor.id_obj, Functor.comp_obj,
      unfoldComp]
    case succ n => simp only [Later, Nat.reduceAdd, Functor.id_obj, Earlier, Functor.comp_obj,
      unfoldComp,CategoryStruct.id,id_eq];
  })
  left_triangle_components X := ToT.Hom.ext (λ n x => by {
    cases n
    case zero => simp only [Earlier,Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, unfoldComp, CategoryStruct.id,id_eq]
    case succ n => simp only [Earlier,Functor.id_obj, Functor.comp_obj, unfoldComp, CategoryStruct.id,id_eq]
  })

def fixpval {Γ A : ToT} (f : MonoidalCategory.tensorObj Γ (ToT.Later.obj A) ⟶ A): (n : Nat) →  Γ.set n → A.set n
  | 0, γ => f.f 0 (γ, ())
  | n+1, γ => f.f (n+1) (γ, fixpval f n (Γ.restrict n γ))

def fixp {Γ X : ToT} (f : MonoidalCategory.tensorObj Γ (ToT.Later.obj X) ⟶ X) : Γ ⟶ X where
  f := fixpval f
  restrictF n γ := by {
    induction n with
    | zero => simp only [fixpval, Function.comp_apply];apply f.restrictF 0
    | succ m p => simp only [fixpval,f.restrictF,prodRestrict]
                  simp only [ToT.Later]
                  rw [<-p]
                  congr
                  rw [<-p]
  }
def ToT.snd (X Y : ToT) : (MonoidalCategoryStruct.tensorObj X Y) ⟶ Y
  := (MonoidalCategoryStruct.whiskerRight (X.toOne) Y) ≫ (MonoidalCategoryStruct.leftUnitor Y).hom
def fixpoint (X : ToT) (f : ToT.Later.obj X ⟶ X) : ToT.one ⟶ X :=
  fixp ((MonoidalCategoryStruct.leftUnitor (ToT.Later.obj X)).hom ≫ f)
