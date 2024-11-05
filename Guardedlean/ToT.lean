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
  restrictMorph: ∀ (n : ℕ),
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
      simp only
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

@[simp]
def ToT.iterRestrictZero (o : ToT) (n m : ℕ) (e : n = m) (x : o.set m) : o.iterRestrict n 0 m e x = e ▸ x := by rfl

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

theorem ToTMorphism.extentionnality (X Y : ToT) (f g : ToTMorphism X Y)
  (e : (n : ℕ) → (x : X.set n) → f.setMorph n x = g.setMorph n x) : f = g := by {
    cases f;cases g
    congr
    funext n x
    apply e
  }
theorem ToTMorphism.restrictMorphLift {X Y : ToT} (η : X ⟶ Y) : ∀ n k m, (eq : n + k = m) →
    (Y.iterRestrict n k m eq) ∘ (η.setMorph m) = (η.setMorph n) ∘ (X.iterRestrict n k m eq) := by {
      intro n
      intro k
      induction k generalizing n with
      | zero =>
        intro m eq
        funext x
        simp only [Function.comp_apply]
        rw [ToT.iterRestrictZero,ToT.iterRestrictZero]
        subst eq
        rfl
      | succ k hk =>
          intro m eq
          funext x
          simp only [ToT.iterRestrict, Function.comp_apply]
          rw [compDefExt (η.setMorph n)]
          rw [<-η.restrictMorph]
          simp only [Function.comp_apply]
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
    simp only [Function.comp_apply]
  }
}

private def ToT_terminal : CategoryTheory.Limits.LimitCone (CategoryTheory.Functor.empty ToT) := {
  cone := {
    pt := ToT.one,
    π := ⟨λ X => (match X with | {as := Xa} => Xa.rec),by {simp only [Functor.const_obj_obj,
      Functor.const_obj_map, Category.id_comp, IsEmpty.forall_iff, implies_true]}⟩
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
        setMorph := λ n x => Prod.mk (π₁.setMorph n x) (π₂.setMorph n x),
        restrictMorph := by {
          intro n;simp only [Functor.const_obj_obj, Limits.pair_obj_left, Function.comp_apply,
            Limits.pair_obj_right, Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as,
            cast_eq];funext x;simp only [Function.comp_apply]
          unfold ToT_prod;simp only [Prod.mk.injEq];
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
      simp only [Functor.const_obj_obj, Limits.pair_obj_left, Function.comp_apply,
        Limits.pair_obj_right, Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as,
        cast_eq, Limits.BinaryFan.π_app_left, Limits.BinaryFan.π_app_right]
      apply ToTMorphism.extentionnality;intros n x
      simp only [Functor.const_obj_obj, Limits.pair_obj_left, Function.comp_apply,
        Limits.pair_obj_right, Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as,
        cast_eq]
      have e₁ := e {as := Limits.WalkingPair.left}
      have e₂ := e {as := Limits.WalkingPair.right}
      clear e;simp only [Limits.pair_obj_left, Functor.const_obj_obj, Function.comp_apply,
        Limits.pair_obj_right, Functor.const_obj_map, id_eq, eq_mpr_eq_cast, Discrete.mk_as,
        cast_eq, Limits.BinaryFan.π_app_left, Limits.BinaryFan.π_app_right] at e₁ e₂
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
        simp only [cut]
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
          apply ToTMorphism.extentionnality;intros n x
          simp only [Functor.comp_obj, MonoidalCategory.tensorLeft_obj, Functor.id_obj,
            Functor.id_map, ToT.unfoldComp, Functor.comp_map, MonoidalCategory.tensorLeft_map]
          apply ToTMorphism.extentionnality;intros m y
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
        apply ToTMorphism.extentionnality; intros n z
        simp only [Functor.id_obj, MonoidalCategory.tensorLeft_obj, Functor.comp_obj,
          MonoidalCategory.tensorLeft_map]
        obtain ⟨x,y⟩ := z
        simp only [ToT.unfoldComp, whiskerMorph, Nat.sub_self, ToT.unfoldId]
        rw [Y.iterRestrictZero]
      }
      right_triangle_components := by {
        intro Y
        apply ToTMorphism.extentionnality;intros n x
        obtain ⟨fx,rx⟩ := x
        simp only [Functor.id_obj, Functor.comp_obj, MonoidalCategory.tensorLeft_obj,
          ToT.unfoldComp, ToT.unfoldId]
        apply ToTMorphism.extentionnality; intros m x
        obtain ⟨e,x₀⟩ := x
        delta ToT.exp
        simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Function.comp_apply]
        apply expIterRestrict Y X m (n-m) n m (by omega) (by rfl) ⟨fx,rx⟩ x₀
      }
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
    setMorph := fun
      | 0,_ => ()
      | n+1,x => f.setMorph n x
    restrictMorph := λ n => by {
      funext x
      simp only [Nat.reduceAdd, Function.comp_apply]
      cases n
      case zero => rfl
      case succ k => simp only; apply congrFun (f.restrictMorph k) x
    }
  }
  map_id X := by {
    apply ToTMorphism.extentionnality; intros n x
    cases n
    case zero => rfl
    case succ k => rfl
  }
  map_comp {X Y Z} f g := by {
    apply ToTMorphism.extentionnality; intros n x
    cases n
    case zero => rfl
    case succ k => rfl
  }

def ToT.Earlier : ToT ⥤ ToT where
  obj X := {
    set := λ n => X.set (n+1)
    restrict := λ n => X.restrict (n+1)
  }
  map {X Y} f := {
    setMorph := λ n => f.setMorph (n+1)
    restrictMorph := λ n => f.restrictMorph (n+1)
  }
  map_id X := by {
    apply ToTMorphism.extentionnality
    simp only [unfoldId, implies_true]
  }
  map_comp {X Y Z} f g := by {
    apply ToTMorphism.extentionnality
    simp only [unfoldComp, implies_true]
  }

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
      setMorph := λ n x => match n with | 0 => () | _+1 => x
      restrictMorph := λ n => by {
        funext x
        cases n
        case zero => simp only [Functor.comp_obj, Functor.id_obj, Nat.reduceAdd, Function.comp_apply,
          LaterUnfoldRestrict0]
        case succ k => simp only [Functor.comp_obj, Functor.id_obj, Function.comp_apply,
          LaterUnfoldRestrictN,EarlierUnfoldRestrict]
      }
    }
    naturality := λ {X Y} f => by {
      apply ToTMorphism.extentionnality; intros n x
      cases n
      case zero => unfold Later Earlier;simp only [Nat.reduceAdd, Functor.comp_obj, Functor.id_obj,
        Functor.id_map, unfoldComp, Functor.comp_map]
      case succ k => unfold Earlier Later;simp only [Nat.reduceAdd, Functor.comp_obj,
        Functor.id_obj, Functor.id_map, unfoldComp, Functor.comp_map]
    }
  }
  counit := {
    app := λ X => {
      setMorph := λ n x => x
      restrictMorph := λ n => by {
        funext x
        simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, EarlierUnfoldRestrict,
          LaterUnfoldRestrictN]
      }
    }
    naturality := λ {X Y} f => by {
      apply ToTMorphism.extentionnality; intros n x
      unfold Earlier Later
      simp only [Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, Functor.comp_map, unfoldComp,
        Functor.id_map]
    }
  }
  right_triangle_components Y := by {
    apply ToTMorphism.extentionnality;intros n x
    unfold Later
    cases n
    case zero => cases x;simp only [Nat.reduceAdd, Functor.id_obj, Functor.comp_obj, unfoldComp,
      unfoldId]
    case succ n => simp only [Nat.reduceAdd, Functor.id_obj, Functor.comp_obj, unfoldComp, unfoldId]
  }
  left_triangle_components X := by {
    apply ToTMorphism.extentionnality;intros n x
    unfold Earlier
    cases n
    case zero => simp only [Functor.id_obj, Nat.reduceAdd, Functor.comp_obj, unfoldComp, unfoldId]
    case succ n => simp only [Functor.id_obj, Functor.comp_obj, unfoldComp, unfoldId]
  }

def fixpval {Γ A : ToT} (f : ToT_prod Γ (ToT.Later.obj A) ⟶ A): (n : Nat) →  Γ.set n → A.set n
  | 0, γ => f.setMorph 0 (γ, ())
  | n+1, γ => f.setMorph (n+1) (γ, fixpval f n (Γ.restrict n γ))

def fixp {Γ X : ToT} (f : ToT_prod Γ (ToT.Later.obj X) ⟶ X) : Γ ⟶ X where
  setMorph := fixpval f
  restrictMorph n := by {
    funext γ
    induction n with
    | zero => simp only [fixpval, Function.comp_apply];apply congrFun (f.restrictMorph 0) _
    | succ m p => simp only [fixpval,f.restrictMorph,ToT_prod]
                  simp only [ToT.Later]
                  simp only [Function.comp_apply]
                  have ee := congrFun (f.restrictMorph (m+1)) (γ, f.setMorph (m + 1) (Γ.restrict (m + 1) γ, fixpval f m (Γ.restrict m (Γ.restrict (m + 1) γ))))
                  simp only [Function.comp_apply] at ee
                  rw [ee]
                  congr
                  simp only [ToT_prod,ToT.Later]
                  congr
                  have e := p (Γ.restrict (m + 1) γ)
                  simp only [Function.comp_apply] at e
                  rw [<- e]
                  congr
  }
def ToT.snd (X Y : ToT) : (MonoidalCategoryStruct.tensorObj X Y) ⟶ Y
  := (MonoidalCategoryStruct.whiskerRight (X.toOne) Y) ≫ (MonoidalCategoryStruct.leftUnitor Y).hom
def fixpoint (X : ToT) (f : ToT.Later.obj X ⟶ X) : ToT.one ⟶ X :=
  fixp ((MonoidalCategoryStruct.leftUnitor (ToT.Later.obj X)).hom ≫ f)
