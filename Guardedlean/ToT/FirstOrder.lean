import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Order.Category.HeytAlg
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Guardedlean.Logic
import Guardedlean.ToT.Later

universe u

open CategoryTheory

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

/--- OPERATORS ---/
def ToTPred.Or {Γ : ToT} (φ ψ : ToTPred Γ) : ToTPred Γ where
  val n γ := φ.val n γ ∨ ψ.val n γ
  property n γ p := Or.rec (λ x => .inl (φ.property n γ x)) (λ x => .inr (ψ.property n γ x)) p

def ToTPred.And {Γ : ToT} (φ ψ : ToTPred Γ) : ToTPred Γ where
  val n γ := φ.val n γ ∧ ψ.val n γ
  property n γ x := by
    constructor
    . exact φ.property n γ x.left
    . exact ψ.property n γ x.right

def ToTPred.HImp {Γ : ToT} (φ ψ : ToTPred Γ) : ToTPred Γ where
  val n γ := ∀ m (p : m ≤ n),
    φ.val m (Γ.iterRestrict m (n-m) n (by omega) γ) → ψ.val m (Γ.iterRestrict m (n-m) n (by omega) γ)
  property n γ q := by
    intro m p r
    specialize q m (by omega)
    rw [Γ.iterRestrictCast m m (n + 1 - m) (1 + (n - m)) (n+1) (n+1) rfl (by omega) rfl] at q
    rw [<-ToT.iterRestrictOne,ToT.iterRestrictComp] at *
    apply q
    exact r

def ToTPred.True {Γ : ToT} : ToTPred Γ where
  val n γ := true
  property _ _ := by simp only [imp_self]

def ToTPred.False {Γ : ToT} : ToTPred Γ where
  val n γ := false
  property _ _ := by simp only [Bool.false_eq_true, imp_self]

def ToTPred.Not {Γ : ToT} (φ : ToTPred Γ) : ToTPred Γ where
  val n γ := ∀ m, (p : m ≤ n) → φ.val m (Γ.iterRestrict m (n-m) n (by omega) γ) → false
  property n γ q := by
    intro m p r
    specialize q m (by omega)
    rw [Γ.iterRestrictCast m m (n + 1 - m) (1 + (n - m)) (n+1) (n+1) rfl (by omega) rfl] at q
    rw [<-ToT.iterRestrictOne,ToT.iterRestrictComp] at *
    apply q
    exact r

def ToTPred.Forall {Γ Δ : ToT} (f : Γ ⟶ Δ) (φ : ToTPred Γ) : ToTPred Δ where
  val n γ := ∀ (m : ℕ) (p : m ≤ n) (δ : Γ.set m),
      (f.f m δ = Δ.iterRestrict m (n-m) n (by omega) γ) → φ.val m δ
  property n γ p := by
    intro m e δ h
    apply p m (by omega)
    rw [h,<-ToT.iterRestrictOne,ToT.iterRestrictComp]
    apply ToT.iterRestrictCast Δ _ _ _ _ _ _ rfl (by omega) rfl (by omega) γ

def ToTPred.Exists {Γ Δ : ToT} (f : Γ ⟶ Δ) (φ : ToTPred Γ) : ToTPred Δ where
  val n γ := ∃ (δ : Γ.set n), (f.f n δ = γ) ∧ φ.val n δ
  property n γ x := by
    obtain ⟨δ,⟨p,q⟩⟩ := x
    exists Γ.restrict n δ
    constructor
    · subst p
      exact Eq.symm (f.restrictF n δ)
    · exact φ.prop _ _ q

/--- HeytingAlgebra (functorial) ---/
instance (Γ : ToT) : LE (ToTPred Γ) where
  le φ ψ := ∀ n γ, (φ.val n γ) → (ψ.val n γ)
instance (Γ : ToT) : HeytingAlgebra (ToTPred Γ) where
  le φ ψ := ∀ n γ, (φ.val n γ) → (ψ.val n γ)
  le_refl := by simp only [imp_self, implies_true]
  le_trans φ ψ ξ a b n γ p := b n γ (a n γ p)
  le_antisymm φ ψ a b := by
    apply Subtype.ext
    funext n γ
    exact propext ⟨a n γ,b n γ⟩ -- (a <-> b) <-> (a = b)
  sup φ ψ := ToTPred.Or φ ψ
  le_sup_left φ ψ n γ a := .inl a
  le_sup_right φ ψ n γ a := .inr a
  sup_le φ ψ ξ a b n γ p := Or.rec (λ x => a n γ x) (λ x => b n γ x) p
  inf φ ψ := ToTPred.And φ ψ
  inf_le_left φ ψ n γ p := p.left
  inf_le_right φ ψ n γ p := p.right
  le_inf φ ψ ξ a b n γ p := ⟨a n γ p, b n γ p⟩
  top := ToTPred.True
  le_top a φ n p := by simp only [ToTPred.True]
  himp φ ψ := ToTPred.HImp φ ψ
  bot := ToTPred.False
  bot_le a n γ p := by simp only [ToTPred.False,Bool.false_eq_true] at p
  compl φ := ToTPred.Not φ
  himp_bot := by simp only [ToTPred.Not,ToTPred.HImp,ToTPred.False,Bool.false_eq_true, imp_false, implies_true]
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

def ToTPred.P : CategoryTheory.Functor ToTᵒᵖ HeytAlg where
  obj := λ ⟨Γ⟩ => {α :=  ToTPred Γ}
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
      simp only at *;congr;funext n y;simp;constructor
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

def ToTPred.ForallP {Γ Δ : ToT} (f : Γ ⟶ Δ) :
  HeytAsCat.obj (ToTPred.P.obj ⟨Γ⟩) ⟶ HeytAsCat.obj (ToTPred.P.obj ⟨Δ⟩) where
  obj := λ φ => ToTPred.Forall f φ
  map := λ {φ ψ} F => by
    constructor
    constructor -- We un-PLift the morphism we construct
    simp only
    intro n γ h m e δ p
    exact F.down.down m δ (h m e δ p)
  map_comp := λ {φ ψ ξ} F G => by constructor
  map_id := λ φ => by constructor

def ToTPred.ExistsP {Γ Δ : ToT} (f : Γ ⟶ Δ) :
  HeytAsCat.obj (ToTPred.P.obj ⟨Γ⟩) ⟶ HeytAsCat.obj (ToTPred.P.obj ⟨Δ⟩) where
  obj := λ φ => ToTPred.Exists f φ
  map := λ {φ ψ} F => by
    constructor
    constructor
    simp only
    intro n γ ⟨δ,⟨p,q⟩⟩
    exact ⟨δ,⟨p,F.down.down n δ q⟩⟩
  map_comp := λ {φ ψ ξ} F G => by constructor

def ToT.LaterZero (m : ℕ) : ToT where
  set n := PLift (n ≤ m)
  restrict n x := ⟨by obtain ⟨p⟩ := x;omega⟩

def ToT.LaterZeroInj (n : ℕ) (X : ToT) (x : X.set n): ToT.LaterZero n ⟶ X where
    f := λ m ⟨e⟩ => X.iterRestrict m (n-m) n (by omega) x
    restrictF := λ m ⟨e⟩ => by
      simp only [CategoryTheory.Limits.cospan_left, LaterZero,
        CategoryTheory.Functor.const_obj_obj];
      rw [<-X.iterRestrictOne,X.iterRestrictComp]
      congr;omega
def ToT.LaterZeroCone {X Y Z : ToT} (f : X ⟶ Z) (g : Y ⟶ Z) (n : ℕ)
  (x : X.set n) (y : Y.set n) (z : Z.set n) (ex : f.f n x = z) (ey : g.f n y = z)
  : CategoryTheory.Limits.Cone (CategoryTheory.Limits.cospan f g) where
    pt := ToT.LaterZero n
    π := {
      app := fun
        | .left => ToT.LaterZeroInj n X x
        | .one => ToT.LaterZeroInj n Z z
        | .right => ToT.LaterZeroInj n Y y
      naturality := λ {A B} => fun
        | .term .left => by
          apply ToT.Hom.ext;intro m ⟨p⟩
          subst ex
          apply f.iterRestrictF
        | .term .right => by
          apply ToT.Hom.ext;intro m ⟨p⟩
          subst ey
          apply g.iterRestrictF
        | .id Z => by
          simp only [CategoryTheory.Functor.const_obj_obj,
            CategoryTheory.Limits.WidePullbackShape.hom_id, CategoryTheory.Functor.const_obj_map,
            CategoryTheory.Category.id_comp, CategoryTheory.Functor.map_id,
            CategoryTheory.Category.comp_id]
    }
def ToT.PullbackElementwise (L J K M : ToT) (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (n : ℕ) (x : K.set n) (y : J.set n) (z : L.set n) (ex : f.f n x = z) (ey : g.f n y = z)
  (eq : k ≫ f = h ≫ g) (pb : Limits.IsLimit (CommutativeSquare f g h k eq)) :
  {δ : M.set n // k.f n δ = x ∧ h.f n δ = y}
  := let kone := ToT.LaterZeroCone f g n x y z ex ey;
    .mk ((pb.lift kone).f n ⟨le_refl n⟩) (by {
      constructor
      · have a := congrArg (fun ξ => ξ.f n ⟨le_refl n⟩) (pb.fac kone .left)
        simp only [CategoryStruct.comp,CommutativeSquare] at a
        rw [a]
        simp only [Limits.cospan_left, LaterZeroCone, Functor.const_obj_obj, LaterZeroInj,
          Nat.sub_self, iterRestrictZero, kone]
      · have a := congrArg (fun ξ => ξ.f n ⟨le_refl n⟩) (pb.fac kone .right)
        simp only [CategoryStruct.comp,CommutativeSquare] at a
        rw [a]
        simp only [Limits.cospan_left, LaterZeroCone, Functor.const_obj_obj, LaterZeroInj,
          Nat.sub_self, iterRestrictZero, kone]
    })

instance : FirstOrderHyperdoctrine ToT where
  P := ToTPred.P
  rightAdj {Γ Δ} f := ToTPred.ForallP f
  leftAdj {Γ Δ} f := ToTPred.ExistsP f
  rightAdjunction {Γ Δ} f := {
    unit := {
      app := λ φ => by
        constructor
        constructor
        intros n γ q m p δ pδ
        suffices h : φ.val m (f.f m δ) by exact h
        rw [pδ]
        apply ToTPred.iterProp
        exact q
    }
    counit := {
      app := λ φ => by
        constructor
        constructor
        intros n γ q
        apply q
        · rw [Δ.iterRestrictCast _ _ (n-n) 0 _ _ rfl (by omega) rfl,Δ.iterRestrictZero]
          simp only [Quiver.Hom.unop_op']
        · simp only [le_refl]
    }
  }
  leftAdjunction {Γ Δ} f := {
    unit := {
      app := λ φ => by
        constructor
        constructor
        intro n γ q
        exists γ
    }
    counit := {
      app := λ φ => by
        constructor
        constructor
        intro n γ q
        obtain ⟨δ,⟨e,p⟩⟩ := q
        rw [<-e]
        exact p
    }
  }
  leftBeckChevalley Γ Ξ Δ Φ f g h k e p := {
    out := by
      constructor
      · constructor
        · rfl
        · rfl
      · constructor
        · intro X Y f
          constructor
        · intro ξ
          constructor
          constructor
          intro n γ p
          -- (∃.f h)((P k)(ξ))(n,γ)
          obtain ⟨δ,⟨pδ,q⟩⟩ := p
          let ⟨β,⟨βδ,βγ⟩⟩ := ToT.PullbackElementwise f g n δ γ (g.f n γ) pδ rfl c
          exists β
          constructor
          · exact βγ
          · rw [<-βδ] at q
            exact q
  }
  rightBeckChevalley Γ Ξ Δ Φ f g h k e p := {
    out := by
      constructor
      · constructor
        · rfl
        · rfl
      · constructor
        · intro X Y f
          constructor
        · intro ξ
          constructor
          constructor
          intro n γ p m pm δ pδ
          let ⟨β,⟨βδ,βγ⟩⟩ := ToT.PullbackElementwise f g m (Ξ.iterRestrict m (n-m) n (by omega) γ)
              δ (g.f m δ) (by symm;trans;exact pδ;apply f.iterRestrictF) rfl c
          rw [<-βγ]
          exact p m pm β βδ
  }
