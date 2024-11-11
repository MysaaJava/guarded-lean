import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Guardedlean.ToT

open CategoryTheory

namespace Guardedlean

alias ToTType := ToT
def ToTType.F (X : ToTType):= X.set
def ToTType.restr (X : ToTType):= X.restrict

def ToTType.cast {A : ToTType} (p : n = k) : A.F n → A.F k := (p ▸ ·)

@[simp]
theorem ToTType.cast_refl_id {A : ToTType} {p : n = n} {x : A.F n} :
  A.cast p x = x := by rfl

@[simp]
theorem ToTType.cast_cast_trans {A : ToTType} {p : n = k} {q : k = j} {x : A.F n} :
  A.cast q (A.cast p x) = A.cast (p.trans q) x := by subst p q;rfl

theorem Subtype.valEq : x = w -> Subtype.mk x y = Subtype.mk w z
  := λ h => by congr

/-
def ToTType.restrmaphelp (n : Nat) : (k : Nat) → F A (n + k) → F A n
  | 0, a => a
  | h+1 , a =>
    let p : (n + (h + 1)) = (n + 1 + h) := by omega
    A.restr n (restrmaphelp (n+1) h (A.cast p a))
--  | h+1 , a => restrmaphelp n h (A.restr (n+h) a)

def restrmaphelpzero
    (n k : Nat)
    (p : k = 0) (q : n + k = n)
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.cast q x := by
  cases p
  simp [ToTType.restrmaphelp]

def restrmaphelpsucc (n k : Nat)
    (p : k = k'+ 1)
    (q : n + k = n + 1 + k')
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.restr n (ToTType.restrmaphelp (n+1) k' (A.cast q x)) := by
  cases p
  simp [ToTType.restrmaphelp]

def LThelp (n m : Nat) (h : m ≤ n) : {k : Nat // m+k = n} where
  val := n-m
  property := by
--     omega
     exact Nat.add_sub_of_le h
     -- Found using apply?
     -- by omega tactic

@[simp]
def LThelpZero (m n : Nat) (p : m+1=n) (q : m+1 ≤ n) : (LThelp n (m+1) q).val = 0
  := by
      have : n-(m+1) = 0 := by omega
      unfold LThelp
      simp[this]

@[simp]
def LThelpVal (m n : Nat) (p : m ≤ n) : (LThelp n m p).val = n - m
  := by
      unfold LThelp
      simp

def ToTType.testr (n m : Nat) (p : n=m) (a : F A n) : F A m
  := p ▸ a
  -- let q : F A n = F A m := by rw[p];
  -- cast q a
-/

def ToTType.restrmap (h : m ≤ n) (a : F A n) : F A m
  := A.iterRestrict m (n-m) n (by omega) a


set_option pp.proofs.withType true

-- wrapper for ToT.iterRestrictComp
def ToTType.restrmapEq
    (p : m+1 ≤ n)
    (q : m ≤ n)
    (a : F A n)
    : A.restr m (restrmap p a) = restrmap q a
  := by simp only [restr, restrmap,<-ToT.iterRestrictOne A m _,ToT.iterRestrictComp];congr;omega

def ToTType.restrmaphelpEqInnerZero
  (m n : Nat)
  (A : ToTType)
  (p : m ≤ n + 1)
  (q : m ≤ n)
  (a : A.F (n + 1))
  (klt : m + 0 = n)
  : restrmap p a = restrmap q (A.restr n a) := by
    simp only [ToTType.restr,restrmap,<-ToT.iterRestrictOne,ToT.iterRestrictComp];congr;omega

def ToTType.restrmapEqInner
    (p : m ≤ n+1)
    (q : m ≤ n)
    (a : F A (n+1))
    : restrmap p a = restrmap q (A.restr n a) := by
    simp only [ToTType.restr,restrmap,<-ToT.iterRestrictOne,ToT.iterRestrictComp];congr;omega


alias ToTHom := ToT.Hom
def ToTHom.val (f : ToT.Hom A B) := f.f

instance : Coe Type ToTType where
  coe T := ToT.ofSet.obj T
instance : Coe Type ToT where
  coe T := ToT.ofSet.obj T

infixr:60 " ⤳ " => ToTHom

def ToTType.delta {A B : Type} (f : A → B) : A ⤳ B := ToT.ofSet.map f

def ToTType.const {A : ToTType} {B : Type} (b : B) : A ⤳ B := ToT.const b

def ToTType.id : A ⤳ A := CategoryStruct.id A

def ToTType.comp (f : A ⤳ B) (g : B ⤳ C) : A ⤳ C := @CategoryStruct.comp ToT _ A B C f g

-- Associativity, lid and rid, later, fixpoints, streams, guarded recursive types

def ToTType.Later (A : ToTType) : ToTType := ToT.Later.obj A

notation:70 "▷" T => ToTType.Later T

def ToTType.Earlier (A : ToTType) : ToTType := ToT.Earlier.obj A

notation:70 "◁" T => ToTType.Earlier T

def ToTType.delay (f : (◁ A) ⤳ B) : A ⤳ ▷B := (ToT.LaterEarlierAdj.homEquiv A B).toFun f

def ToTType.adv (f : A ⤳ ▷B) : (◁A) ⤳ B := (ToT.LaterEarlierAdj.homEquiv A B).invFun f

-- XXX def ToTType.next : A ⤳ ▷A where

-- XXX def ToTType.prev : (◁Γ) ⤳ Γ := adv (next)

def ToTType.Prod (A B : ToTType) : ToTType := @MonoidalCategory.tensorObj ToT _ _ A B

def ToTType.fst : (ToTType.Prod A B) ⤳ A
  := (@ChosenFiniteProducts.product ToT _ _ A B).cone.π.app ⟨.left⟩

def ToTType.snd : (ToTType.Prod A B) ⤳ B
  := (@ChosenFiniteProducts.product ToT _ _ A B).cone.π.app ⟨.right⟩

-- This is a syntactic sugar for the universal property of the product
def ToTType.pair (A B C : ToTType) (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B)
  := (@ChosenFiniteProducts.product ToT _ _ A B).isLimit.lift ⟨C,⟨fun ⟨x⟩ => match x with | .left => f | .right => g,λ ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by simp only at f;cases f;simp only [Functor.const_obj_obj,
    Discrete.functor_map_id, Category.id_comp, Category.comp_id]⟩⟩

def ToTType.unitFinal (A : ToTType) : A ⤳ Unit := ToT.toOne A

def ToTType.cut (A : ToTType) (n : Nat) : ToTType := ToT.cut A n

def ToTType.Fun (A B : ToTType) : ToTType := (@MonoidalClosed.closed ToT _ _ _ A).rightAdj.obj B

-- XXX Changed product order def ToTType.ev : Prod (Fun A B) A ⤳ B
def ToTType.ev : Prod A (Fun A B) ⤳ B
  := ((Adjunction.homEquiv (@MonoidalClosed.closed ToT _ _ _ A).adj) (Fun A B) B).invFun (@CategoryStruct.id ToT _ (Fun A B))

-- XXX Changed product order def ToTType.lam (f : Prod A B ⤳ C) : A ⤳ Fun B C
def ToTType.lam (f : Prod B A ⤳ C) : A ⤳ Fun B C
  := ((Adjunction.homEquiv (@MonoidalClosed.closed ToT _ _ _ B).adj) A C).toFun f


-- XXX def ToTType.deltaFun {A B : Type} (f : A → B) : Γ ⤳ Fun A B :=

-- XXX def ToTType.funcomp : Prod (Fun A B) (Fun B C) ⤳ Fun A C

-- XXX def ToTType.appfun : Prod (▷(Fun A B)) (▷A) ⤳ ▷B

-- XXX For now, fixpoint has the same type
#check fixpoint

-----------------------------------
------------- STREAM --------------
-----------------------------------
-- Show fixpoint is fixed point

def ToTType.StrF (A : Type) : Nat → Type
  | 0 => A × Unit
  | n + 1 => A × StrF A n

def ToTType.StrR (A : Type) : (n : Nat) → StrF A (n+1) → StrF A n
   | 0, (a, _) => (a, ())
   | n+1, (a, as) => (a, StrR A n as)

def ToTType.Str (A : Type) : ToTType where
  set := ToTType.StrF A
  restrict := StrR A

--def ToTType.Str.tailmap (A : Type) (xs : ToTType.Str A) : (n : Nat) →

def ToTType.StrUnfold (A : Type) (n : Nat) : (ToTType.Str A).set n = (A × (▷(ToTType.Str A)).set n)
 := by
      simp[Str,Later]
      cases n
      simp
      rfl
      simp[StrF]

def ToTType.Str.tail {A : Type} : ToTType.Str A ⤳ ▷(ToTType.Str A) where
     f
      | 0, a => a.snd
      | n+1, a => a.snd
     restrictF := by
                  intro n x
                  simp[Later]
                  cases n
                  simp
                  constructor


def ToTType.Str.headmap {A : Type} : (n : Nat) →  (as : (Str A).set n) →  A
  := fun n a => ((StrUnfold A n) ▸ a).fst

def ToTType.Str.head {A : Type} : ToTType.Str A ⤳ A where
     f := headmap
     restrictF := by
                  intro n
                  intro x
                  simp[headmap, Str, StrR]
                  induction n with
                  | zero => simp[StrR,ToT.ofSet]
                  | succ m _ => simp[Later,StrR,ToT.ofSet]

def ToTType.Str.headFun {A : Type} (str : Γ ⤳ ToTType.Str A) : Γ ⤳ A := comp str head

def ToTType.Str.consmap {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) (n : Nat) : Γ.set n → (ToTType.Str B).set n
  := fun γ => StrUnfold B n ▸ (g.f n γ, f.f n γ)

def ToTType.Str.cons {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) : Γ ⤳ (ToTType.Str B) where
  f := consmap g f
  restrictF := by
     intro n x
     simp[consmap,Str]
     induction n with
     | zero => simp[StrR]
               apply congr
               apply congr
               rfl
               exact g.restrictF 0 x
               constructor
     | succ m _ => simp[StrR]
                   apply congr
                   apply congr
                   rfl
                   exact g.restrictF (m+1) x
                   exact f.restrictF (m+1) x

-- XXX def zeros : Unit ⤳ ToTType.Str Nat := fixpoint (ToTType.Str Nat) (ToTType.Str.cons (ToTType.const 0) (ToTType.id))

--- zeros : ToTType.Str Nat := fix x. 0 :: x
--- cons (a : A) (xs : Str A) := fold (a, xs)

def Box (A : ToTType) : Type := Unit ⤳ A

abbrev Scream (A : Type) := Box (ToTType.Str A)

def force {A : ToTType} (b : Box (▷A)) : Box A where
  f := fun n => b.f (n+1)
  restrictF := by
               intro n x
               simp
               exact b.restrictF (n+1) x

def ToTType.Str.cihead {A : Type} (s : Scream A) : A := (s.f 0 ()).fst

def ToTType.Str.citail {A : Type} (s : Scream A) : Scream A := force (ToTType.comp s ToTType.Str.tail)

def ToTType.Str.take (s : Scream A) : Nat → List A
  | 0 => []
  | n+1 => cihead s :: Str.take (citail s) n

def ToTType.Str.map {A B : Type} (f : A ⤳ B) : (Str A) ⤳ (Str B) :=
  let appf : (Str A) ⤳ B
    := comp head f;
  let hdout : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ B
    := comp snd appf;
  let dgrass : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ ▷(Fun (Str A) (Str B))
    := ToTType.fst;
  let grass : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ (Fun (Str A) (Str B))
    := adv (dgrass); -- GR assumption, grass
  let tl : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str A)
    := comp snd tail;
  let delaytl : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ Str A
    := adv (tl);
  let tlout : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str B)
    := delay (comp (pair grass delaytl) ev)
  let fpterm : (▷(Fun (Str A) (Str B))) ⤳ Fun (Str A) (Str B)
    := lam (cons hdout tlout);
  let resultcurr : Unit ⤳ Fun (Str A) (Str B)
    := fixpoint (Fun (Str A) (Str B)) fpterm;
  let resultuncurr : Prod Unit (Str A) ⤳ Str B
    := comp (pair (comp fst resultcurr) snd) ev;
  comp (pair unitFinal ToTType.id) resultuncurr

def ToTType.Str.from : Nat ⤳ (Str Nat) :=
   let hdout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := snd
   let succsnd : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := comp snd (delta (fun n => n+1))
   let tlout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ ▷ (Str Nat)
     := comp (pair fst (comp succsnd next)) appfun
   let fpfuncurr : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Str Nat
     := cons hdout tlout
   let fpfun : (▷(Fun Nat (Str Nat))) ⤳ Fun Nat (Str Nat)
     := lam fpfuncurr
   let almostresult : Nat ⤳ Fun Nat (Str Nat)
     := fixp (comp snd fpfun)
   comp (pair almostresult id) ev

def ToTType.Str.natseq : Box (Str Nat) := comp (delta (fun _ => 0)) Str.from

/-- info: [0, 1, 2, 3, 4, 5, 6, 7] -/
#guard_msgs in
#eval ToTType.Str.take (ToTType.Str.natseq) 8

/-- info: [5, 5, 5, 5, 5, 5, 5, 5] -/
#guard_msgs in
#eval ToTType.Str.take pretty_from 8

--#eval ToTType.Str.take zeros 8
/-- info: [0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval ToTType.Str.take pretty_zeros 8

--#check Nat ⤳ Nat

-- Start of families part

structure ToTType.Fam (Γ : ToTType) where
  F : (n : Nat) → Γ.F (n) → Type
  restr : {n : Nat} → {γ : Γ.F (n + 1)} → F (n+1) γ → F n (Γ.restr n γ)

def ToTType.AsFam (A : ToTType) : Fam Γ where
  F n _ := A.F n
  restr {n} := A.restr n

def ToTType.SubstHelp {A : Fam Γ} {f : Δ ⤳ Γ} {n : Nat} {δ : Δ.F (n+1)} (a : A.F n (Γ.restr n (f.val (n+1) δ)) ) : A.F n (f.val n (Δ.restr n δ)) :=
  f.property n δ ▸ a

def ToTType.Subst (A : Fam Γ) (f : Δ ⤳ Γ) : Fam Δ where
  F n δ := A.F n (f.val n δ)
  restr a := SubstHelp (A.restr a)

def ToTType.Elem (Γ : ToTType) (A : Fam Γ) : Type
    := {f : (n : Nat) → (γ : Γ.F n) → A.F n γ // (∀n γ, A.restr (f (n+1) γ)= f n (Γ.restr n γ))}

def ToTType.AsElem (f : Γ ⤳ A) : Elem Γ (AsFam A) where
   val n γ := f.val n γ
   property := by
     intro n γ
     simp[AsFam]
     exact f.property n γ

def ToTType.Compr (A : Fam Γ) : ToTType where
  F n := (γ : Γ.F n)× (A.F n γ)
  restr n ga := let ⟨γ,a⟩ := ga;
                let γ' := Γ.restr n γ;
                let a' := A.restr a;
                ⟨γ', a'⟩

-- Maybe better to just do logic?

def ToTType.ToTPred (Γ : ToTType) : Type
  := {φ : {n : Nat} → (γ : Γ.F n) → Prop // ∀ n γ, φ γ → φ (Γ.restr n γ)}

def ToTType.AsToTPred (φ : A → Prop) : ToTPred A where
  val := φ
  property := by
    intro n γ
    simp



/-- instance {A : Type} : Coe (A → Prop) (ToTPred A) where
  coe T := { F := fun _ => T, restr := fun _ => id}
  --/

def ToTType.PredSubst (φ : ToTPred Γ) (σ : Δ ⤳ Γ) : ToTPred Δ where
  val {n} δ := φ.val (σ.val n δ)
  property := by
    intro n γ
    simp
    have p := σ.property n γ
    rw[← p]
    exact φ.property n (σ.val (n + 1) γ)


def ToTType.AsToTPred' (φ : A → Prop) : ToTPred (Prod Unit A) :=
  PredSubst (AsToTPred φ) snd



def ToTType.PCompr (φ : ToTPred Γ) : ToTType where
  F n := {γ : Γ.F n // φ.val γ}
  restr n γp := ⟨ Γ.restr n γp.val , φ.property n γp.val γp.property ⟩

def ToTType.PComprPr (φ : ToTPred Γ) : (PCompr φ) ⤳ Γ where
  val := fun n γp => γp.val
  property := by
    simp
    intro n x
    simp[PCompr]

/-- Weakening by a predicate-/
def ToTType.PredWeak (φ ψ : ToTPred Γ) : ToTPred (ToTType.PCompr φ)  := ToTType.PredSubst ψ (PComprPr φ)



def ToTType.Proof (Γ : ToTType) (φ : ToTPred Γ) : Prop :=
  ∀ n (γ : Γ.F n), φ.val γ



def ToTType.AsToTProof (p : ∀ x, φ x) : Proof _ (AsToTPred φ) :=
  by
    simp[Proof]
    intro n γ
    simp[AsToTPred]
    exact p γ


-- The next one reintroduces sequents under different name
def ToTType.ProofImpl (φ ψ : ToTPred Γ) : Prop :=
  Proof _ (PredWeak φ ψ)

-- Forget about sequents, use Proof
/--
def ToTType.Sequent (φ ψ : ToTPred Γ) : Prop
  := ∀ n (γ : Γ.F n), (φ.val γ) → (ψ.val γ)

def ToTType.SeqTrivial : Sequent φ φ :=
  by
    sorry

def ToTType.SeqComp (ρ φ ψ : ToTPred Γ) (p : Sequent ρ φ) (q : Sequent φ ψ) : Sequent ρ ψ :=
  by
   simp[Sequent]
   intro n γ
   intro a
   exact (q n γ (p n γ a))

-/

def ToTType.Conj (φ ψ : ToTPred Γ) : ToTPred Γ where
  val γ := φ.val γ ∧ ψ.val γ
  property := by
    intro n γ
    simp
    intro  p q
    constructor
    . exact φ.property n γ p
    . exact ψ.property n γ q

def ToTType.ConjIntro (p : Proof _ φ) (q : Proof _ ψ) : Proof _ (Conj φ ψ) :=
  by sorry

def ToTType.ConjElimL (p : Proof _ (Conj φ ψ)) : Proof _ φ :=
  by sorry

def ToTType.ConjElimR (p : Proof _  (Conj φ ψ)) : Proof _  ψ :=
  by sorry

def ToTType.Impl (φ ψ : ToTPred Γ) : ToTPred Γ where
 val {n} γ := ∀ m, (p : m ≤ n) → φ.val (restrmap p γ) → ψ.val (restrmap p γ)
 property := by
   intro n γ q m p r
   have s := restrmapEqInner (m:=m) (n:= n) (by omega) p γ
   rw[← s] at r
   have t := q m (by omega) r
   rw[s] at t
   exact t

def ToTType.ImplIntro (p : Proof  (Γ := PCompr φ) (PredWeak φ ψ)) : Proof _  (Impl φ ψ) :=
  by
   simp_all[Proof]
   intro n γ
   -- apply p n
   simp[Impl]
   intro m q r
   simp_all[PCompr,PredSubst,PComprPr]
   exact p m (⟨restrmap q γ, r ⟩)

/--
def ToTType.ConjIntro (ρ φ ψ : ToTPred Γ) (p : Sequent ρ φ) (q : Sequent ρ ψ) : Sequent ρ (Conj φ ψ) :=
  by
    simp[Sequent]
    intro n γ r
    simp[Conj]
    constructor
    . exact p n γ r
    . exact q n γ r

def ToTType.ConjElimL (ρ φ ψ : ToTPred Γ) (p : Sequent ρ (Conj φ ψ)) : Sequent ρ φ :=
  by
    simp[Sequent]
    intro n γ q
    have r := p n γ q
    let ⟨r1 , _ ⟩ :=  r
    exact r1

def ToTType.ConjElimR (ρ φ ψ : ToTPred Γ) (p : Sequent ρ (Conj φ ψ)) : Sequent ρ ψ :=
  by
    simp[Sequent]
    intro n γ q
    have r := p n γ q
    let ⟨ _ , r2 ⟩ :=  r
    exact r2
-/

def ToTType.Forall (φ : ToTPred (Prod Γ Δ)) : ToTPred Γ where
  val {n} γ := ∀ m, (p : m≤ n) → ∀ δ , φ.val ⟨ restrmap p γ , δ ⟩
  property := by
    intro n γ
    simp
    intro q
    intro m p δ
    have r := q m (by omega) δ
    have s := restrmapEqInner (m:=m) (n:= n) (by omega) p γ
    rw[s] at r
    exact r


def ToTType.prodOverCompr : PCompr (Γ := (Prod Γ Δ)) (PredSubst φ fst) ⤳ Prod (PCompr (Γ := Γ) φ) Δ where
  val n γ' :=
    let ⟨(γ, δ), p⟩ := γ'
    (⟨γ, p⟩, δ)
  property := by
    intro n x
    let ⟨(γ, δ), p⟩ := x
    simp[PCompr, PredSubst,Prod]

def ToTType.comprOverProd : Prod (PCompr (Γ := Γ) φ) Δ ⤳ PCompr (Γ := (Prod Γ Δ)) (PredSubst φ fst) where
  val n γ' :=
    let ⟨⟨γ, p⟩, δ⟩ := γ'
    ⟨(γ, δ), p⟩
  property := by
    intro n x
    let ⟨⟨γ, p⟩, δ⟩ := x
    simp[PCompr, PredSubst,Prod]

def isConst (f : α → β) := ∃ (y : β), ∀ (x : α), f x = y

def isConst' (f : α → β) := ∀ x y, f x = f y



@[simp]
theorem ToTType.cast_eq : HEq (cast h a) a := by
  cases h
  simp [cast]


theorem eq_rec_trans (x : γ) (p1 : α = β) (p2 : β = γ) : p1 ▸ p2 ▸ x = (p1.trans p2) ▸ x := by
  cases p1
  simp

theorem ToTType.restrmaphelp_const {A : ToTType} (c : isConst' A.F) (a : A.F (n + k)) :
    (∀ n x, A.restr n x = (c _ _).mp x) → restrmaphelp n k a = (c _ _).mp a := by
  intro constRestr
  induction k generalizing n with
  | zero =>
    have := restrmaphelpzero n 0 rfl rfl a
    simp only [Nat.add_zero, cast_refl_id] at this; trivial
  | succ k' ih =>
    have := restrmaphelpsucc n (k' + 1) rfl (by omega) a
    rw [this]
    have h : n + (k' + 1) = n + 1 + k' := by omega
    have := constRestr n (restrmaphelp (n + 1) k' (cast h a))
    simp_all only; clear this
    simp [Eq.mp]
    rw [eq_rec_trans] <;> try (apply c)
    have : A.F (n + (k' + 1)) = A.F (n + 1 + k') := by apply c
    congr 1
    . apply c
    . rw [h]
    . apply cast_eq
    . rw [h]



theorem ToTType.restrmap_const_id (A : ToTType) (c : isConst' A.F) :
    (∀ n x, A.restr n x = (c _ _).mp x) → (x : A.F m) →
    restrmap (m := n) (A := A) p x = (c _ _) ▸ x := by
  intro constRestr
  intros
  simp [restrmap]
  rw [restrmaphelp_const] <;> try trivial
  congr 1
  . apply c
  . exact heq_of_eqRec_eq (congrFun (congrArg Eq (c (n + (LThelp m n p).val) m)) (A.F n)) rfl
  . exact cast_eq


def ToTType.PredWeakForall {φ : ToTPred Γ} {ψ : ToTPred (Γ.Prod A)} :
    Proof _  (PredWeak φ (Forall ψ)) ↔ Proof _  (Forall (PredSubst (PredWeak (PredSubst φ fst) ψ) comprOverProd))
  := by
  constructor
  . intro p
    simp[Proof, Forall, PredSubst, PredWeak,PComprPr, comprOverProd]
    intro n γ m m_le_n δ
    simp[Proof, Forall, PredSubst, PredWeak,PComprPr, comprOverProd] at p
    let r := p n γ m m_le_n δ
    simp[Prod,PCompr]
    let s := restrmap_nat (PComprPr φ) n m m_le_n γ
    simp[PComprPr] at s
    rw[s]
    exact r
  . intro h
    intro n γ
    simp [PredWeak, PredSubst, Forall, PComprPr]
    intro m m_le_n δ
    have r := restrmap_nat (PComprPr φ) n m m_le_n γ
    simp [PComprPr] at r
    simp [PCompr, Proof, PredSubst, Forall, PredWeak] at γ h
    have := h n γ m m_le_n δ
    simp [PComprPr, comprOverProd] at this
    rw[r] at this
    exact this










def ToTType.ForallCl (φ : ToTPred Γ) : ToTPred Unit :=
  Forall (PredSubst φ snd)

def ToTType.ForallIntro {φ : ToTPred (Prod Γ A)} (p : Proof _  φ) : Proof (Γ := Γ) (Forall φ) :=
  by sorry

def ToTType.ForallIntroCl (p : Proof _  φ) : Proof _  (ForallCl φ) :=
  by sorry

def ToTType.ForallElim {φ : ToTPred (Prod Γ Δ)} (p : Proof _  (Forall φ)) : Proof _  φ :=
  by sorry

def ToTType.ForallElimCl (p : Proof _  (ForallCl φ)) : Proof _  φ :=
  by sorry

/--
def ToTType.ForallIntro (p : Sequent (PredSubst φ fst) ψ) : Sequent φ (Forall ψ) :=
  by
    sorry

def ToTType.ForallElim (p : Sequent φ (Forall ψ)) : Sequent (PredSubst φ fst) ψ :=
  by
    sorry

def ToTType.ForallClIntro (p : Sequent (PredSubst φ fst) ψ) : Sequent φ (ForallCl ψ) :=
  by
    sorry

def ToTType.ForallClElim (p : Sequent φ (ForallCl ψ)) : Sequent (PredSubst φ fst) ψ :=
  by
    sorry
-/

def ToTType.True (Γ : ToTType) : ToTPred Γ where
  val γ := true
  property := by
    intro n _
    simp

def ToTType.Top {Γ : ToTType} : Proof _  (True Γ) :=
  by
    simp[Proof]
    intro n γ
    simp[True]

structure ToTType.proofsOf (φ : Prop) : Type where
  proof : φ
--{ x : Unit // φ}

def ToTType.proofsOfEl (φ : Prop) (p : φ) : (proofsOf φ) := ⟨ p ⟩

def ToTType.proofsOfImp (p : φ → ψ) (x : proofsOf φ) : (proofsOf ψ) :=
  let ⟨ q ⟩ := x
  ⟨ p q ⟩
--  proofsOfEl ψ (p (x.property))
--  val := x.val
--  property := p x.property

def ToTType.UnitSet (x y : Unit) : x=y :=
  by
   ext

@[simp]
def ToTType.proofsOfSet (x y : proofsOf φ) : x = y :=
  by
   cases x
   cases y
   rfl

def ToTType.Yoneda (n : Nat) : ToTType where
  F {m} := proofsOf (m ≤ n)
  restr m := proofsOfImp (by omega)

def ToTType.YonMap (p : m ≤ n) : (Yoneda m) ⤳ (Yoneda n) where
  val o q := proofsOfEl (o ≤ n) (by let r : (o ≤ m) := q.proof ; omega)
  property := by
    intro n x
    apply proofsOfSet


def ToTType.ToTProp : ToTType where
  F n := ToTPred (Yoneda n)
  restr n φ :=
    let f : (Yoneda n) ⤳ (Yoneda (n+1)) := YonMap (by omega)
    PredSubst φ f

-- PredPi Γ is the Π type Π Γ ToTProp
-- def ToTType.PredPi (Γ : ToTType) : ToTType where
--   F n := ToTPred (Prod Γ (Yoneda n))
--   restr n φ :=
--     let f : (Prod Γ (Yoneda n)) ⤳ (Prod Γ (Yoneda (n+1))) := ProdHom ToTType.id (YonMap (by omega))
--     PredSubst φ f

def ToTType.Code (φ : ToTPred Γ) : Γ ⤳ ToTProp where
  val n γ :=
    let ψ := fun {m} y => φ.val (restrmap y.proof γ)
    let prop : ∀ (m : Nat) (ρ : (Yoneda n).F (m+1)) , ψ ρ → ψ ((Yoneda n).restr m ρ) :=
      by
       intro m ρ p
       simp[ψ]
       simp[ψ] at p
       let q := φ.property m _ p
       let mn := ρ.proof
       let r:= @ToTType.restrmapEq m n Γ mn (by omega) γ
       rw [← r]
       apply q
    ⟨ ψ , prop ⟩
  property := by
    sorry

def ToTType.PropEl : ToTPred Γ := True Γ

def ToTType.PropElem (f : Γ ⤳ ToTProp) : ToTPred Γ  :=
  PredSubst PropEl f

/- def ToTType.PLaterVal (φ : ToTPred (◁ Γ)) : {n : Nat} → (γ : Γ.F n) → Prop
  | 0, _ => true
  | _+1, γ => φ.val γ

def ToTType.PLater (φ : ToTPred (◁ Γ)) : ToTPred Γ where
  val := PLaterVal φ
  property := by
    intro n
    cases n
    . simp[PLaterVal]
    . simp[PLaterVal]
      apply φ.property
 -/

def ToTType.PLaterVal (φ : ToTPred Γ) : {n : Nat} → (γ : (▷ Γ).F n) → Prop
  | 0, _ => true
  | _+1, γ => φ.val γ

def ToTType.PLater (φ : ToTPred Γ) : ToTPred (▷ Γ) where
  val := PLaterVal φ
  property := by
    intro n
    cases n
    . simp[PLaterVal]
    . simp[PLaterVal]
      apply φ.property

def ToTType.PLaterFib (φ : ToTPred Γ) : ToTPred Γ :=
  PredSubst (PLater φ) next

def ToTType.PLatBind (φ : ToTPred (◁ Γ)) : ToTPred Γ :=
  PredSubst (PLater φ) (delay  (ToTType.id))

def ToTType.PEarlier (φ : ToTPred Γ) : ToTPred (◁ Γ) where
  val := φ.val
  property := by
    intro n γ
    apply (φ.property (n+1) γ)


-- def ToTType.Pfix (p : Sequent (Conj φ (PredSubst (PLater ψ) ToTType.next)) ψ) : Sequent φ ψ  :=
def ToTType.Pfix (φ : ToTPred Γ) (p : Proof _ (PredWeak (PLaterFib φ) φ)) : Proof _  φ  :=
  by
    sorry

/-- def ToTType.PfixCl (p : Sequent (PredSubst (PLater ψ) ToTType.next) ψ) : Sequent True ψ :=
  -- Pfix (SeqComp (ConjElimR (Conj True (PredSubst (PLater ψ) ToTType.next)) True (PredSubst (PLater ψ) ToTType.next) SeqTrivial) p)
  by
    sorry
--/

def ToTType.PLaterProp : ToTPred (▷ ToTProp) := PLater (True ToTProp)

--def ToTType.PBox (φ : ToTPred Γ) (γ : Box Γ) : Prop :=
-- Sequent True φ

def ToTType.PredLiftStr {A : Type} (ψ : A → Prop) : ToTPred (ToTType.Str A) :=
  let φ := AsToTPred ψ
  let hd : (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) ⤳ A := comp snd Str.head
  let tl : (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) ⤳ (▷ (Str A)) := comp snd Str.tail
  let tlcond : ToTPred (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) := PredSubst PLaterProp (comp (pair fst tl) appfun)
  let help : ToTPred (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) := Conj (PredSubst φ hd) tlcond
  let helper : (▷ (Fun (Str A) ToTProp)) ⤳ (Fun (Str A) ToTProp) := lam (Code help)
  let f : Unit ⤳ (Fun (Str A) ToTProp) := (fixpoint (Fun (Str A) ToTProp) helper)
  let g : (Str A)  ⤳ ToTProp := comp (pair (comp unitFinal f) id) ev
  PropElem g

-- def ToTType.PredLiftStrFold : Sequent (Conj (PredSubst φ hd) (PredSubst (PLater (PredLiftStr φ)) Str.tail)) (PredLiftStr φ) :=
  def ToTType.PredLiftStrFold (p : Proof _  (PredSubst (AsToTPred φ) hd)) (q : Proof _  (PredSubst (PLater (PredLiftStr φ)) Str.tail)) : Proof _  (PredLiftStr φ) :=
    by sorry

def ToTType.PredLiftStrHelp {φ : A → Prop} (p : forall a, φ a)
   : ProofImpl (PLaterFib (ForallCl (PredLiftStr φ))) (ForallCl (PredLiftStr φ))
   :=
  let hdproof : ProofImpl (PredSubst (PLaterFib (ForallCl (PredLiftStr  φ))) fst) (PredSubst (AsToTPred φ) Str.head) :=
    by
      sorry
  let tlproof : ProofImpl (PredSubst (PLaterFib (ForallCl (PredLiftStr φ))) fst) (PredSubst (PLater (PredLiftStr φ)) Str.tail) :=
    by
      sorry
  ForallIntro (PredLiftStrFold hdproof tlproof)



def ToTType.PredLiftStrProof (p : Proof _  φ) : Proof _  (ForallCl (PredLiftStr φ)) :=
  ForallIntroCl (Pfix _)

-- Add tail condition to the below
def ToTType.PredLiftStrPretty  {A : Type} : Box (((A : ToTType).Fun ToTProp).Fun ((ToTType.Str A).Fun ToTProp)) :=
  box(fun (φ : _) => fix (ψ : ((Str A).Fun ToTProp)) => fun (xs : _)  => φ (head(xs)))

axiom LiftPredStr {Γ} {A} : (φ : A → Prop) → ToTType.ToTPred (ToTType.Prod Γ (ToTType.Str A))

axiom ToTType.LiftPredStrWeak {Γ} {A} {φ} : Proof (Prod Γ (ToTType.Str A)) (LiftPredStr φ)  → Proof _ (PredWeak (LiftPredStr φ) _)

declare_syntax_cat ctxt
declare_syntax_cat ctxt_elem
declare_syntax_cat stmt
syntax "✓" : ctxt_elem
syntax (name:=binder) ident " ∈ " term : ctxt_elem
syntax ident " : " stmt : ctxt_elem
syntax ctxt_elem : ctxt
syntax "·" : ctxt
syntax ctxt ", " ctxt_elem : ctxt

syntax stmt " → " stmt : stmt
syntax ident : stmt
syntax "∀ " ident ", " stmt : stmt
syntax "∀ " ident " : " term ", " stmt : stmt
syntax "[" term "] " ident* : stmt -- apply ToT-pred in Lean syntax to arguments
syntax "(" stmt ")" : stmt
syntax "↑" term : stmt -- lift predicate to stream
syntax "![" ctxt " | " stmt "]" : term
syntax "!{" ctxt "}" : term
syntax "![" stmt "]" : term
syntax "¡" ctxt " | " ident* "!" : term
syntax "¡" ctxt "€" ident "!" : term

declare_syntax_cat tot_proof_state
syntax (ctxt_elem ppLine)* "⊨ " stmt : tot_proof_state
namespace Internals
scoped syntax (name:=embedProof) tot_proof_state : term
end Internals

open Lean in
macro_rules
  | `(¡ $_ | !) => `((ToTType.unitFinal ))
  | `(¡ $Γ | $xs:ident* $x:ident !) => `(ToTType.pair ¡ $Γ | $xs* ! ¡ $Γ € $x !)
  | `(¡ · € $x !) => Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡ $y:ident ∈ $_:term € $x:ident !) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡ $Γ, $y:ident ∈ $_:term € $x:ident !) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else ``(ToTType.comp ToTType.fst ¡ $Γ € $x !)



macro_rules
  | `(![$Γ | ($s)]) => `(![$Γ | $s])
  | `(![$s]) => `(![· | $s])
  | `(![ $Γ | $s1 → $s2]) => `(ToTType.Impl ![$Γ | $s1] ![$Γ | $s2])
  | `(![ $Γ | ∀ $x:ident, $s:stmt]) =>
    `(let t := _; ToTType.Forall (Δ := t) ![$Γ, $x:ident ∈ t | $s])
  | `(![ $Γ | ∀ $x:ident : $t, $s]) =>
    `(let t := $t; ToTType.Forall (Δ := t) ![$Γ, $x:ident ∈ t | $s])
  | `(![ $_ | True]) => `(ToTType.True _)
  | `(![ $Γ | [ $pred ] $arg*]) =>
    ``(ToTType.PredSubst $pred (¡ $Γ | $arg* !))
  | `(!{·}) => ``((Unit : ToTType))
  | `(!{✓}) => ``((◁ Unit : ToTType))
  | `(!{$Γ:ctxt, ✓}) => ``((◁ !{$Γ} : ToTType))
  | `(!{$x:ident ∈ $t}) => ``((ToTType.Prod Unit $t : ToTType))
  | `(!{$Γ, $x:ident ∈ $t}) =>
    ``((ToTType.Prod !{$Γ} $t : ToTType))
  | `(!{$x:ident : $t}) => ``((@ToTType.PCompr Unit ![· | $t] : ToTType))
  | `(!{$Γ:ctxt, $x:ident : $t}) =>
    ``((@ToTType.PCompr !{$Γ} ![$Γ | $t] : ToTType))
/-- info: { F := fun x => Unit, restr := fun x => id } : ToTType -/
#guard_msgs in
#check !{·}

/--
info: { F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id } : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat}

/--
info: (◁({ F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id }).Prod
        { F := fun x => String, restr := fun x => id }).Prod
  { F := fun x => Nat, restr := fun x => id } : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat}

/--
info: ToTType.PCompr
  ((◁({ F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id }).Prod
            { F := fun x => String, restr := fun x => id }).Prod
      { F := fun x => Nat, restr := fun x => id }).True : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : True}

#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : ∀ x, True}

#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : ∀ x : Int, True}

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabArgs : DelabM (TSyntaxArray `ident) := do
  let e ← getExpr
  match_expr e with
  | ToTType.unitFinal _ => pure #[]
  | ToTType.pair _ _ _ _ _ =>
    let pre ← withAppFn <| withAppArg delabArgs
    let me ← withAppArg <| annAsTerm <| ← `(ident|x)
    return pre.push me
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabMorph : DelabM (TSyntaxArray `ident) := do
  let e ← getExpr
  match_expr e with
  | ToTType.unitFinal _ => pure #[]
  | ToTType.pair _ _ _ _ _ =>
    let pre ← withAppFn <| withAppArg delabArgs
    let me ← withAppArg <| annAsTerm <| ← `(ident|x)
    return pre.push me
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabStmtInner : DelabM (TSyntax `stmt) := do
  let e ← getExpr
  let stx ←
    match e with
    | .letE _ _ _ body _ => withLetBody delabStmtInner
    | _ =>
    match_expr e with
    | ToTType.Impl _ _ _ =>
      let s1 ← withAppFn <| withAppArg delabStmtInner
      let s2 ← withAppArg delabStmtInner
      `(stmt| $s1 → $s2)
    | ToTType.Forall _ _ _ =>
      let x := mkIdent (← mkFreshBinderName)
      let body ← withAppArg delabStmtInner
      `(stmt| ∀ $x, $body)
    | ToTType.PredSubst _ _ _ _ =>
      let pred ← withAppFn <| withAppArg delab
      let args ← withAppArg delabArgs

      `(stmt| [$pred] $args*)
    | ToTType.PredWeak _ _ _ =>
      withAppArg delabStmtInner
    | _ =>
      `(stmt| [$(← delab)])
  annAsTerm stx

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabProofCtxt : DelabM (TSyntaxArray `ctxt_elem) := do
  match_expr ← getExpr with
  | ToTType.PCompr _ _ =>
    let Γ ← withAppFn <| withAppArg delabProofCtxt
    let φ ← withAppArg do delabStmtInner
    return Γ.push (← withAppArg <| annAsTerm (← `(ctxt_elem|x : $φ)))
  | ToTType.mk _ _ =>
    withAppFn <| withAppArg do
      match (← getExpr) with
      | .lam _ _ _ _ =>
        withBindingBody `x do
          match_expr (← getExpr) with
          | Unit =>
            pure #[]
          | _ =>
          failure
      | _ => failure
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
open Internals in
@[delab app.ToTType.Proof]
partial def delabProof : Delab := do
  match_expr ← getExpr with
  | ToTType.Proof _ _ =>
    let stmt ← withAppArg delabStmtInner
    let ctxt ← withAppFn <| withAppArg delabProofCtxt
    let prf ← `(tot_proof_state| $[$ctxt]* ⊨ $stmt)
    pure ⟨prf.raw⟩
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
@[delab app.ToTType.Impl, delab app.ToTType.Forall, delab app.ToTType.PredSubst, delab app.ToTType.PredWeak]
partial def delabStmt : Delab := do
  -- This delaborator only understands a certain arity - give up if it's incorrect
  guard <| match_expr ← getExpr with
    | ToTType.Impl _ _ _ => true
    | ToTType.Forall _ _ _ => true
    | ToTType.PredSubst _ _ _ _=> true
    | ToTType.PredWeak _ _ _ => true
    | _ => false
  match ← delabStmtInner with
  | `(stmt|[$e]) => pure e
  | e => `(term|![$(⟨e⟩)])


namespace Internals
scoped syntax "builtinIntro" : tactic
macro_rules | `(tactic|builtinIntro) => `(tactic|intro)
end Internals

syntax (name := ourIntro) "intro" : tactic

open ToTType in
open Internals in
macro_rules (kind := ourIntro)
  | `(tactic|intro) =>
    `(tactic|first | apply ImplIntro | apply ForallIntro | builtinIntro)



theorem ToTType.liftOk (φ : A → Prop) : Proof _ (Impl (ForallCl (AsToTPred φ)) (ForallCl (LiftPredStr φ))) := sorry

theorem ToTType.liftOk' (φ : A → Prop) : Proof (Γ := Unit) ![ (∀ x : A, [AsToTPred' φ] x) → (∀ xs : Str A, [LiftPredStr φ] xs) ] := by
  intro
  rw [PredWeakForall]
  apply Pfix
  rw [PredWeakForall]
  apply ForallIntro
  sorry


-- @Proof ?Γ (![∀ x✝, [?φ] ]) : Prop

--    @Forall ?Γ ?A ?φ : ?Γ.ToTPred

-- @Proof
--   (PCompr
--     (let t := A;
--     ![∀ x✝, [AsToTPred' φ] x✝]))
--   (![∀ x✝, [LiftPredStr φ] x✝]) : Prop

--    @PredWeak { F := fun x => Unit, restr := fun x => _root_.id }
--     (let t := A;
--     ![∀ x✝, [AsToTPred' φ] x✝])
--     (let t := Str A;
--     ![∀ x✝, [LiftPredStr φ] x✝]) : (PCompr
--       (let t := A;
--       ![∀ x✝, [AsToTPred' φ] x✝])).ToTPred

theorem ToTType.liftOk'AfterIntro (φ : A → Prop) :
    Proof (Γ := ToTType.PCompr (Γ := Unit) ![(∀ x : A, [AsToTPred' φ] x)]) ![ (∀ xs : Str A, [LiftPredStr φ] xs) ] := by
  skip

-- TODO next time: we just finished intro tactic for implication, next time do it for universal quantification. Current progress: weakening is getting in the way. We think we need PredWeakForall above, but didn't finish it.

/-
  Sketch proof using tactics:
   Assumption: φ : A → Prop
   Construct LiftPredStr φ : Pred (Str A) such that LiftPredStr φ (xs) equivalent to
   φ(hd(xs)) ∧ ▷ LiftPredStr φ (adv(tl(xs)))
   Want to prove
   (∀ x, φ (x)) → ∀ xs, LiftPredStr φ xs
   Proof should proceed as follows:
     intro p
     guarded_recursion
       At this point the context should be
         p : ∀ x, φ (x)
         IH : ▷ (∀ xs, LiftPredStr φ xs)
     intro xs
     [Something to unfold LiftPredStr φ xs]
    constructor/conjIntro  (not sure what the tactic name is, need to prove conjunction)
     . apply p
     . tickintro
         At this point context is
            p : ∀ x, φ (x)
            IH : ▷ (∀ xs, LiftPredStr φ xs)
            xs : Str A
            tick
          Must prove
          LiftPredStr φ (adv(tl(xs)))
        exact (adv IH (adv (tl(xs))))

  -/
