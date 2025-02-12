import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder

namespace Guardedlean

def makeArrow : {n m : ℕ} → (p : n ≤ m) → (n ⟶ m) := λ p => ULift.up (PLift.up p)
def makeOpArrow : {n m : ℕ} → (n ≤ m) → (Opposite.op m ⟶ Opposite.op n) := λ p => Quiver.Hom.op (makeArrow p)
def unmakeArrow : {n m : ℕ} →  (p: n ⟶ m) → (n ≤ m):= λ p => PLift.down (ULift.down p)
def unmakeOpArrow : {n m : ℕ} → (p : Opposite.op m ⟶ Opposite.op n) → (n ≤ m) := λ p => unmakeArrow (Quiver.Hom.unop p)
-- TODO This lemma should exist somewhere, right ?
lemma comp_assoc {A B C D:Type} (a : A → B) (b : B → C) (c : C → D) :
  (c ∘ b) ∘ a = c ∘ (b ∘ a) := by {
    rw [Function.comp_def,Function.comp_def,Function.comp_def,Function.comp_def]
  }
lemma cast_replace {A B : Sort u} (eq eq': A = B) {x y : A} (e : x = y): eq ▸ x = eq' ▸ y := by {cases eq; cases e; rfl}

lemma cast_symm {X Y : Sort} {e : X = Y} (x : X) (y : Y): cast e x = y → x = cast (Eq.symm e) y := by intro h;cases h;rfl

@[simp]
lemma cast_poly {α β : Sort u} {φ : Sort u → Sort v} (f : {ξ : Sort u} → ξ → φ ξ) (e : α = β) (x : α)
  : f (cast e x) = cast (congrArg φ e) (f x) := by {
    cases e
    rfl
  }
@[simp]
lemma cast_poly2 {X : Sort u} {α β : X} {φ : X → Sort v} {ψ : X → Sort w} (f : {ξ : X} → φ ξ → ψ ξ) (e : α = β) (x : φ α)
  : f ((congrArg φ e) ▸ x) = (congrArg ψ e) ▸ (f x) := by {
    cases e
    rfl
  }
lemma cast_poly3 {X : Sort u} {α β : X} {φ : X → Sort v} {Y : Sort w} (f : {ξ : X} → φ ξ → Y) (e : α = β) (x : φ α)
  : @f α x = @f β (cast (congrArg φ e) x) := by {
    cases e
    rfl
  }
lemma rectocast {α: Sort u} (θ : α → Sort v) {a b : α} (h : Eq a b) (t : θ a):
  @Eq.rec α a (motive := λ x _ => θ x) t b h = cast (congrArg θ h) t := by
  cases h
  rfl
lemma Eq.rec_symm {X : Sort u} {ξ : (x : X) → Sort w} {A B : X} (e : A = B) {x : ξ A} {y : ξ B}:
  Eq.rec (motive := λ α _ => ξ α) x e = y → x = Eq.rec (motive := λ α _ => ξ α) y (Eq.symm e) := by intro h;cases h;cases e;rfl

lemma Eq.rec_lam {X : Sort u} {Y : Sort v} (ξ : (x : X) → (y : Y) → Sort w) {a : X} (f : (y : Y) → ξ a y) {b : X} (eq : a = b) :
  Eq.rec (motive := λ x _ => (y : Y) → ξ x y) (λ y => f y) eq = λ y => Eq.rec (motive := fun x _ => ξ x y) (f y) eq:= by cases eq;rfl

lemma Eq.rec_congrArg {Γ : Sort u} {A B : Γ} (e : A = B) (ξ : (x : Γ) → Sort v) (h : ξ A) :
  Eq.rec (motive := fun x _ => ξ x) h e = Eq.rec (motive := fun x _ => x) h (congrArg ξ e) := by cases e;rfl


lemma etaCast {α β γ: Sort u} {f : β → γ} {e : α = β} : (fun x:α => f (e ▸ x)) = e ▸ f := by {
  cases e
  rfl
}
@[simp]
lemma compCast {α α' β γ : Sort u} (f : α → β) (g : β → γ) {e : α = α'}: g ∘ (e ▸ f) = e ▸ (g ∘ f) := by {cases e;rfl}
@[simp]
lemma compCast2 {α β γ γ' : Sort u} (f : α → β) (g : β → γ) {e : γ = γ'}: (e ▸ g) ∘ f = e ▸ (g ∘ f) := by {cases e;rfl}

lemma compDefExt {α β γ : Sort u} (f : β → γ) (g : α → β) (x : α): f (g x) = (f ∘ g) x := by simp


-- We can do an induction on ℕ with (0,1,+)
lemma ℕsumInduction (P : ℕ → Prop) (zero : P 0) (one : P 1) (add : ∀ a b, P a → P b → P (a+b)):
  ∀ n, P n := by
  intro n
  induction n with
  | zero => apply zero
  | succ n₀ hr => cases n₀ with
  | zero => apply one
  | succ n₁ => apply add; apply hr; apply one
