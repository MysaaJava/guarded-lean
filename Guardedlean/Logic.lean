import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.Order.Category.HeytAlg
import Guardedlean.Lemmas
import Guardedlean.CategoryTheory.PreservesChosen
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

open CategoryTheory
open CategoryTheory.Limits

namespace Guardedlean

def bicatId {C : Type u} [Bicategory C]
  {A B : C} {F G : A ⟶ B} (e : F = G) : F ⟶ G := e ▸ 𝟙 F

def CommutativeSquare {T : Type u} [Category.{v} T]
  {L J K M : T} (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (eq : k ≫ f = h ≫ g) : Limits.Cone (Limits.cospan f g) where
    pt := M
    π := {
      app := fun
      | .left => k
      | .right => h
      | .one => k ≫ f
      naturality := λ _ _ => fun
      | .term .left => by simp only [Functor.const_obj_obj, Limits.cospan_one,
        Functor.const_obj_map, Category.id_comp, Limits.cospan_left, Limits.cospan_map_inl]
      | .term .right => by simp only [Functor.const_obj_obj, Limits.cospan_one,
        Functor.const_obj_map, Category.id_comp, Limits.cospan_right, Limits.cospan_map_inr,eq]
      | .id x => by simp only [Functor.const_obj_obj, Limits.WidePullbackShape.hom_id,
        Functor.const_obj_map, Limits.cospan_one, Category.id_comp, CategoryTheory.Functor.map_id,
        Category.comp_id]
   }

-- ID cell in a commutative square, casted to a 2-cell from one branch to another
def Comm2Cell {T : Type u} [Category.{v} T]
  (P : T ⥤ Cat)
  {L J K M : T} (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (eq : k ≫ f = h ≫ g) : (P.map k) ≫ (P.map f) ⟶ (P.map h) ≫ (P.map g)
  := @bicatId _ _ _ _ ((P.map k) ≫ (P.map f)) ((P.map h) ≫ (P.map g)) (by rw [<-P.map_comp,<-P.map_comp,eq])

def cospanMapEq {T : Type u₁} [Category.{v₁} T] {U : Type u₂} [Category.{v₂} U] (F : T ⥤ U)
  {L J K : T} (f : K ⟶ L) (g : J ⟶ L) :
  Limits.cospan (F.map f) (F.map g) = (Limits.cospan f g) ⋙ F:= by
    apply CategoryTheory.Functor.ext
    · intro X Y x
      match x with
      | .term .left => simp only [Limits.cospan_left, Limits.cospan_one, Limits.cospan_map_inl,
        Functor.comp_obj, eqToHom_refl, Functor.comp_map, Category.comp_id, Category.id_comp]
      | .term .right => simp only [Limits.cospan_right, Limits.cospan_one, Limits.cospan_map_inr,
        Functor.comp_obj, eqToHom_refl, Functor.comp_map, Category.comp_id, Category.id_comp]
      | .id Z => simp only [Limits.WidePullbackShape.hom_id, CategoryTheory.Functor.map_id,
        Functor.comp_obj, Functor.comp_map, Category.id_comp, eqToHom_trans, eqToHom_refl]
    · intro X
      match X with
      | .left => simp only [Limits.cospan_left, Functor.comp_obj]
      | .right => simp only [Limits.cospan_right, Functor.comp_obj]
      | .one => simp only [Limits.cospan_one, Functor.comp_obj]

def ConeCast {D : Type u} [Category D] {C : Type v} [Category C] {F G : D ⥤ C} (e: F = G)
    (pt : C) (π : (Functor.const D).obj pt ⟶ F):
   e ▸ (Limits.Cone.mk pt π) = Limits.Cone.mk pt (e ▸ π) := by cases e;rfl
def NatTransCast {D : Type u} [Category D] {C : Type v} [Category C] {P F G : D ⥤ C} (e : F = G)
  (η :  (X : D) → P.obj X ⟶ F.obj X) (nat: ∀ ⦃X Y : D⦄ (f : X ⟶ Y), P.map f ≫ (fun x => η x) Y = (fun x => η x) X ≫ F.map f):
  e ▸ NatTrans.mk η nat = NatTrans.mk (e ▸ η) (λ X Y f => by subst e;simp_all only) := by cases e;rfl

def CommutativeSquareMap {T : Type u₁} [Category.{v₁} T] {U : Type u₂} [Category.{v₂} U] (F : T ⥤ U)
  {L J K M : T} (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (eq : k ≫ f = h ≫ g) :
  F.mapCone (CommutativeSquare f g h k eq) =
  cospanMapEq F f g ▸ CommutativeSquare (F.map f) (F.map g) (F.map h) (F.map k) (by rw [<-F.map_comp,<-F.map_comp,eq]) := by
    simp only [Functor.mapCone, Limits.Cones.functoriality, Functor.const_obj_obj, Functor.comp_obj,
      Functor.const_obj_map, Functor.comp_map, id_eq, eq_mpr_eq_cast, CommutativeSquare,
      Limits.cospan_one]
    symm
    rw [ConeCast (cospanMapEq F f g)]
    congr
    rw [NatTransCast (cospanMapEq F f g)]
    congr
    funext x
    rw [Eq.rec_lam (fun x X => F.obj M ⟶ x.obj X) _ (cospanMapEq F f g)]
    match x with
    | some Limits.WalkingPair.left => apply Eq.rec_congrArg (cospanMapEq F f g) (λ ξ => F.obj M ⟶ ξ.obj (.left))
    | some Limits.WalkingPair.right => apply Eq.rec_congrArg (cospanMapEq F f g) (λ ξ => F.obj M ⟶ ξ.obj (.right))
    | none => simp only [F.map_comp];apply Eq.rec_congrArg (cospanMapEq F f g) (λ ξ => F.obj M ⟶ ξ.obj (.none))

def IsLimitLift {T : Type u₁} [Category.{v₁} T] {U : Type u₂} [Category.{v₂} U] (F : T ⥤ U)
  [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
  {L J K M : T} (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (eq : k ≫ f = h ≫ g) (p : Limits.IsLimit (CommutativeSquare f g h k eq))
  : Limits.IsLimit (CommutativeSquare (F.map f) (F.map g) (F.map h) (F.map k) (by rw [<-F.map_comp,<-F.map_comp,eq])) := by
      apply cast (α := Limits.IsLimit (F.mapCone (CommutativeSquare f g h k eq)))
      · rw [CommutativeSquareMap]
        rw [cast_poly3 (λ {α} a => Limits.IsLimit (F := α) a) (cospanMapEq F f g)]
        congr
        apply Eq.rec_congrArg
      · apply pbF.preservesLimit.preserves p



-- TODO Hyperdoctrine is not most generic as Beck-Chevalley is asked on every pullback instead of
-- only on a specific class of them
/-
u₁ : Universe of Obj(C)
v₁ : Universe of Hom(C)
u₂ : Universe of u.obj(Obj(C))
v₂ : Universe of u.map(Hom(C))
u₃ : Universe of Obj(T)
v₃ : Universe of Hom(T)
-/
class Hyperdoctrine.{u₁,v₁,u₂,v₂,u₃,v₃} (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{u₂,v₂})
  (T : Type u₃) [Category.{v₃} T] [Limits.HasFiniteLimits T] where

  P : Tᵒᵖ ⥤ C

  -- Adjunctions
  leftAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  leftAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (leftAdj f) (u.map (P.map ⟨f⟩))
  rightAdj {A B : T} (f : A ⟶ B) : u.obj (P.obj ⟨A⟩) ⟶ u.obj (P.obj ⟨B⟩)
  rightAdjunction {A B : T} (f : A ⟶ B) : CategoryTheory.Adjunction (u.map (P.map ⟨f⟩)) (rightAdj f)

  -- Beck-Chevalley property : The right/left mate of an identity from a pullback is inversible
  -- id is casted id as k ≫ f = h ≫ g
  leftBeckChevalley (L J K M : T) (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
     (eq : k ≫ f = h ≫ g) (pb : IsLimit (CommutativeSquare f g h k eq)):
     IsIso ((mateEquiv (leftAdjunction f) (leftAdjunction h)).invFun
     (Comm2Cell (P ⋙ u) (.op k) (.op h) (.op g) (.op f) (by simp only [<-op_comp,eq])))
  rightBeckChevalley (L J K M : T) (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
     (eq : k ≫ f = h ≫ g) (pb : Limits.IsLimit (CommutativeSquare f g h k eq)):
     IsIso ((mateEquiv (rightAdjunction g) (rightAdjunction k)).toFun
     (Comm2Cell (P ⋙ u) (.op k) (.op h) (.op g) (.op f) (by simp only [<-op_comp,eq])))


/-
(0) T has finite products and terminal object 1,
=> T is Cartesian

(5') for each t : X --+ Y in T, t* has adjoints
=> We have the adjunction ∀f ⊢ P(f) ⊢ ∃f in C for every morphism f of T
(5'') then the morphism Z,t*rp 3 t ‘ * & p is an isomorphism
=> Beck-Chevalley

(1) P is an indexed category over T (“a T-category”) <=> P : Tᵒᵖ ⟶ Cat
=> P : Tᵒᵖ ⟶ C, and Objects of C are Categories & 1-morphisms of C are functors <=> C is sub-bicategory of Cat
(2) for each object X of T, the fibre P ( X ) is Cartesian closed, and furthermore,
=> Objects of C are Cartesian Closed
(3) has finite coproducts and an initial object O x ,
=> Objects of C are complete categories
(4)for each morphism t of T, the “inverse image’.’ functor t* preserves the structure of (2),(3)
=> 1-morphisms of C preserve the structures
|---> C is a sub-bicategory of complete categories

-/
instance (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{u₂,v₂}) (T : Type u₃) [Category.{v₃} T] [Limits.HasFiniteLimits T] :
   Category (Hyperdoctrine C u T) where
     Hom P Q := P.P ⟶ Q.P
     id P := 𝟙 P.P
     comp η ν := NatTrans.vcomp η ν

def HyperdoctrineFunctor.{u₁,v₁,u₂,v₂,u₃,v₃,u₄,v₄} (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{u₂,v₂})
 (T : Type u₃) [Category.{v₃} T] [Limits.HasFiniteLimits T] [HT : Hyperdoctrine C u T] (U : Type u₄) [Category.{v₄} U] [Limits.HasFiniteLimits U]
 (F : U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]: Hyperdoctrine C u U where
   P := F.op ⋙ HT.P
   leftAdj f := HT.leftAdj (F.map f)
   leftAdjunction f := HT.leftAdjunction (F.map f)
   rightAdj f := HT.rightAdj (F.map f)
   rightAdjunction f := HT.rightAdjunction (F.map f)
   leftBeckChevalley Γ Ξ Δ Φ f g h k e p :=
      HT.leftBeckChevalley (F.obj Γ) (F.obj Ξ) (F.obj Δ) (F.obj Φ) (F.map f) (F.map g) (F.map h) (F.map k)
        (by rw [<-F.map_comp,<-F.map_comp,e]) (IsLimitLift F f g h k e p)
   rightBeckChevalley Γ Ξ Δ Φ f g h k e p :=
      HT.rightBeckChevalley (F.obj Γ) (F.obj Ξ) (F.obj Δ) (F.obj Φ) (F.map f) (F.map g) (F.map h) (F.map k)
        (by rw [<-F.map_comp,<-F.map_comp,e]) (IsLimitLift F f g h k e p)


instance : HasForget₂ HeytAlg Preord :=
   let _ := HasForget₂.trans HeytAlg BddDistLat DistLat
   let _ := HasForget₂.trans HeytAlg DistLat Lat
   let _ := HasForget₂.trans HeytAlg Lat PartOrd
   HasForget₂.trans HeytAlg PartOrd Preord

def HeytAsCat : HeytAlg ⥤ Cat := (forget₂ HeytAlg Preord ⋙ preordToCat)

abbrev FirstOrderHyperdoctrine (T : Type u) [Category.{v} T] [Limits.HasFiniteLimits T]:=
   Hyperdoctrine HeytAlg HeytAsCat T
