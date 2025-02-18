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

def Hyperdoctrine.Hom
  {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
  {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
  (P Q : Hyperdoctrine C u T) := NatTrans (Functor.comp P.P u) (Functor.comp Q.P u)

instance Hyperdoctrine.category.{u₁,v₁,u₂,v₂,u₃,v₃}
  (C : Type u₁) [Category.{v₁} C] (u : C ⥤ Cat.{u₂,v₂})
  (T : Type u₃) [Category.{v₃} T] [Limits.HasFiniteLimits T] :
   Category (Hyperdoctrine C u T) where
     Hom P Q := Hyperdoctrine.Hom P Q
     id P := 𝟙 (P.P ⋙ u)
     comp η ν := NatTrans.vcomp η ν

def Hyperdoctrine.precompose
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T] (P : Hyperdoctrine C u T)
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 (F : U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : Hyperdoctrine C u U where
   P := F.op ⋙ P.P
   leftAdj f := P.leftAdj (F.map f)
   leftAdjunction f := P.leftAdjunction (F.map f)
   rightAdj f := P.rightAdj (F.map f)
   rightAdjunction f := P.rightAdjunction (F.map f)
   leftBeckChevalley Γ Ξ Δ Φ f g h k e p :=
      P.leftBeckChevalley (F.obj Γ) (F.obj Ξ) (F.obj Δ) (F.obj Φ) (F.map f) (F.map g) (F.map h) (F.map k)
        (by rw [<-F.map_comp,<-F.map_comp,e]) (IsLimitLift F f g h k e p)
   rightBeckChevalley Γ Ξ Δ Φ f g h k e p :=
      P.rightBeckChevalley (F.obj Γ) (F.obj Ξ) (F.obj Δ) (F.obj Φ) (F.map f) (F.map g) (F.map h) (F.map k)
        (by rw [<-F.map_comp,<-F.map_comp,e]) (IsLimitLift F f g h k e p)

def Hyperdoctrine.precompose_map
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T] {P P' : Hyperdoctrine C u T}
 (η : Hyperdoctrine.Hom P P')
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 (F : U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : Hyperdoctrine.Hom (Hyperdoctrine.precompose P F) (Hyperdoctrine.precompose P' F) where
   app X := η.app (.op (F.obj X.unop))
   naturality {X Y} s := by simp only [Functor.comp_obj, Functor.comp_map]; apply η.naturality

def Hyperdoctrine.HypFun
  {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
  {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
  {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
  (F : U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
   : Hyperdoctrine C u T ⥤ Hyperdoctrine C u U where
     obj P := Hyperdoctrine.precompose P F
     map {P P'} η := Hyperdoctrine.precompose_map η F (pbF := _)

def Hyperdoctrine.HypFun_id
  {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
  {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
   : Hyperdoctrine.HypFun (Functor.id T) = Functor.id (Hyperdoctrine C u T) := rfl
def Hyperdoctrine.HypFun_comp
  {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
  {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
  {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
  {V : Type u₅} [Category.{v₅} V] [Limits.HasFiniteLimits V]
  {F : T ⥤ U} [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
  {G : U ⥤ V} [pbG:PreservesChosenLimitsOfShape Limits.WalkingCospan G]
   : Hyperdoctrine.HypFun (Functor.comp F G) =
    Functor.comp (Hyperdoctrine.HypFun G) (@Hyperdoctrine.HypFun C _ u _ _ _ _ _ _ F _) := rfl

def Hyperdoctrine.precompose_mapOLD
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T] {P Q : Hyperdoctrine C u T}
 (η : Hyperdoctrine.Hom P Q)
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 (F : U ⥤ T) [pbF:PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 : Hyperdoctrine.Hom (Hyperdoctrine.precompose P F) (Hyperdoctrine.precompose Q F) where
   app X := η.app (.op (F.obj X.unop))
   naturality {X Y} s := by simp only [Functor.comp_obj, Functor.comp_map]; apply η.naturality

def Hyperdoctrine.precompose_map₂
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {F G : U ⥤ T} [PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 (η : NatTrans F G)
 (P : Hyperdoctrine C u T)
 : Hyperdoctrine.Hom (Hyperdoctrine.precompose P G) (Hyperdoctrine.precompose P F) :=
  -- We want a NatTrans ((F.op ⋙ P.P) ⋙ u) ((G.op ⋙ P.P) ⋙ u)
  whiskerRight (whiskerRight (NatTrans.op η) P.P) u

def Hyperdoctrine.HypNat
 {C : Type u₁} [Category.{v₁} C] {u : C ⥤ Cat.{u₂,v₂}}
 {T : Type u₃} [Category.{v₃} T] [Limits.HasFiniteLimits T]
 {U : Type u₄} [Category.{v₄} U] [Limits.HasFiniteLimits U]
 {F G : U ⥤ T} [PreservesChosenLimitsOfShape Limits.WalkingCospan F]
 [PreservesChosenLimitsOfShape Limits.WalkingCospan G]
 (η : NatTrans F G)
 : NatTrans (Hyperdoctrine.HypFun G) (@Hyperdoctrine.HypFun C _ u T _ _ U _ _ F _) where
    app P := Hyperdoctrine.precompose_map₂ η P
    naturality {P P'} ρ := by
      apply NatTrans.ext
      funext X
      simp only
      calc
        ((HypFun G).map ρ ≫ precompose_map₂ η P').app X = ((HypFun G).map ρ).app X ≫ (precompose_map₂ η P').app X := NatTrans.vcomp_app ((HypFun G).map ρ) (precompose_map₂ η P') X
        _ = (precompose_map₂ η P).app X ≫ ((HypFun F).map ρ).app X := Eq.symm (ρ.naturality (η.app X.unop).op)
        _ = (precompose_map₂ η P ≫ (HypFun F).map ρ).app X := by rw [<-NatTrans.vcomp_app];rfl





instance : HasForget₂ HeytAlg Preord :=
   let _ := HasForget₂.trans HeytAlg BddDistLat DistLat
   let _ := HasForget₂.trans HeytAlg DistLat Lat
   let _ := HasForget₂.trans HeytAlg Lat PartOrd
   HasForget₂.trans HeytAlg PartOrd Preord

def HeytAsCat : HeytAlg ⥤ Cat := (forget₂ HeytAlg Preord ⋙ preordToCat)

abbrev FirstOrderHyperdoctrine (T : Type u) [Category.{v} T] [Limits.HasFiniteLimits T]:=
   Hyperdoctrine HeytAlg HeytAsCat T

section HypType.Hyperdoctrine

def HypType.P : Type uᵒᵖ ⥤ HeytAlg where
  obj X := ⟨X.unop → Prop,inferInstance⟩
  map f := {
    toFun P := λ x => P (f.unop x)
    map_sup' := by aesop_cat
    map_inf' := by aesop_cat
    map_bot' := by aesop_cat
    map_himp' := by aesop_cat
  }
def HypType.existsP {A B : Type u} (σ : A ⟶ B): HeytAsCat.obj (P.obj ⟨A⟩) ⟶ HeytAsCat.obj (P.obj ⟨B⟩) where
  obj P := λ x => ∃ y, (σ y = x) ∧ P y
  map {P Q} i := by
    constructor
    constructor
    intro x
    intro ⟨y,⟨hye,hyP⟩⟩
    exists y
    constructor
    · exact hye
    · exact i.down.down y hyP

  --⟨⟨λ x => λ ⟨y,⟨hye,hyP⟩⟩ => ⟨y,⟨hye,i.down.down y hyP⟩⟩⟩⟩
  -- XXX Declaration has free variables, i don't understand why

def HypType.forallP {A B : Type u} (σ : A ⟶ B): HeytAsCat.obj (P.obj ⟨A⟩) ⟶ HeytAsCat.obj (P.obj ⟨B⟩) where
  obj P := λ x => ∀ y, (σ y = x) → P y
  map {P Q} i := by
    constructor
    constructor
    intro x
    intro hy
    intro y
    intro e
    exact i.down.down y (hy y e)
def HypType.OneCone {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
  (x : X) (y : Y) (z : Z) (ex : f x = z) (ey : g y = z)
  : CategoryTheory.Limits.Cone (CategoryTheory.Limits.cospan f g) where
    pt := PUnit
    π := {
      app := fun
        | .left => λ _ => x
        | .one => λ _ => z
        | .right => λ _ => y
      naturality := λ {A B} => fun
        | .term .left => by
          funext u
          exact Eq.symm ex
        | .term .right => by
          funext u
          exact Eq.symm ey
        | .id Z => by
          simp only [Functor.const_obj_obj, WidePullbackShape.hom_id, Functor.const_obj_map,
            Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
      }
def HypType.PullbackElementwise {L J K M : Type u} (f : K ⟶ L) (g : J ⟶ L) (h : M ⟶ J) (k : M ⟶ K)
  (x : K) (y : J) (z : L) (ex : f x = z) (ey : g y = z)
  (eq : k ≫ f = h ≫ g) (pb : Limits.IsLimit (CommutativeSquare f g h k eq)) :
  {δ : M // k δ = x ∧ h δ = y} :=
    let kone := HypType.OneCone f g x y z ex ey;
    .mk ((pb.lift kone) PUnit.unit) (by {
      constructor
      · exact congrFun (pb.fac kone .left) PUnit.unit
      · exact congrFun (pb.fac kone .right) PUnit.unit
    })
instance HypType.hyperdoctrine : FirstOrderHyperdoctrine (Type u) where
  P := HypType.P
  leftAdj σ := HypType.existsP σ
  leftAdjunction σ := {
    unit := {
      app P := ⟨⟨λ x Px => ⟨x,⟨rfl,Px⟩⟩⟩⟩
    }
    counit := {
      app P := ⟨⟨λ x Px => let ⟨y,⟨ey,Py⟩⟩ := Px; by rw [<-ey];exact Py⟩⟩
    }
  }
  rightAdj σ := HypType.forallP σ
  rightAdjunction σ := {
    unit := {
      app P := ⟨⟨λ x Px y ey => by rw [<-ey] at Px;exact Px⟩⟩
    }
    counit := {
      app P := ⟨⟨λ x Px => Px _ rfl⟩⟩
    }
  }
  leftBeckChevalley L J K M f g h k eq pb := {
    out := by
      constructor
      · constructor
        · rfl
        · rfl
      · constructor
        · intro X Y f
          constructor
        · intro P
          constructor
          constructor
          intro x p
          obtain ⟨δ,⟨pδ,q⟩⟩ := p
          let ⟨β,⟨βδ,βγ⟩⟩ := HypType.PullbackElementwise f g h k δ x (g x) pδ rfl eq pb
          exists β
          constructor
          · exact βγ
          · rw [<-βδ] at q
            exact q
  }
  rightBeckChevalley L J K M f g h k eq pb := {
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
          intro γ ep δ pδ
          let ⟨β,⟨βδ,βγ⟩⟩ := HypType.PullbackElementwise f g h k γ δ (g δ) (Eq.symm pδ) rfl eq pb
          rw [<-βγ]
          exact ep β βδ
  }

end HypType.Hyperdoctrine
