import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
universe v₁ v₂ u₁ u₂

open Opposite

open CategoryTheory

section Opposite12
universe v u

variable (α : Sort u)

@[aesop safe cases]
structure Opposite12 where
  /-- The canonical map `α → αᵒᵖ`. -/
  op12 ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop12 : α

attribute [pp_nodot] Opposite12.unop12

/-- Make sure that `Opposite.op12 a` is pretty-printed as `op12 a` instead of `{ unop12 := a }` or
`⟨a⟩`. -/
@[app_unexpander Opposite12.op12]
protected def Opposite12.unexpander_op12 : Lean.PrettyPrinter.Unexpander
  | s => pure s

notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `Presheaf Cᵒᵖ¹²` parses as `Presheaf (Cᵒᵖ¹²)` and not `(Presheaf C)ᵒᵖ¹²`.
α "ᵒᵖ¹²" => Opposite12 α

section Quiver
variable {V : Type u} [Quiver.{v} V]
instance opposite12Q : Quiver (Opposite12 V) :=
  ⟨fun a b => Opposite (b.unop12 ⟶ a.unop12)⟩

/-- The opposite of an arrow in `V`. -/
def Quiver.Hom.op12 {X Y : V} (f : X ⟶ Y) : Opposite12.op12 Y ⟶ Opposite12.op12 X := ⟨f⟩
/-- Given an arrow in `Vᵒᵖ¹²`, we can take the "unopposite" back in `V`. -/
def Quiver.Hom.unop12 {X Y : Vᵒᵖ¹²} (f : X ⟶ Y)
   : Opposite12.unop12 Y ⟶ Opposite12.unop12 X := Opposite.unop f

@[simp]
theorem Quiver.Hom.unop_op12 {X Y : V} (f : X ⟶ Y) : f.op12.unop12 = f :=
  rfl
@[simp]
theorem Quiver.Hom.op_unop12 {X Y : Vᵒᵖ¹²} (f : X ⟶ Y) : f.unop12.op12 = f :=
  rfl
@[simp] theorem Quiver.Hom.unop12_mk {X Y : Vᵒᵖ¹²} (f : X ⟶ Y) : Quiver.Hom.unop12 {unop := f} = f := rfl

end Quiver


instance opposite12CS {V} [BC : CategoryStruct V]: CategoryStruct (Opposite12 V) where
  id B := Opposite.op (BC.id B.unop12)
  comp f g := Opposite.op (BC.comp (Opposite.unop g) (Opposite.unop f))
instance opposite12C {V} [BC : Category V]: Category (Opposite12 V) where
  toCategoryStruct := @opposite12CS V BC.toCategoryStruct
  id_comp f := by simp only [opposite12CS, Category.comp_id];congr
  comp_id f := by simp only [opposite12CS, Category.id_comp];congr
  assoc f g h := by simp only [opposite12CS, Category.assoc]

@[simps]
def isoOpposite12 {V} [Category V] {A B : V} (eq: A ≅ B)
 : Opposite12.op12 A ≅ Opposite12.op12 B where
  hom := Opposite.op eq.inv
  inv := Opposite.op eq.hom
  hom_inv_id := by simp only [CategoryStruct.comp, Iso.hom_inv_id, CategoryStruct.id]
  inv_hom_id := by simp only [CategoryStruct.comp, Iso.inv_hom_id, CategoryStruct.id]

@[simp]
theorem op_unop12 (x : Opposite12 α) : Opposite12.op12 (Opposite12.unop12 x) = x :=
  rfl
@[simp]
theorem unop_op12 (x : α) : Opposite12.unop12 (Opposite12.op12 x) = x :=
  rfl

end Opposite12
open Bicategory
instance Bicategory.opposite12 (C : Type u₁) [BC : Bicategory.{w₁,v₁} C]: Bicategory.{w₁,v₁} (Opposite12 C) where
  toCategoryStruct := opposite12CS
  homCategory A B := Category.opposite
  whiskerLeft f g h η := Opposite.op (BC.whiskerRight η.unop f.unop12)
  whiskerRight η f := Opposite.op (BC.whiskerLeft f.unop12 η.unop)
  associator {A B C D} f g h := Iso.op (BC.associator h.unop12 g.unop12 f.unop12)
  leftUnitor f := Iso.op (Iso.symm (BC.rightUnitor f.unop12))
  rightUnitor f := Iso.op (Iso.symm (BC.leftUnitor f.unop12))
  whisker_exchange η θ :=  congrArg Opposite.op (BC.whisker_exchange θ.unop η.unop)
  id_whiskerLeft η := congrArg Opposite.op (by
   simp only [CategoryStruct.comp,Category.assoc];simp only [Iso.op_inv,
    Iso.symm_inv, Quiver.Hom.unop_op, op_comp, op_unop, Quiver.Hom.op_unop, unop_comp, Iso.op_hom,
    Iso.symm_hom, Category.assoc];exact BC.whiskerRight_id η.unop)
  whiskerLeft_id f g := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];exact BC.id_whiskerRight g.unop12 f.unop12)
  whiskerLeft_comp f a b c η θ := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];exact BC.comp_whiskerRight θ.unop η.unop f.unop12)
  comp_whiskerLeft f g a b η := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];simp only [Iso.op_inv,
    Quiver.Hom.unop_op, Quiver.Hom.unop_op', op_comp, unop_comp, Iso.op_hom, Category.assoc];exact BC.whiskerRight_comp η.unop g.unop12 f.unop12)
  id_whiskerRight f g := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerLeft_id g.unop12 f.unop12)
  comp_whiskerRight η θ f := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerLeft_comp f.unop12 θ.unop η.unop)
  whiskerRight_id η := congrArg Opposite.op (by
   simp only [CategoryStruct.comp,Category.assoc];simp only [Iso.op_inv,
    Iso.symm_inv, Quiver.Hom.unop_op, op_comp, op_unop, Quiver.Hom.op_unop, unop_comp, Iso.op_hom,
    Iso.symm_hom, Category.assoc];exact BC.id_whiskerLeft η.unop)
  whiskerRight_comp η f g := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc];simp only [Iso.op_hom,
    Quiver.Hom.unop_op, Quiver.Hom.unop_op', op_comp, unop_comp, Iso.op_inv, Category.assoc];exact BC.comp_whiskerLeft g.unop12 f.unop12 η.unop)
  whisker_assoc f _ _ η g := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc,isoOpposite12];simp only [Quiver.Hom.unop12,
    Quiver.Hom.unop_op', Iso.op_inv, Quiver.Hom.unop_op, whisker_assoc, Iso.inv_hom_id_assoc,
    op_comp, unop_comp, Iso.op_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  pentagon f g h i := congrArg Opposite.op (by simp only [CategoryStruct.comp,Category.assoc,isoOpposite12,Iso.symm_inv, Iso.symm_hom, pentagon,Quiver.Hom.unop12];simp only [Iso.op_hom,
    Quiver.Hom.unop_op, Quiver.Hom.unop_op', op_comp, unop_comp, Category.assoc, pentagon])
  triangle {a b c} f g := congrArg Opposite.op (by apply triangle_assoc_comp_right_inv)

set_option maxHeartbeats 300000
def Pseudofunctor.op12
  {C : Type u₁} [Bicategory.{v₁,w₁} C]
  {D : Type u₂} [Bicategory.{v₂,w₂} D]
  (F : Pseudofunctor C D) : Pseudofunctor Cᵒᵖ¹² Dᵒᵖ¹² where
  obj X := Opposite12.op12 (F.obj X.unop12)
  map f := Opposite.op (F.map f.unop12)
  map₂ η := Quiver.Hom.op (F.map₂ η.unop)
  mapId X := Iso.op (Iso.symm (F.mapId X.unop12))
  mapComp f g := Iso.op (Iso.symm (F.mapComp g.unop12 f.unop12))
  map₂_id f := by simp only [Bicategory.opposite12, CategoryStruct.id, unop_op12,
    Quiver.Hom.unop12.eq_1, Quiver.Hom.unop12, PrelaxFunctor.map₂_id];simp only [op_id, op_unop,
      unop_id, PrelaxFunctor.map₂_id]
  map₂_comp α β := by
    simp only [Bicategory.opposite12, CategoryStruct.comp, unop_op12]
    simp only [Quiver.Hom.unop12, op_comp, op_unop, Quiver.Hom.op_unop, unop_comp,
      PrelaxFunctor.map₂_comp, Quiver.Hom.unop_op]
  map₂_whisker_left f _ _ β := by simp only [Bicategory.opposite12, CategoryStruct.comp,
    unop_op12, isoOpposite12, Iso.symm_inv, Iso.symm_hom, op_unop12, Quiver.Hom.unop12,
    Pseudofunctor.map₂_whisker_right, Category.assoc];simp only [Quiver.Hom.unop_op',
      Pseudofunctor.map₂_whisker_right, op_comp, Category.assoc, Iso.op_inv, Iso.symm_inv,
      Quiver.Hom.unop_op, unop_comp, Iso.op_hom, Iso.symm_hom]
  map₂_whisker_right α g := by simp only [Bicategory.opposite12, CategoryStruct.comp, unop_op12,
    isoOpposite12, Iso.symm_inv, Iso.symm_hom, op_unop12, Quiver.Hom.unop12,
    Pseudofunctor.map₂_whisker_left, Category.assoc];simp only [Quiver.Hom.unop_op',
      Pseudofunctor.map₂_whisker_left, op_comp, Category.assoc, Iso.op_inv, Iso.symm_inv,
      Quiver.Hom.unop_op, unop_comp, Iso.op_hom, Iso.symm_hom]
  map₂_associator α g := by simp only [Bicategory.opposite12, CategoryStruct.comp, unop_op12,
    isoOpposite12, Iso.symm_inv, Iso.symm_hom, op_unop12, Quiver.Hom.unop12,
    Pseudofunctor.map₂_associator, Category.assoc, implies_true];simp only [Iso.op_hom,
      Quiver.Hom.unop_op, Pseudofunctor.map₂_associator, op_comp, Category.assoc, Iso.op_inv,
      Iso.symm_inv, Quiver.Hom.unop_op', unop_comp, Iso.symm_hom, implies_true]
  map₂_left_unitor {X Y} f := by
    simp only [Bicategory.opposite12, opposite12CS, CategoryStruct.comp, unop_op12, isoOpposite12,
      Iso.symm_inv, Iso.symm_hom, op_unop12, Quiver.Hom.unop12.eq_1, Quiver.Hom.unop12,
      Category.assoc]
    simp only [Iso.op_hom, Iso.symm_hom, Quiver.Hom.unop_op, Quiver.Hom.unop_op',
        unop_comp, Category.assoc]
    rw [Pseudofunctor.whiskerLeft_mapId_inv]
    congr
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  map₂_right_unitor {X Y} f := by
    unfold Bicategory.opposite12
    simp only
    unfold opposite12CS
    simp only [CategoryStruct.comp, unop_op12, isoOpposite12,
      Iso.symm_inv, Iso.symm_hom, op_unop12, Quiver.Hom.unop12.eq_1, Quiver.Hom.unop12,
      Category.assoc]
    simp only [Iso.op_hom, Iso.symm_hom, Quiver.Hom.unop_op, Quiver.Hom.unop_op',
        unop_comp, Category.assoc]
    congr
    rw [Pseudofunctor.whiskerRight_mapId_inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]

@[simp]
def Pseudofunctor.op12_id
  {C : Type u₁} [Bicategory.{v₁,w₁} C]
   : Pseudofunctor.op12 (Pseudofunctor.id C) = Pseudofunctor.id (Opposite12 C) := by
    unfold Pseudofunctor.op12
    unfold Pseudofunctor.id
    congr
