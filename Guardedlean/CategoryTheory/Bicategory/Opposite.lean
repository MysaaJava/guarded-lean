import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic
universe v₁ v₂ u₁ u₂

open Opposite

namespace CategoryTheory

section Opposite1
universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable (α : Sort u)

-- Porting note: in mathlib, `opposite α` was a type synonym for `α`, but if we did
-- the same in Lean4, one could write problematic definitions like:
-- example (X : C) : Cᵒᵖ := X
-- example {X Y : C} (f : X ⟶ Y): op Y ⟶ op X := f
/-- The type of objects of the opposite of `α`; used to define the opposite category.

  Now that Lean 4 supports definitional eta equality for records,
  both `unop (op X) = X` and `op (unop X) = X` are definitional equalities.

-/
structure Opposite1 where
  /-- The canonical map `α → αᵒᵖ`. -/
  op1 ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop1 : α

instance opposite1Q {V} [Quiver V] : Quiver (Opposite1 V) :=
  ⟨fun a b => b.unop1 ⟶ a.unop1⟩
/-- The opposite of an arrow in `V`. -/
def Quiver.Hom.op1 {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : Opposite1.op1 Y ⟶ Opposite1.op1 X := f
/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
def Quiver.Hom.unop1 {V} [Quiver V] {X Y : Opposite1 V} (f : X ⟶ Y) : Y.unop1 ⟶ X.unop1 := f
instance opposite1CS {V} [BC : CategoryStruct V]: CategoryStruct (Opposite1 V) where
  id B := BC.id B.unop1
  comp f g := BC.comp g f
instance opposite1C {V} [BC : Category V]: Category (Opposite1 V) where
  id_comp f := by simp only [opposite1CS, Category.comp_id]
  comp_id f := by simp only [opposite1CS, Category.id_comp]
  assoc f g h := by simp only [opposite1CS, Category.assoc]


end Opposite1

section Opposite12
universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable (α : Sort u)
structure Opposite12 where
  /-- The canonical map `α → αᵒᵖ`. -/
  op12 ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop12 : α

instance opposite12Q {V} [Quiver V] : Quiver (Opposite12 V) :=
  ⟨fun a b => Opposite12 (b.unop12 ⟶ a.unop12)⟩
/-- The opposite of an arrow in `V`. -/
def Quiver.Hom.op12 {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : Opposite12.op12 Y ⟶ Opposite12.op12 X := ⟨f⟩
/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
@[simp]
def Quiver.Hom.unop12 {V} [Quiver V] {X Y : Opposite12 V} (f : X ⟶ Y) : Y.unop12 ⟶ X.unop12 := f.unop12
instance opposite12CS {V} [BC : CategoryStruct V]: CategoryStruct (Opposite12 V) where
  id B := Opposite12.op12 (BC.id B.unop12)
  comp f g := Opposite12.op12 (BC.comp g.unop12 f.unop12)
instance opposite12C {V} [BC : Category V]: Category (Opposite12 V) where
  toCategoryStruct := @opposite12CS V BC.toCategoryStruct
  id_comp f := by simp only [opposite12CS, Category.comp_id];congr
  comp_id f := by simp only [opposite12CS, Category.id_comp];congr
  assoc f g h := by simp only [opposite12CS, Category.assoc]

def isoOpposite12 {V} [Category V] {A B : V} (eq: A ≅ B)
 : Opposite12.op12 A ≅ Opposite12.op12 B where
  hom := Opposite12.op12 eq.inv
  inv := Opposite12.op12 eq.hom
  hom_inv_id := by simp only [CategoryStruct.comp, Iso.hom_inv_id, CategoryStruct.id]
  inv_hom_id := by simp only [CategoryStruct.comp, Iso.inv_hom_id, CategoryStruct.id]
lemma eqOpposite12 {V} {A B : V} (eq: A = B)
 : Opposite12.op12 A = Opposite12.op12 B := congrArg Opposite12.op12 eq

@[simp]
theorem op_unop12 (x : Opposite12 α) : Opposite12.op12 (Opposite12.unop12 x) = x :=
  rfl
@[simp]
theorem unop_op12 (x : α) : Opposite12.unop12 (Opposite12.op12 x) = x :=
  rfl

end Opposite12

/-- The opposite category.

See <https://stacks.math.columbia.edu/tag/001M>.
-/

instance Bicategory.opposite1 (C : Type u₁) [BC : Bicategory.{w₁,v₁} C]: Bicategory.{w₁,v₁} (Opposite1 C) where
  toCategoryStruct := opposite1CS
  homCategory A B := BC.homCategory B.unop1 A.unop1
  whiskerLeft f g h η := BC.whiskerRight η f
  whiskerRight η f := BC.whiskerLeft f η
  associator {A B C D} f g h := Iso.symm (BC.associator h g f)
  leftUnitor := BC.rightUnitor
  rightUnitor := BC.leftUnitor
  whisker_exchange η θ := Eq.symm (BC.whisker_exchange θ η)
  id_whiskerLeft := BC.whiskerRight_id
  whiskerLeft_id f g := BC.id_whiskerRight g f
  whiskerLeft_comp f a b c η θ := BC.comp_whiskerRight η θ f
  comp_whiskerLeft f g a b η := BC.whiskerRight_comp η g f
  id_whiskerRight f g := BC.whiskerLeft_id g f
  comp_whiskerRight η θ f := BC.whiskerLeft_comp f η θ
  whiskerRight_id := BC.id_whiskerLeft
  whiskerRight_comp η f g := BC.comp_whiskerLeft g f η
  --whisker_assoc f _ _ η g := by simp?;BC.whisker_assoc g η f
  pentagon f g h i := BC.pentagon_inv i h g f
  triangle {a b c} f g := triangle_assoc_comp_right g f

instance Bicategory.opposite12 (C : Type u₁) [BC : Bicategory.{w₁,v₁} C]: Bicategory.{w₁,v₁} (Opposite12 C) where
  toCategoryStruct := opposite12CS
  homCategory A B := @opposite12C _ (BC.homCategory B.unop12 A.unop12)
  whiskerLeft f g h η := ⟨BC.whiskerRight η.unop12 f.unop12⟩
  whiskerRight η f := ⟨BC.whiskerLeft f.unop12 η.unop12⟩
  associator {A B C D} f g h := isoOpposite12 (Iso.symm (BC.associator h.unop12 g.unop12 f.unop12))
  leftUnitor f := isoOpposite12 (BC.rightUnitor f.unop12)
  rightUnitor f := isoOpposite12 (BC.leftUnitor f.unop12)
  whisker_exchange η θ := eqOpposite12 (BC.whisker_exchange θ.unop12 η.unop12)
  id_whiskerLeft η := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerRight_id η.unop12)
  whiskerLeft_id f g := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.id_whiskerRight g.unop12 f.unop12)
  whiskerLeft_comp f a b c η θ := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.comp_whiskerRight θ.unop12 η.unop12 f.unop12)
  comp_whiskerLeft f g a b η := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerRight_comp η.unop12 g.unop12 f.unop12)
  id_whiskerRight f g := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerLeft_id g.unop12 f.unop12)
  comp_whiskerRight η θ f := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.whiskerLeft_comp f.unop12 θ.unop12 η.unop12)
  whiskerRight_id η := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.id_whiskerLeft η.unop12)
  whiskerRight_comp η f g := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc];exact BC.comp_whiskerLeft g.unop12 f.unop12 η.unop12)
  whisker_assoc f _ _ η g := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc,isoOpposite12];apply BC.whisker_assoc_symm g.unop12 η.unop12 f.unop12)
  pentagon f g h i := eqOpposite12 (by simp only [CategoryStruct.comp,Category.assoc,isoOpposite12,Iso.symm_inv, Iso.symm_hom, pentagon])
  triangle {a b c} f g := eqOpposite12 (by apply triangle_assoc_comp_right_inv)

end CategoryTheory
