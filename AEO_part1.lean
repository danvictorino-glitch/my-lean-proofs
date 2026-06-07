import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Preorder
import Mathlib.Order.Preorder.Basic

open CategoryTheory

universe u

/-! ### 1. THE GEOMETRIC BASE (PREORDER) -/
structure GeometricOpenSet where
  id   : Nat
  size : Nat

-- Defining U ≤ V iff U.size ≤ V.size
instance : Preorder GeometricOpenSet where
  le := fun U V => U.size ≤ V.size
  le_refl := by
    intro U
    exact Nat.le_refl U.size
  le_trans := by
    intro U V W huv hvw
    exact Nat.le_trans huv hvw

-- Turning the Preorder into a Category automatically via Mathlib
instance : SmallCategory GeometricOpenSet := Preorder.toCategory

/-! ### 2. THE CORE ENGINE (TERAMORPHISMS WITH FIN BOUNDS) -/
inductive MorphismType where
  | standard
  | infinitesimal
  | joker

inductive SpinDirection where
  | left
  | right

structure Teramorphism (U V : GeometricOpenSet) where
  map          : Fin U.size → Fin V.size
  morph_type   : MorphismType
  current_spin : SpinDirection

@[simp]
def spinLeftToRight {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  match t.current_spin with
  | SpinDirection.left => { t with current_spin := SpinDirection.right }
  | SpinDirection.right => t
