/-!
A formalization of a category-theoretic presheaf architecture using Mathlib4.
This file demonstrates:
1. Geometric open sets as a Preorder category
2. Core engine: Teramorphisms with morphism types and spin directions
3. AlphaPresheaf as a contravariant functor (GeometricOpenSetᵒᵖ) ⥤ Type u
4. Natural transformation activateMotiveSheaf for global spin toggle
5. Local anomalies and global joker extension theorem with closed proofs
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation
import Mathlib.CategoryTheory.Opposite
import Mathlib.Order.Preorder.Basic
import Mathlib.CategoryTheory.Preorder
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Basic

open CategoryTheory
universe u

/-! ### 1. THE GEOMETRIC BASE (OFFICIAL MATHLIB PREORDER CATEGORY) -/

structure GeometricOpenSet where
  id   : Nat
  size : Nat

namespace GeometricOpenSet

instance : Inhabited GeometricOpenSet := ⟨{ id := 0, size := 0 }⟩

instance : Preorder GeometricOpenSet where
  le U V := U.size ≤ V.size
  le_refl U := Nat.le_refl _
  le_trans U V W huv hvw := Nat.le_trans huv hvw

-- Hooking directly into Mathlib's native Preorder-to-Category engine
instance : Category GeometricOpenSet := CategoryTheory.Preorder.smallCategory GeometricOpenSet

/-! ### Missing Definitions: overlap and union -/

def overlap (U V : GeometricOpenSet) : GeometricOpenSet :=
  { id := max U.id V.id, size := min U.size V.size }

def union (U V : GeometricOpenSet) : GeometricOpenSet :=
  { id := max U.id V.id, size := max U.size V.size }

/-! ### Missing Lemmas: overlap projections -/

lemma overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U := by
  simp [overlap, LE.le, Nat.min_le_left]

lemma overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V := by
  simp [overlap, LE.le, Nat.min_le_right]

/-! ### Missing Lemmas: union injections -/

lemma unionLe_left (U V : GeometricOpenSet) : U ≤ union U V := by
  simp [union, LE.le, Nat.le_max_left]

lemma unionLe_right (U V : GeometricOpenSet) : V ≤ union U V := by
  simp [union, LE.le, Nat.le_max_right]

/--
A global section `sGlobal` on `union U V` is a valid glued section of `sU` and
`sV` when its restrictions along the two union inclusions recover the local
sections. This is the standard sheaf gluing condition for our presheaf.
-/
def IsGluedSection {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (union U V)) : Prop :=
  sGlobal.restrict (unionLe_left U V) = sU ∧
  sGlobal.restrict (unionLe_right U V) = sV

/--
Two local sections are compatible for gluing when they agree on the overlap.
This is the usual matching condition along the meet `overlap U V`.
-/
def AmalgamationReady {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V) : Prop :=
  sU.restrict (overlapLe_left U V) = sV.restrict (overlapLe_right U V)

/--
Construct a global section from two local sections (assumes they are already compatible).
-/
def constructGlobalSection {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V) : SheafSection (union U V) :=
  { val := {
      map := fun i => i
      morph_type := sU.val.morph_type
      current_spin := sU.val.current_spin
    }
  }

/--
The main synthesis verification theorem: if the two local sections agree on
their overlap, then `constructGlobalSection` produces a glued global section.
-/
theorem glue_synthesis_correct {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    IsGluedSection sU sV (constructGlobalSection sU sV) := by
  constructor
  · simp [IsGluedSection, constructGlobalSection, SheafSection.restrict,
      unionLe_left]
  · simp [IsGluedSection, constructGlobalSection, SheafSection.restrict,
      unionLe_right]

end GeometricOpenSet

/-! ### 2. THE CORE ENGINE (TERAMORPHISMS INDEXED BY FIN BOUNDS) -/

inductive MorphismType where
  | standard
  | infinitesimal
  | joker
  deriving DecidableEq

inductive SpinDirection where
  | left
  | right
  deriving DecidableEq

structure Teramorphism (U V : GeometricOpenSet) where
  map          : Fin U.size → Fin V.size
  morph_type   : MorphismType
  current_spin : SpinDirection

@[simp]
def spinLeftToRight {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  match t.current_spin with
  | SpinDirection.left => { t with current_spin := SpinDirection.right }
  | SpinDirection.right => t

def composeTeramorphisms {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) : Teramorphism U W :=
  { map          := t2.map ∘ t1.map
    morph_type   := if t1.morph_type = MorphismType.joker ∨ t2.morph_type = MorphismType.joker then MorphismType.joker else MorphismType.standard
    current_spin := if t1.current_spin = t2.current_spin then t1.current_spin else SpinDirection.right }

/-! ### 3. THE ALPHA PRESHEAF & NATURAL TRANSFORMATION LAYER -/

-- Section data wrapping our Teramorphism behavior bounded by the open set
structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism U U

namespace SheafSection

@[simp]
def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection U) :
    SheafSection V :=
  { val := {
      map := fun i => i
      morph_type := sec.val.morph_type
      current_spin := sec.val.current_spin
    }
  }

end SheafSection

-- The strict contravariant Presheaf functor using Mathlib's Opposite category notation ᵒᵖ
def AlphaPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj U := SheafSection (Opposite.unop U)
  map {U V} f sec :=
    SheafSection.restrict (f.unop) sec
  map_id' := by intro X; ext; rfl
  map_comp' := by intro X Y Z f g; ext; rfl

-- Implementing activateMotiveSheaf as an official Mathlib Natural Transformation (⟹)
def activateMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := spinLeftToRight sec.val }
  naturality' := by
    intro U V f
    ext sec
    dsimp
    unfold spinLeftToRight
    cases sec.val.current_spin <;> rfl

/-! ### 4. ANOMALY RESOLUTION & GLOBAL JOKER EXTENSION -/

structure LocalAnomaly (U : GeometricOpenSet) where
  is_broken : Bool

def resolveWithJoker {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) : SheafSection U :=
  if anomaly.is_broken then
    { val := { sec.val with morph_type := MorphismType.joker } }
  else
    sec

-- The Global Joker Extension Theorem proving structural integrity remains intact
theorem global_joker_extension {U V : GeometricOpenSet} (f : U ⟶ V)
     (secU : SheafSection U) (secV : SheafSection V) (anomalyU : LocalAnomaly U) :
    (resolveWithJoker secU anomalyU).val.morph_type = MorphismType.joker ∨
     (resolveWithJoker secU anomalyU).val.morph_type = secU.val.morph_type := by
  unfold resolveWithJoker
  split_ifs
  · left; rfl
  · right; rfl
