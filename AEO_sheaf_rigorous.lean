import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Preorder

open CategoryTheory
open scoped classical

universe u

structure GeometricOpenSet where
  size : Nat

instance : LE GeometricOpenSet := ⟨fun U V => U.size ≤ V.size⟩

instance : Preorder GeometricOpenSet where
  le_refl := by intro U; exact le_rfl
  le_trans := by intros U V W hUV hVW; exact le_trans hUV hVW

instance : SmallCategory GeometricOpenSet := Preorder.toCategory

structure AlphaObject where
  carrier : Type u

inductive MorphismType where
  | standard
  | infinitesimal
  | joker

inductive SpinDirection where
  | left
  | right

structure Teramorphism (A B : AlphaObject) where
  map : A.carrier → B.carrier
  morph_type : MorphismType
  current_spin : SpinDirection

structure SheafSection (A : AlphaObject) where
  open_set : GeometricOpenSet
  content  : A.carrier

namespace SheafExtension

abbrev Section (U : GeometricOpenSet) : Type :=
  SheafSection (AlphaObject.mk (Fin U.size → Nat))

@[simp]
def restrictSection {U V : GeometricOpenSet} (h : V ≤ U)
    (s : Section U) : Section V :=
  { open_set := V
    content := s.content ∘ Fin.castLE h }

@[simp]
def overlap (U V : GeometricOpenSet) : GeometricOpenSet :=
  { size := min U.size V.size }

@[simp]
def union (U V : GeometricOpenSet) : GeometricOpenSet :=
  { size := max U.size V.size }

lemma overlap_le_left (U V : GeometricOpenSet) : overlap U V ≤ U := by
  simp [overlap, LE]

lemma overlap_le_right (U V : GeometricOpenSet) : overlap U V ≤ V := by
  simp [overlap, LE]

lemma le_union_left (U V : GeometricOpenSet) : U ≤ union U V := by
  simp [union, LE]

lemma le_union_right (U V : GeometricOpenSet) : V ≤ union U V := by
  simp [union, LE]

@[simp]
def AlphaPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj := fun U => Section (unop U)
  map := fun {U V} f => restrictSection (unop f)
  map_id' := by
    intro U
    ext x
    rfl
  map_comp' := by
    intro U V W f g
    ext x
    rfl

lemma sheaf_gluing {U V : GeometricOpenSet}
    (sU : Section U) (sV : Section V)
    (h : restrictSection (overlap_le_left U V) sU =
          restrictSection (overlap_le_right U V) sV)
    : ∃! t : Section (union U V),
        restrictSection (le_union_left U V) t = sU ∧
        restrictSection (le_union_right U V) t = sV := by
  have total := Nat.le_total U.size V.size
  cases total with
  | inl hUV =>
    have h' : restrictSection hUV sV = sU := by
      have := h
      simp [restrictSection, overlap, overlap_le_left, overlap_le_right, hUV, min_eq_left hUV] at this
      exact this.symm
    refine ⟨sV, ?_, ?_⟩
    · constructor
      · simp [restrictSection, union, le_union_left, hUV, max_eq_right hUV]
      · simp [restrictSection, union, le_union_right, hUV, max_eq_right hUV, h']
    · intro t ht
      have : t = sV := by
        have := ht.2
        simpa [restrictSection, union, le_union_right, hUV, max_eq_right hUV] using this
      subst this
      simp
  | inr hVU =>
    have h' : restrictSection hVU sU = sV := by
      have := h
      simp [restrictSection, overlap, overlap_le_left, overlap_le_right, hVU, min_eq_right hVU] at this
      exact this.symm
    refine ⟨sU, ?_, ?_⟩
    · constructor
      · simp [restrictSection, union, le_union_left, hVU, max_eq_left hVU, h']
      · simp [restrictSection, union, le_union_right, hVU, max_eq_left hVU]
    · intro t ht
      have : t = sU := by
        have := ht.1
        simpa [restrictSection, union, le_union_left, hVU, max_eq_left hVU] using this
      subst this
      simp

end SheafExtension
