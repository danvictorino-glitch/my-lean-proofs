# Categorical Limits: Products and Coproducts in GeometricOpenSet

## Overview

This documentation describes the extension of `AEO_sheaf_integrated.lean` with formal category-theoretic limits, proving that:
- **`overlap` is the categorical product (meet)** in the GeometricOpenSet preorder category
- **`union` is the categorical coproduct (join)** in the GeometricOpenSet preorder category

These structures are formalized using Mathlib4's `CategoryTheory.Limits` framework.

---

## Section 5: Categorical Limits Framework

### Part A: Binary Products via `overlap`

#### Key Structures

**Projection Morphisms:**
```lean
def overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U
def overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V
```
- Extract the left and right projections from the meet structure
- In a preorder category, `≤` is the sole morphism constructor
- Proven using `Nat.min_le_left` and `Nat.min_le_right`

**Mediating Morphism:**
```lean
def overlapMediate {U V X : GeometricOpenSet} (f : X ≤ U) (g : X ≤ V) : X ≤ overlap U V
```
- Universal arrow: given a cone with apex X and morphisms f: X → U, g: X → V
- Returns the unique morphism from X to the product overlap U V
- Constructed via `Nat.le_min`: X.size ≤ min(U.size, V.size)

**Binary Product Instance:**
```lean
instance (U V : GeometricOpenSet) : Limits.HasBinaryProduct U V
```
- Registers overlap as the formal categorical product in Mathlib4
- Implements `Limits.IsLimit` with cone apex = overlap and projections π₁, π₂
- Satisfies the universal property: for any cone with apex X, the lift map is overlapMediate

#### Universal Properties

**Commutativity Diagram 1** (Product Projection):
```
    X
    |
    | f (or g)
    |
    v
overlap U V ----π₁----> U
    |
    | π₂
    v
    V
```

**Theorem:** `prod_overlap_universal`
```lean
theorem prod_overlap_universal {U V X : GeometricOpenSet} (f : X ≤ U) (g : X ≤ V) :
    (overlapMediate f g) ≫ (overlapLe_left U V) = f ∧
    (overlapMediate f g) ≫ (overlapLe_right U V) = g
```
- **Semantics:** Composing the mediating morphism with left projection recovers f; same for right
- **Proof:** Reflexivity in preorder composition (transitivity of ≤ is associative)

**Uniqueness Theorem:** `prod_overlap_unique`
```lean
theorem prod_overlap_unique {U V X : GeometricOpenSet} (f : X ≤ U) (g : X ≤ V) (h : X ≤ overlap U V)
    (hf : h ≫ (overlapLe_left U V) = f)
    (hg : h ≫ (overlapLe_right U V) = g) :
    h = overlapMediate f g
```
- **Semantics:** The mediating morphism is the unique arrow making the diagram commute
- **Proof:** In preorder categories, propositional equality of ≤ relations is automatic

---

### Part B: Binary Coproducts via `union`

#### Key Structures

**Injection Morphisms:**
```lean
def unionLe_left (U V : GeometricOpenSet) : U ≤ union U V
def unionLe_right (U V : GeometricOpenSet) : V ≤ union U V
```
- Extract the left and right injections from the join structure
- Proven using `Nat.le_max_left` and `Nat.le_max_right`

**Descending Morphism:**
```lean
def unionMediate {U V X : GeometricOpenSet} (f : U ≤ X) (g : V ≤ X) : union U V ≤ X
```
- Dual to overlapMediate
- Given a cocone with apex X and morphisms f: U → X, g: V → X
- Returns the unique morphism from the coproduct union U V to X
- Constructed via `Nat.max_le`: max(U.size, V.size) ≤ X.size

**Binary Coproduct Instance:**
```lean
instance (U V : GeometricOpenSet) : Limits.HasBinaryCoproduct U V
```
- Registers union as the formal categorical coproduct in Mathlib4
- Implements `Limits.IsColimit` with cocone apex = union and injections ι₁, ι₂
- Satisfies the universal property: for any cocone with apex X, the descent map is unionMediate

#### Universal Properties

**Commutativity Diagram 2** (Coproduct Injection):
```
    U ----ι₁----> union U V
           |
           |
           | g (or desc)
           |
           v
           X
    V ----ι₂----> union U V
```

**Theorem:** `coprod_union_universal`
```lean
theorem coprod_union_universal {U V X : GeometricOpenSet} (f : U ≤ X) (g : V ≤ X) :
    (unionLe_left U V) ≫ (unionMediate f g) = f ∧
    (unionLe_right U V) ≫ (unionMediate f g) = g
```
- **Semantics:** Composing left injection with descending morphism recovers f; same for right
- **Proof:** Reflexivity in preorder composition

**Uniqueness Theorem:** `coprod_union_unique`
```lean
theorem coprod_union_unique {U V X : GeometricOpenSet} (f : U ≤ X) (g : V ≤ X) (h : union U V ≤ X)
    (hf : (unionLe_left U V) ≫ h = f)
    (hg : (unionLe_right U V) ≫ h = g) :
    h = unionMediate f g
```
- **Semantics:** The descending morphism is the unique arrow making the diagram commute
- **Proof:** Propositional equality in preorder categories

---

## Implementation Details

### Preorder Category Structure

GeometricOpenSet is a preorder category where:
- **Objects:** Geometric open sets U with a natural size parameter
- **Morphisms:** U ⟶ V iff U.size ≤ V.size (reflexive and transitive)
- **Composition:** Transitivity of ≤ (Nat.le_trans)
- **Identity:** Reflexivity of ≤ (Nat.le_refl)

### Products in Preorder Categories

In a preorder (partially ordered set):
- **Product of U and V = meet(U, V) = min(U.size, V.size)** = overlap U V
- **Coproduct of U and V = join(U, V) = max(U.size, V.size)** = union U V

This is a fundamental fact in category theory: in a preorder viewed as a category, limits coincide with meets and colimits coincide with joins.

### Mathlib4 Integration

**Imports added:**
```lean
import Mathlib.CategoryTheory.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryCoproducts
```

**Instance declarations:**
- `Limits.HasBinaryProduct U V` for every pair of opens
- `Limits.HasBinaryCoproduct U V` for every pair of opens

These instances allow use of Mathlib4's generic limit API, including:
- Accessing products via `Limits.prod U V` (notation: `U ⨯ V`)
- Accessing coproducts via `Limits.coprod U V` (notation: `U ⨿ V`)
- Constructing limit cones and cocones generically

---

## Mathematical Significance

### For Sheaf Theory

Products and coproducts are essential for:
1. **Sheaf gluing:** Sections on disjoint opens can be glued via coproducts
2. **Restriction:** Sections on a product of opens restrict to each factor
3. **Presheaf functoriality:** The AlphaPresheaf respects products contravariance

### For the Teramorphism Architecture

The formalization enables:
- Composition of Teramorphism fibers over products and coproducts of base opens
- Coherence checks: ensuring spin/classification properties survive across limit structures
- Global-to-local consistency: anomaly repair must respect the limit/colimit structure

### Connection to Prior Theorems

The overlap and union operations were already defined in sections 6 of the original file:
```lean
def overlap (U V : GeometricOpenSet) : GeometricOpenSet := { size := min U.size V.size }
def union (U V : GeometricOpenSet) : GeometricOpenSet := { size := max U.size V.size }
```

**Section 5 now proves** that these naive definitions are *categorical products and coproducts* in the formal Mathlib4 sense, with all required universal properties.

---

## Usage Examples

### Accessing Products in Code

```lean
-- The product overlap is accessible as a formal limit
example (U V : GeometricOpenSet) : Limits.HasBinaryProduct U V := inferInstance

-- Morphisms are obtained via projections
example (U V : GeometricOpenSet) : overlap U V ⟶ U := overlapLe_left U V
example (U V : GeometricOpenSet) : overlap U V ⟶ V := overlapLe_right U V

-- Mediating morphisms are constructed automatically
example {U V X : GeometricOpenSet} (f : X ⟶ U) (g : X ⟶ V) : X ⟶ overlap U V :=
  overlapMediate f g
```

### Working with Presheaf Restrictions

The AlphaPresheaf can now exploit products:
```lean
-- A section over the product is the same as a pair of sections with compatible restrictions
def sectionOnProduct (U V : GeometricOpenSet) : Type u :=
  AlphaPresheaf.obj (Opposite.op (overlap U V))

-- By functoriality, a section on the product restricts to sections on each factor
def projectLeft (U V : GeometricOpenSet) (s : sectionOnProduct U V) : 
    AlphaPresheaf.obj (Opposite.op U) :=
  AlphaPresheaf.map (overlapLe_left U V) s
```

---

## Completeness and Future Work

### Completed
✓ Binary products (overlap) with universal property  
✓ Binary coproducts (union) with universal property  
✓ Mathlib4 `HasBinaryProduct` and `HasBinaryCoproduct` instances  
✓ Uniqueness and commutativity proofs  

### Future Extensions
- **Finite products:** Generalize to products of n opens via iterated binary products
- **Finite coproducts:** Extend to n-way coproducts for sheaf gluing along multiple opens
- **Equalizers/Coequalizers:** Formalize fiber products and pushouts for more complex gluing
- **Adjoint functors:** Prove that restriction (pullback) along product projection is left adjoint to the product inclusion
- **Limit-preserving properties:** Show that AlphaPresheaf preserves products (contravariance)

---

## References

1. **Mathlib4 CategoryTheory.Limits:**
   - https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/CategoryTheory/Limits
   
2. **Preorder Categories:**
   - Riehl, E. (2017). *Category Theory in Context*, Chapter 1.5
   
3. **Sheaf Theory:**
   - Bredon, G.E. (1997). *Sheaf Theory*, 2nd Edition, Springer

---

**Author's Note:** This formalization bridges abstract category theory with concrete topological structure, making the Teramorphism sheaf system fully compatible with Mathlib4's limits infrastructure.
