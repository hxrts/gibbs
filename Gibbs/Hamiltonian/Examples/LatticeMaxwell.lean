import Mathlib

/-
The Problem. Provide a concrete lattice Maxwell example with nontrivial curl stencils
and a domain-decomposition interface that can be refined later.

The key insight is to model E and B on edges/faces (Yee lattice) so discrete curls
use only local stencils, which then drives the ghost-layer/domain decomposition design.

Solution Structure.
1. Lattice geometry: points, directions, edges, faces.
2. Discrete curls with explicit stencils.
3. Quadratic energy + Ohmic damping.
4. Domain decomposition helpers and a coherence lemma for perfect ghost data.
-/

namespace Gibbs.Hamiltonian.Examples

open scoped BigOperators

noncomputable section

/-! ## Lattice Geometry -/

/-- A rectangular 3D lattice with sizes in each dimension. -/
structure Lattice3D where
  /-- Grid size in x-direction. -/
  nx : ℕ
  /-- Grid size in y-direction. -/
  ny : ℕ
  /-- Grid size in z-direction. -/
  nz : ℕ

/-- Lattice points as a product of finite indices. -/
abbrev Lattice3D.Point (L : Lattice3D) := Fin L.nx × Fin L.ny × Fin L.nz

instance (L : Lattice3D) : Fintype L.Point := inferInstance

/-- Cardinal directions in 3D. -/
inductive Direction
  | x | y | z
  deriving DecidableEq, Fintype

namespace Direction

/-- Next direction in cyclic order x -> y -> z -> x. -/
def next : Direction → Direction
  | x => y
  | y => z
  | z => x

/-- Previous direction in cyclic order x <- y <- z <- x. -/
def prev : Direction → Direction
  | x => z
  | y => x
  | z => y

end Direction

/-- An edge in the lattice: a point with an oriented direction. -/
abbrev Edge (L : Lattice3D) := L.Point × Direction

/-- A face in the lattice: a point with a normal direction. -/
abbrev Face (L : Lattice3D) := L.Point × Direction

instance (L : Lattice3D) : Fintype (Edge L) := inferInstance
instance (L : Lattice3D) : Fintype (Face L) := inferInstance

/-- Electric field assigns a scalar to each edge. -/
abbrev ElectricField (L : Lattice3D) := Edge L → ℝ

/-- Magnetic field assigns a scalar to each face. -/
abbrev MagneticField (L : Lattice3D) := Face L → ℝ

/-- Maxwell phase space: electric and magnetic fields. -/
abbrev MaxwellPhase (L : Lattice3D) := ElectricField L × MagneticField L

/-! ## Point Shifts (Periodic) -/

private def shiftPos (n : ℕ) [NeZero n] (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

private def shiftNeg (n : ℕ) [NeZero n] (i : Fin n) : Fin n :=
  ⟨(i.val + (n - 1)) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

private def shiftPointPlus (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (p : L.Point) (dir : Direction) : L.Point := by
  -- Periodic shift by +1 along the given direction.
  rcases p with ⟨x, y, z⟩
  cases dir with
  | x => exact ⟨shiftPos L.nx x, y, z⟩
  | y => exact ⟨x, shiftPos L.ny y, z⟩
  | z => exact ⟨x, y, shiftPos L.nz z⟩

private def shiftPointMinus (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (p : L.Point) (dir : Direction) : L.Point := by
  -- Periodic shift by -1 along the given direction.
  rcases p with ⟨x, y, z⟩
  cases dir with
  | x => exact ⟨shiftNeg L.nx x, y, z⟩
  | y => exact ⟨x, shiftNeg L.ny y, z⟩
  | z => exact ⟨x, y, shiftNeg L.nz z⟩

/-! ## Discrete Curl Operators -/

/-- The discrete curl of E (used to update B). -/
def curlE (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (E : ElectricField L) : MagneticField L :=
  fun f =>
    let u := f.2.next
    let v := f.2.prev
    E (f.1, u) +
      E (shiftPointPlus L f.1 u, v) -
      E (shiftPointPlus L f.1 v, u) -
      E (f.1, v)

/-- The discrete curl of B (used to update E). -/
def curlB (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (B : MagneticField L) : ElectricField L :=
  fun e =>
    let u := e.2.next
    let v := e.2.prev
    B (e.1, v) -
      B (shiftPointMinus L e.1 u, v) -
      B (e.1, u) +
      B (shiftPointMinus L e.1 v, u)

/-- Stencil edges needed for `curlE` at a face. -/
def curlE_stencil (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (f : Face L) : Finset (Edge L) := by
  classical
  let u := f.2.next
  let v := f.2.prev
  exact { (f.1, u),
    (shiftPointPlus L f.1 u, v),
    (shiftPointPlus L f.1 v, u),
    (f.1, v) }

/-- Stencil faces needed for `curlB` at an edge. -/
def curlB_stencil (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (e : Edge L) : Finset (Face L) := by
  classical
  let u := e.2.next
  let v := e.2.prev
  exact { (e.1, v),
    (shiftPointMinus L e.1 u, v),
    (e.1, u),
    (shiftPointMinus L e.1 v, u) }

/-- Locality: `curlE` depends only on its stencil edges. -/
theorem curlE_local (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (E₁ E₂ : ElectricField L) (f : Face L)
    (h : ∀ e ∈ curlE_stencil L f, E₁ e = E₂ e) :
    curlE L E₁ f = curlE L E₂ f := by
  classical
  let u := f.2.next
  let v := f.2.prev
  have h1 : E₁ (f.1, u) = E₂ (f.1, u) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlE_stencil]))
  have h2 : E₁ (shiftPointPlus L f.1 u, v) = E₂ (shiftPointPlus L f.1 u, v) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlE_stencil]))
  have h3 : E₁ (shiftPointPlus L f.1 v, u) = E₂ (shiftPointPlus L f.1 v, u) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlE_stencil]))
  have h4 : E₁ (f.1, v) = E₂ (f.1, v) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlE_stencil]))
  simp [curlE, u, v, h1, h2, h3, h4]

/-- Locality: `curlB` depends only on its stencil faces. -/
theorem curlB_local (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (B₁ B₂ : MagneticField L) (e : Edge L)
    (h : ∀ f ∈ curlB_stencil L e, B₁ f = B₂ f) :
    curlB L B₁ e = curlB L B₂ e := by
  classical
  let u := e.2.next
  let v := e.2.prev
  have h1 : B₁ (e.1, v) = B₂ (e.1, v) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlB_stencil]))
  have h2 : B₁ (shiftPointMinus L e.1 u, v) = B₂ (shiftPointMinus L e.1 u, v) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlB_stencil]))
  have h3 : B₁ (e.1, u) = B₂ (e.1, u) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlB_stencil]))
  have h4 : B₁ (shiftPointMinus L e.1 v, u) = B₂ (shiftPointMinus L e.1 v, u) := by
    exact h _ (by
      simpa [u, v] using (by simp [curlB_stencil]))
  simp [curlB, u, v, h1, h2, h3, h4]

/-! ## Material Parameters and Energy -/

/-- Maxwell system parameters on a lattice. -/
structure LatticeMaxwell (L : Lattice3D) where
  /-- Permittivity. -/
  ε : ℝ
  /-- Permeability. -/
  μ : ℝ
  /-- Conductivity at each edge. -/
  σ : Edge L → ℝ
  /-- Conductivity is positive. -/
  σ_pos : ∀ e, 0 < σ e

/-- Sum of squared magnitudes for an electric field. -/
def fieldNormSqE (L : Lattice3D) (E : ElectricField L) : ℝ :=
  ∑ e, (E e) ^ 2

/-- Sum of squared magnitudes for a magnetic field. -/
def fieldNormSqB (L : Lattice3D) (B : MagneticField L) : ℝ :=
  ∑ f, (B f) ^ 2

/-- Electric-field energy density is nonnegative. -/
theorem fieldNormSqE_nonneg (L : Lattice3D) (E : ElectricField L) : 0 ≤ fieldNormSqE L E := by
  -- Each term is nonnegative, so the sum is nonnegative.
  classical
  unfold fieldNormSqE
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Magnetic-field energy density is nonnegative. -/
theorem fieldNormSqB_nonneg (L : Lattice3D) (B : MagneticField L) : 0 ≤ fieldNormSqB L B := by
  -- Each term is nonnegative, so the sum is nonnegative.
  classical
  unfold fieldNormSqB
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Quadratic Maxwell Hamiltonian on the lattice. -/
def maxwellHamiltonian (L : Lattice3D) (sys : LatticeMaxwell L) :
    MaxwellPhase L → ℝ :=
  fun x =>
    (1 / 2) * sys.ε * fieldNormSqE L x.1 +
    (1 / 2) * (1 / sys.μ) * fieldNormSqB L x.2

/-- Ohmic damping term from conductivity σ. -/
def ohmicDamping (L : Lattice3D) (sys : LatticeMaxwell L) : ElectricField L → ElectricField L :=
  fun E e => -(sys.σ e) * E e

/-- The zero electric field. -/
def zeroElectric (L : Lattice3D) : ElectricField L := fun _ => 0

/-- The zero magnetic field. -/
def zeroMagnetic (L : Lattice3D) : MagneticField L := fun _ => 0

/-- The zero Maxwell phase point. -/
def zeroMaxwellPhase (L : Lattice3D) : MaxwellPhase L :=
  (zeroElectric L, zeroMagnetic L)

/-- The Maxwell Hamiltonian is nonnegative under positive parameters. -/
theorem maxwellHamiltonian_nonneg (L : Lattice3D) (sys : LatticeMaxwell L)
    (hε : 0 ≤ sys.ε) (hμ : 0 < sys.μ) (x : MaxwellPhase L) :
    0 ≤ maxwellHamiltonian L sys x := by
  -- Each term is nonnegative since field norms are nonnegative.
  have hE : 0 ≤ fieldNormSqE L x.1 := fieldNormSqE_nonneg L x.1
  have hB : 0 ≤ fieldNormSqB L x.2 := fieldNormSqB_nonneg L x.2
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hμinv : 0 ≤ (1 / sys.μ) := by
    simpa [one_div] using (inv_nonneg.mpr (le_of_lt hμ))
  have htermE : 0 ≤ (1 / 2) * sys.ε * fieldNormSqE L x.1 :=
    mul_nonneg (mul_nonneg hhalf hε) hE
  have htermB : 0 ≤ (1 / 2) * (1 / sys.μ) * fieldNormSqB L x.2 :=
    mul_nonneg (mul_nonneg hhalf hμinv) hB
  simpa [maxwellHamiltonian, add_comm, add_left_comm, add_assoc] using add_nonneg htermE htermB

/-- The Hamiltonian vanishes at the zero field. -/
theorem maxwellHamiltonian_zero (L : Lattice3D) (sys : LatticeMaxwell L) :
    maxwellHamiltonian L sys (zeroMaxwellPhase L) = 0 := by
  -- All field norms vanish at zero.
  simp [maxwellHamiltonian, zeroMaxwellPhase, zeroElectric, zeroMagnetic, fieldNormSqE, fieldNormSqB]

/-- The zero field minimizes the Maxwell Hamiltonian under positive parameters. -/
theorem maxwellHamiltonian_minimizer (L : Lattice3D) (sys : LatticeMaxwell L)
    (hε : 0 ≤ sys.ε) (hμ : 0 < sys.μ) (x : MaxwellPhase L) :
    maxwellHamiltonian L sys (zeroMaxwellPhase L) ≤ maxwellHamiltonian L sys x := by
  -- Use nonnegativity and the zero energy at the origin.
  have hnonneg := maxwellHamiltonian_nonneg L sys hε hμ x
  simpa [maxwellHamiltonian_zero] using hnonneg

/-! ## Global and Local Updates -/

/-- Maxwell update (global) for the lattice fields. -/
def maxwellUpdate (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) : MaxwellPhase L → MaxwellPhase L :=
  fun x => (curlB L x.2 + ohmicDamping L sys x.1, -curlE L x.1)

/-! ## Domain Decomposition -/

/-- A subdomain of the lattice, represented by a finite set of points. -/
structure Subdomain (L : Lattice3D) where
  /-- Lattice points included in the subdomain. -/
  points : Finset L.Point

/-- Check if an edge is in a subdomain. -/
def Subdomain.containsEdge (S : Subdomain L) (e : Edge L) : Prop :=
  e.1 ∈ S.points

/-- Check if a face is in a subdomain. -/
def Subdomain.containsFace (S : Subdomain L) (f : Face L) : Prop :=
  f.1 ∈ S.points

instance (S : Subdomain L) (e : Edge L) : Decidable (S.containsEdge e) := by
  dsimp [Subdomain.containsEdge]
  infer_instance

instance (S : Subdomain L) (f : Face L) : Decidable (S.containsFace f) := by
  dsimp [Subdomain.containsFace]
  infer_instance

/-! ## Ghost Sets -/

/-- Ghost edges: outside the subdomain but needed by a face inside. -/
def ghostEdges (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (S : Subdomain L) : Set (Edge L) :=
  { e | ¬S.containsEdge e ∧ ∃ f, S.containsFace f ∧ e ∈ curlE_stencil L f }

/-- Ghost faces: outside the subdomain but needed by an edge inside. -/
def ghostFaces (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (S : Subdomain L) : Set (Face L) :=
  { f | ¬S.containsFace f ∧ ∃ e, S.containsEdge e ∧ f ∈ curlB_stencil L e }

/-- Extend an electric field with ghost values outside the subdomain. -/
def extendElectric (S : Subdomain L) (E_local E_ghost : ElectricField L) : ElectricField L :=
  fun e => if S.containsEdge e then E_local e else E_ghost e

/-- Extend a magnetic field with ghost values outside the subdomain. -/
def extendMagnetic (S : Subdomain L) (B_local B_ghost : MagneticField L) : MagneticField L :=
  fun f => if S.containsFace f then B_local f else B_ghost f

/-- Extension with perfect ghost data is the identity. -/
theorem extendElectric_self (S : Subdomain L) (E : ElectricField L) :
    extendElectric S E E = E := by
  funext e
  simp [extendElectric]

/-- Extension with perfect ghost data is the identity. -/
theorem extendMagnetic_self (S : Subdomain L) (B : MagneticField L) :
    extendMagnetic S B B = B := by
  funext f
  simp [extendMagnetic]

/-- Local Maxwell update using ghost-extended fields. -/
def localMaxwellUpdate (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) (S : Subdomain L)
    (E_ghost : ElectricField L) (B_ghost : MagneticField L) :
    MaxwellPhase L → MaxwellPhase L :=
  fun x =>
    let E' := extendElectric S x.1 E_ghost
    let B' := extendMagnetic S x.2 B_ghost
    (curlB L B' + ohmicDamping L sys E', -curlE L E')

/-- Extension agrees with the true field on a face stencil when ghost data match. -/
private theorem extendElectric_eq_on_stencil (L : Lattice3D)
    [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (S : Subdomain L) (E E_ghost : ElectricField L) (f : Face L)
    (hface : S.containsFace f)
    (hghost : ∀ e, e ∈ ghostEdges L S → E_ghost e = E e) :
    ∀ e ∈ curlE_stencil L f, extendElectric S E E_ghost e = E e := by
  intro e he
  by_cases hEdge : S.containsEdge e
  · simp [extendElectric, hEdge]
  · have hghostMem : e ∈ ghostEdges L S := by
      exact ⟨hEdge, ⟨f, hface, he⟩⟩
    have hghostEq : E_ghost e = E e := hghost e hghostMem
    simp [extendElectric, hEdge, hghostEq]

/-- Extension agrees with the true field on an edge stencil when ghost data match. -/
private theorem extendMagnetic_eq_on_stencil (L : Lattice3D)
    [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (S : Subdomain L) (B B_ghost : MagneticField L) (e : Edge L)
    (hedge : S.containsEdge e)
    (hghost : ∀ f, f ∈ ghostFaces L S → B_ghost f = B f) :
    ∀ f ∈ curlB_stencil L e, extendMagnetic S B B_ghost f = B f := by
  intro f hf
  by_cases hFace : S.containsFace f
  · simp [extendMagnetic, hFace]
  · have hghostMem : f ∈ ghostFaces L S := by
      exact ⟨hFace, ⟨e, hedge, hf⟩⟩
    have hghostEq : B_ghost f = B f := hghost f hghostMem
    simp [extendMagnetic, hFace, hghostEq]

/-- Local update matches global update on edges in the subdomain. -/
theorem localMaxwellUpdate_eq_on_edges (L : Lattice3D)
    [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) (S : Subdomain L)
    (E_ghost : ElectricField L) (B_ghost : MagneticField L)
    (x : MaxwellPhase L)
    (_hghostE : ∀ e, e ∈ ghostEdges L S → E_ghost e = x.1 e)
    (hghostB : ∀ f, f ∈ ghostFaces L S → B_ghost f = x.2 f) :
    ∀ e, S.containsEdge e →
      (localMaxwellUpdate L sys S E_ghost B_ghost x).1 e =
        (maxwellUpdate L sys x).1 e := by
  intro e hedge
  have hE : extendElectric S x.1 E_ghost e = x.1 e := by
    simp [extendElectric, hedge]
  have hcurl :
      curlB L (extendMagnetic S x.2 B_ghost) e = curlB L x.2 e := by
    apply curlB_local L
    intro f hf
    exact extendMagnetic_eq_on_stencil L S x.2 B_ghost e hedge hghostB f hf
  have hOhm :
      ohmicDamping L sys (extendElectric S x.1 E_ghost) e =
        ohmicDamping L sys x.1 e := by
    simp [ohmicDamping, hE]
  simp [localMaxwellUpdate, maxwellUpdate, hcurl, hOhm]

/-- Local update matches global update on faces in the subdomain. -/
theorem localMaxwellUpdate_eq_on_faces (L : Lattice3D)
    [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) (S : Subdomain L)
    (E_ghost : ElectricField L) (B_ghost : MagneticField L)
    (x : MaxwellPhase L)
    (hghostE : ∀ e, e ∈ ghostEdges L S → E_ghost e = x.1 e)
    (_hghostB : ∀ f, f ∈ ghostFaces L S → B_ghost f = x.2 f) :
    ∀ f, S.containsFace f →
      (localMaxwellUpdate L sys S E_ghost B_ghost x).2 f =
        (maxwellUpdate L sys x).2 f := by
  intro f hface
  have hcurl :
      curlE L (extendElectric S x.1 E_ghost) f = curlE L x.1 f := by
    apply curlE_local L
    intro e he
    exact extendElectric_eq_on_stencil L S x.1 E_ghost f hface hghostE e he
  simp [localMaxwellUpdate, maxwellUpdate, hcurl]

/-- Combined coherence: local update matches global update on subdomain edges and faces. -/
theorem localMaxwellUpdate_eq_on_subdomain (L : Lattice3D)
    [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) (S : Subdomain L)
    (E_ghost : ElectricField L) (B_ghost : MagneticField L)
    (x : MaxwellPhase L)
    (hghostE : ∀ e, e ∈ ghostEdges L S → E_ghost e = x.1 e)
    (hghostB : ∀ f, f ∈ ghostFaces L S → B_ghost f = x.2 f) :
    (∀ e, S.containsEdge e →
        (localMaxwellUpdate L sys S E_ghost B_ghost x).1 e =
          (maxwellUpdate L sys x).1 e) ∧
    (∀ f, S.containsFace f →
        (localMaxwellUpdate L sys S E_ghost B_ghost x).2 f =
          (maxwellUpdate L sys x).2 f) := by
  constructor
  · intro e hedge
    exact localMaxwellUpdate_eq_on_edges L sys S E_ghost B_ghost x hghostE hghostB e hedge
  · intro f hface
    exact localMaxwellUpdate_eq_on_faces L sys S E_ghost B_ghost x hghostE hghostB f hface

/-- Coherence with perfect ghost data: local update matches global update. -/
theorem maxwell_domain_coherence (L : Lattice3D) [NeZero L.nx] [NeZero L.ny] [NeZero L.nz]
    (sys : LatticeMaxwell L) (S : Subdomain L) (x : MaxwellPhase L) :
    localMaxwellUpdate L sys S x.1 x.2 x = maxwellUpdate L sys x := by
  -- Ghost data equals the global fields, so extensions are identities.
  simp [localMaxwellUpdate, maxwellUpdate, extendElectric_self, extendMagnetic_self]

end

end Gibbs.Hamiltonian.Examples
