# Reinhardt degree-6 certificate verification

**Status: the certificate has been extended to a conditional theorem about the
original packing density of a convex body.** Lattice packing density, a packing
from a circumscribed hexagon, midpoint normalization, the numerical compact-domain
exclusion, and reconstruction of the controls from curvature are now formalized.
The full Hales–Vajjha Theorem 5.0.6 area estimate is now proved in its published
strict star domain, including all contact points, coordinate changes, and area
overlap arguments. HV Section 3.2's area/cost identity is also proved from the
six frame arcs covering the boundary once. Convexity now supplies the supporting
tangent lines, the inverse state frame supplies the contacts and enclosing
hexagons, and the strict interior star conditions are derived. Nonnegative
boundary curvature is now derived from convexity as well. The universal
reduction now requires a normalized balanced frame for an area-preserving
image of the constructed minimizing body. A global minimizer of the
area/hexagon-infimum ratio is now constructed, normalized to hexagon-area
infimum `2*sqrt(3)`, and equipped with an explicit Lipschitz radial boundary.
The hexagon-area infimum is now attained, its exact area/covolume is proved,
and its ratio is compared to the original packing density for every disc. The
minimizer is irreducible, and an area-preserving coordinate change normalizes
its attained hexagon. Every critical hexagon of the minimizer now has six
genuine sides, with all six side midpoints on the body frontier. The initial
normalization places the six regular roots on that frontier. Each critical
midpoint now has a unique supporting line; its normalized support normal is
continuous on the compact set of critical midpoints. The enclosing critical
hexagon is also unique as a geometric region at each such midpoint. Construction
of the special balanced frame boundary remains unfinished. Every supporting face
now contains a critical midpoint. Every boundary point lies on an edge of a
critical hexagon and has a unique supporting line. The normalized support normal
and an oriented tangent direction are now continuous over the whole boundary.
The critical midpoint locus carries a continuous successor homeomorphism with
the six-point balance identities. The gauge and radial boundary map are now C1,
with an explicit derivative that is nonzero in directions transverse to the
radius. Full midpoint coverage and global order of the critical successor are
now proved. Exact area variation and compactness now give globally Lipschitz
gauge gradients and oriented tangents on the boundary. The explicit angular
radial curve is regular and C1, and its actual velocity is absolutely continuous
on every bounded interval. Assembly of the normalized balanced frame remains
unfinished. This is **not** yet an unconditional packing theorem.
The reproducibility audit is in `logs/final/verification.json`.

The project verifies the supplied fixed certificate. It does not rerun the
optimization that discovered it. See `WORK_LOG.md` for the development history.

## Exact result and proof chain

The stored degree-4 potential has 255 rational monomials and denominator `2^40`.
Its cleared differential and boundary certificates have degree 6. Their boundary
constant is exactly

```
gamma = -11322938895932849560433 / 1484340697497600000000
        + (108969540019475 / 17592186044416) * sqrt(3).
```

`NumericBound.lean` proves, strictly,

```
8950112 / 10000000 < gamma / (2 * sqrt(3)).
```

The assembly connects the actual certificate data through the following chain:

1. Each of the **248 actual Gram matrices** is positive semidefinite over the reals.
2. All **248 polynomial expansions**, **75 distinct multiplier certificates**, and
   **four determinant/square-root reductions** are checked exactly.
3. Each complete SOS sum is identified with its recorded polynomial; all **four
   assembled target inequalities** now pass. These are no longer merely separate
   block checks or identities with assumed positivity.
4. The recorded targets are identified with the derivatives and boundary change of
   the actual stored potential. Positive scaling constants are canceled explicitly.
5. The differential inequalities are combined using nonnegative simplex controls
   and integrated along an absolutely continuous trajectory. The final theorem
   uses the original matrix control equations and normalized endpoints.
6. The six inequalities describing the published HV compact domain imply all
   twelve certificate constraints involving `X`, including the height and denominator
   bounds. Their equivalence with the three rotated cusp/wall charts is checked.
7. For trajectories with cost at most **3.11**, the original group ODE, endpoints,
   and height bound imply all six angular-sector constraints and the group norm
   bound. The regularity needed here is derived from absolute continuity and the
   a.e. ODE. Higher-cost trajectories already exceed `gamma`, which Lean proves is
   strictly below 3.11. Consequently the final theorem needs **no upper cost bound**.
8. An explicit lattice packing proves `area(K)/|det(v,w)| <= packingDensity(K)`
   for the original ball-limsup definition. A circumscribed symmetric hexagon
   supplies the nonoverlapping translates. Two normalized side midpoints give
   lattice covolume `2*sqrt(3)`. The packing-density comparison is proved locally.
9. The scalar expression in the HV area estimate is at least `269/300` outside
   the compact domain. This is above `gamma/(2*sqrt(3))`, so compact-domain
   membership is derived in the low-density case, without an interval grid or
   comparison with the exact smoothed-octagon optimum.
10. Nonnegative curvature reconstructs nonnegative simplex controls and the exact
    `X` control equation. Absolute continuity supplies coordinate derivatives
    almost everywhere; differentiating the determinant constraint supplies the
    tangent identity. The highest-level theorem does not assume those controls.
11. The final theorem concludes `8950112/10000000 < Packing.packingDensity K`
    from the remaining explicit geometric data. The audit checks 320 named results.
12. HV 5.0.6 is now proved from geometric minimality. The final theorem
    `packing_density_bound_of_curvature_critical_hexagon_family` derives its area
    estimate and constructs the packing hexagon, using the explicit boundary
    presentation and its area identity.
13. The newer `packing_density_bound_of_curvature_boundary_critical_hexagons`
    also derives the area identity. A radial-sector Jacobian gives measured area
    from the boundary arcs; their interiors do not overlap, and the omitted
    boundary and endpoint rays have zero area. The six determinant integrands
    sum to `6h`, so half their integral is exactly the trajectory cost.
14. `packing_density_bound_of_curvature_convex_boundary` derives the supporting
    geometry and strict interior stars as well. A zero star coordinate would
    force adjacent tangents parallel, contradicting the determinant constraints.
    Continuity extends the area estimate to endpoints; no strict endpoint-star
    assumption is added.
15. `packing_density_bound_of_convex_frame` also derives the curvature sign.
    The signed distance from a supporting tangent has a local minimum. Its
    second derivative is therefore nonnegative wherever it exists. A checked
    derivative of the frame velocity identifies this with the matrix curvature
    expression. The final input path contains neither curvature nor controls.

For a state `x` in the stated region, the differential inequalities are

```
r_k * (cost - D_g V[gX]) - D_X V[N_k] >= 0,
r_k = -tr(X Z_k),     N_k = r_k I + 2 X Z_k.
```

The denominator normalization is important. The proof uses this exact denominator,
not a differently scaled star function. The boundary inequality is

```
gamma <= V(R, R^-1 X R) - V(I, X).
```

The intermediate theorem `CompactTrajectory.cost_lower_bound` proves
`gamma <= integral cost` from the original matrix ODE and compact domain.
`NormalizedTrajectory.cost_lower_bound` replaces compact-domain membership by
the earlier geometric area estimate. `CurvatureTrajectory.cost_lower_bound`
also reconstructs the controls and `X` equation from curvature.

The per-body frame theorem
`Packing.packing_density_bound_of_convex_frame` uses the original benchmark
packing definitions (copied verbatim inside `Certificate.Packing`). It requires
an absolutely continuous `FrameTrajectory`, a `FrameTrace` whose six arcs cover
the convex boundary with injective, disjoint interiors, and minimum
circumscribed-hexagon area at least `2*sqrt(3)`. The trajectory includes weak star
inequalities, determinant constraints, the group ODE, and normalized endpoints.
Nonnegative curvature, controls, strict interior stars, supporting lines,
inverse frames, contacts, enclosing strips, both area statements, and the
lattice packing are all derived. The second derivative only needs to exist
almost everywhere; continuity of curvature is not assumed.

These presentation hypotheses are not asserted to hold automatically for every
convex disc. `MinimizerConstruction.lean` now constructs a global ratio minimizer
with hexagon-area infimum `2*sqrt(3)` and an antipodal Lipschitz radial boundary.
The radial map is not yet the balanced frame boundary required above. Earlier
conditional interfaces remain available.

## Constructed minimizing body and radial boundary

`ratioMinimizingBody` is selected from a proved existence theorem, not supplied
as an assumption. The objective is

```
criticalHexArea K = inf { volume H.set | H : Hex, K ⊆ H.set }
hexagonRatio K = (volume K).toReal / (criticalHexArea K).toReal.
```

The infimum is positive, finite, and attained by an actual enclosing hexagon
for every symmetric convex disc. An invertible linear change of
coordinates multiplies both areas by the same absolute determinant.

The existence proof maximizes an inscribed parallelogram determinant to put
any body between the coordinate diamond and square. The resulting family of
compact convex sets is compact in the Vietoris/Hausdorff topology. Nearby
bodies fit into slightly expanded copies of one another, giving a quantitative
ratio comparison and lower semicontinuity. The ratio therefore attains its
global minimum. A scalar dilation normalizes the hexagon-area infimum to
`2*sqrt(3)` and proves area minimality among all bodies whose circumscribed
hexagons have area at least that amount.

`ratioMinimizingBoundary` is the gauge radial homeomorphism. On a unit vector
`u` it is exactly `u / gauge K u`. It covers the entire frontier, is injective,
is antipodal, and is Lipschitz on the circle. These facts construct a usable
boundary without assuming an existing boundary curve. They do **not** supply
the C1 balanced multi-curve, Lipschitz tangents, or normalized frame ODE.

`all_discs_ratio_bound_of_minimizer_frame` now reduces a lower bound for the
hexagon ratios of **all** symmetric convex discs to constructing a `FrameTrace`
for an area-preserving linear image of the chosen minimizer. This permits the
initial frame to be aligned without changing the normalized objective.
`hexagonRatio_le_packingDensity` now proves the general comparison with the
original benchmark density. Therefore `all_discs_packing_bound_of_minimizer_frame`
reduces the **original universal packing-density bound** to the remaining
balanced frame construction. No independent density comparison remains an input.

| Construction | Entry point |
| --- | --- |
| Affine compactness normalization | `DiscAffineNormalization.lean` |
| Compact normalized family and nondegenerate limits | `NormalizedDiscCompactness.lean`, `NormalizedDiscInterior.lean` |
| Nearby-body and area comparison | `DiscHausdorffComparison.lean` |
| Hexagon infimum and affine invariance | `CriticalHexagonInfimum.lean` |
| Global ratio minimizer | `MinimizingDisc.lean` |
| Scalar normalization and area minimality | `NormalizedMinimizer.lean` |
| Explicit boundary and Lipschitz regularity | `RadialBoundaryConstruction.lean`, `RadialBoundaryRegularity.lean` |
| C1 radial boundary and nonzero transverse derivatives | `MinimizerGaugeDifferentiability.lean` |
| Chosen body and boundary | `MinimizerConstruction.lean` |
| Conditional reduction for all bodies | `MinimizerFrameReduction.lean`, `PackingFromConstructedMinimizer.lean` |
| Exact area of arbitrary hexagons | `HexagonFanAlgebra.lean`, `HexagonFanArea.lean`, `HexagonCovolumeArea.lean`, `HexagonCompactness.lean` |
| Original packing-density comparison | `PackingFromHexagonInfimum.lean` |
| Attained minimum enclosing hexagon | `HexagonParameters.lean`, `HexagonParameterBounds.lean`, `CriticalHexagonAttainment.lean` |
| Irreducibility and chosen critical hexagon | `MinimizerIrreducibility.lean`, `MinimizerHexagonConstruction.lean` |
| Compact critical family and contact locus | `CriticalHexagonFamilyCompactness.lean` |
| Area-preserving initial coordinates | `CriticalHexagonNormalization.lean` |

Every represented hexagon, including degenerate cases, is a compact convex
disc. Its six inscribed triangles have total area equal to the lattice covolume.
The already verified lattice-density theorem gives the opposite area inequality,
so actual hexagon area equals covolume. Taking the infimum then proves the
comparison with the original packing density, without assuming that lattice
packings are optimal.

To prove attainment, normals and vertices are encoded by twelve real
coordinates. A fixed inner diamond bounds the normal coefficients; an upper
area bound controls every vertex coordinate using contained triangles. The
closed incidence constraints force lattice nondegeneracy even in a limit.
The area objective is a continuous determinant and attains its minimum on
this compact parameter set.

`ratioMinimizingHexagon` is an actual minimum-area enclosing hexagon of
`ratioMinimizingBody`, with area and covolume exactly `2*sqrt(3)`. The body's
irreducibility is also proved: any proper symmetric convex subdisc has smaller
critical-hexagon area. The family of critical hexagons is compact, and its
contact locus is a closed subset of the frontier. **Coverage of the frontier
by these contacts is not yet proved.**

`initiallyNormalizedMinimizer` is the image under an explicit area-preserving
linear map. All six edge midpoints of the chosen hexagon become the sixth
roots of unity, and global ratio minimality is preserved. The new midpoint-contact
theorem proves that these six roots lie on the actual body frontier; their convex
hull is an inscribed regular hexagon. This establishes the initial normalized
contact configuration, but does not yet construct the moving balanced boundary.

`criticalHexagon_of_minimizer_midpoint_frontier` now proves midpoint contact
for **every** critical hexagon of the constructed minimizer, with no additional
nondegeneracy or midpoint-membership assumptions. The proof has two parts:

- An exact rational side-variation formula, combined with convex separation,
  shows that a missing midpoint would permit a smaller enclosing hexagon.
- A hexagon with a collapsed side or redundant strip is a linear image of a
  square. Cutting a missing pair of opposite corners gives a smaller enclosing
  hexagon for every proper convex subdisc. A strictly convex comparison body
  gives ratio strictly below one, so the minimizer cannot itself be a hexagon.
  Thus all its critical hexagons have six genuine sides.

The new proofs are in `HexagonSideVariation`, `HexagonMidpointContact`,
`HexagonRelabeling`, `StrictHexagonBoundaryContacts`, `MinimizerNotHexagon`,
`HexagonDegeneracy`, `SquareCornerCut`, and `MinimizerMidpointContacts`.

The supporting-line step is now proved as well. If a second normalized support
form passed through a critical midpoint, the exact side variation fixing that
midpoint would decrease area quadratically. Thus the supporting line is unique.
`criticalHexagon_of_minimizer_supporting_form` handles any nonzero supporting
functional: it is a **positive** multiple of the hexagon's side normal. The
statement applies to every critical hexagon and all six midpoints, and is
transported to the normalized body's six regular roots.

`criticalMidpointSet` is a compact subset of the minimizer frontier containing
all those midpoints. The normalized normal coefficients form a continuous
function on this set. The proof uses the compact parameter family and uniqueness
to descend its continuous normal coordinates through the midpoint projection.
It does **not** claim that this set covers the whole frontier, that the normal
is Lipschitz, or by itself that the entire boundary is C1. Global normal
continuity and C1 radial regularity are now proved separately below. The
geometric critical hexagon is also proved unique at each critical midpoint. Equality is of the actual hexagon regions;
vertex labels and orientation may differ.

The new proofs are in `HexagonSecondVariation`, `HexagonAdmissibleVariation`,
`HexagonUniqueSupport`, `SupportingFormNormalization`,
`MinimizerMidpointTangents`, `CriticalMidpointNormalContinuity`,
`CriticalHexagonMidpointUniqueness`, and `MinimizerCriticalHexagonUniqueness`.

For the last uniqueness step, equal oriented area and a shared midpoint constrain
the next midpoint to a line. The neighboring supporting strips of the two
hexagons rule out displacement in either direction. Their midpoint
configurations agree, and unique supporting normals identify their strips.
`exists_unique_critical_hexagon_region` consequently gives an actual unique
critical region at every point of `criticalMidpointSet`.

## Full boundary contacts and unique supporting lines

`minimizer_support_face_midpoint` proves that every supporting face contains a
critical side midpoint. A supporting face is the set where a supporting line
touches the body; it may be a point or a whole segment.

The proof constructs symmetric slab cuts approaching the original body.
Irreducibility gives smaller minimum enclosing hexagons. Their parameters
have a subsequence converging to a strict critical hexagon, so eventually the
cut hexagons are strict and their side midpoints lie on the cut boundaries.
If all limiting midpoints avoided the shaved faces, all nearby midpoints would
be strictly inside the cut slab. A short convex-segment argument then makes
each cut-supporting line support the original body. This contradicts the
smaller hexagon area. Thus a critical midpoint lies on the requested face.

This closes the edge-contact coverage gap:
`criticalContactSet_eq_frontier_minimizer` proves that **every boundary point**
lies on an edge of a critical hexagon, including points on flat faces. The
support form of a face agrees with the unique supporting form at its critical
midpoint, identifying it with the critical hexagon's side normal.

`minimizer_frontier_unique_normalized_support` proves a unique supporting line
at **every** boundary point. Average any two normalized support forms there.
Both attain level one at a critical midpoint of the average form's supporting
face, and midpoint uniqueness forces the two forms to agree. Normalization is
legitimate because every nonzero supporting form has positive support level.
These are the boundary-contact and no-corners conclusions of HV Lemma 2.2.5.

The earlier, weaker supporting-face/contact argument and closed convex hull
reconstruction are also verified. The seven new modules are
`SymmetricSupportCuts`, `CriticalHexagonLimitTools`,
`MinimizerSupportFaceContact`, `MinimizerContactHull`, `SupportCutLocality`,
`MinimizerSupportFaceMidpoint`, and `MinimizerBoundarySupport`.

Both the critical **contact** set and the critical **midpoint** set are now
proved equal to the whole boundary. The successor is globally ordered.
Stronger tangent regularity and the normalized balanced frame remain to be
constructed. The coverage proof and boundary successor are described below.

## Continuous midpoint family and global tangent direction

`CriticalMidpointDynamics` and `CriticalMidpointCycle` construct the successor
map `N` on the actual critical midpoint set. It takes a midpoint to the next
midpoint of its uniquely determined, positively oriented critical hexagon.
Compactness and uniqueness prove continuity; the inverse is five successive
applications of `N`, so this is a homeomorphism. Lean checks
`N²(p)=N(p)-p`, `N³(p)=-p`, `N⁶(p)=p`, and
`det(p,N(p))=sqrt(3)/2`. All six midpoint coordinates vary continuously.
This supplies continuous motion on the known locus, without assuming that the
locus is the whole boundary or that the motion preserves boundary order.

`MinimizerBoundaryNormalContinuity` extends continuity of normalized support
normals to the **entire boundary**, including flat-face endpoints. Compact
critical edge-contact presentations project onto the boundary, and uniqueness
makes their normal coefficients agree on each projection fiber. The resulting
continuous tangent direction `t(p)` is nonzero and satisfies
`det(p,t(p))=1`; every body point lies on its supporting side. It agrees with
the previously constructed support normal at critical midpoints. A derivative
formula for the radial boundary is proved in the next section. A Lipschitz
bound for tangent directions remains separate work.

## C1 regularity of the radial boundary

`MinimizerGaugeDifferentiability` identifies the derivative of `gauge K x`, for
nonzero `x`, with the normalized support form at `x / gauge K x`. The support
inequalities at two nearby points bound the first-order error by the change
in these forms times their displacement. Their continuity proves a C1 gauge.
Consequently `x ↦ x / gauge K x` is C1 away from the origin. On the unit circle
this is exactly the boundary parametrization constructed earlier.

The explicit derivative along a curve with position `x` and velocity `v` is
also checked. Its determinant with the projected position is
`gauge K x ^ (-2) * det(x,v)`. Thus the derivative is nonzero for any direction
transverse to the radius, including tangent directions to the unit circle.
This supplies regular radial boundary parametrization; it does not establish
Lipschitz continuity of the tangent or regularity of a balanced critical family.

## Shorter route to the neighboring-midpoint parametrization

`CriticalMidpointTransversality` proves the hypotheses needed for the local
implicit-function approach. If `q=N(p)` is the next critical midpoint, then
`D gauge(K,q)[p]>0`. The map in `q` given by
`(gauge(K,q), det(p,q))` has an explicitly checked invertible derivative.
This uses strictness of the critical hexagon and the existing C1 gauge;
no coordinate-by-coordinate inverse or separate arclength construction is needed
for this transversality step.

`CriticalMidpointImplicit` now applies mathlib's C1 implicit-function theorem.
It constructs an ambient local solution near each existing critical pair.
Local uniqueness and continuity identify that solution with the actual
successor on the midpoint locus. Any C1 curve in that locus carries all six
midpoint coordinates along C1 curves.

`CriticalMidpointOrientation` identifies the strict derivative and its action
on the normalized counterclockwise tangent `T(p)`, where `det(p,T(p))=1`.
For the local extension `ψ_p`, writing `q=N(p)`, `a=D gauge(K,p)[q]`,
and `b=D gauge(K,q)[p]`, Lean proves
`0<a<1`, `0<b<1`, and

```
D ψ_p(p)[T(p)] = (a/b) T(q).
```

This multiplier is continuous and uniformly bounded above and away from zero
on the compact midpoint locus. Adjacent tangents and the corresponding adjacent
velocities have strictly positive determinant. These are the local orientation
and nondegeneracy facts needed before a determinant-normalizing time change.

`CriticalMidpointRegularCurves` supplies the link to actual motion. A
curve in the midpoint locus has gauge constantly one, so its velocity is tangent.
The checked derivative formula therefore preserves nonzero velocity under the
successor, without an extra tangency assumption.

Full midpoint coverage and global monotonicity are now proved below. Stronger
tangent estimates and construction of `FrameTrajectory`/`FrameTrace` remain.
The final frame requires absolutely continuous state coordinates; the C1
position curves and bounded tangent-speed multiplier do not prove Lipschitz
variation of boundary tangents. No full boundary curve in the midpoint locus
is assumed by these results.

`CriticalMidpointSupportFace` now identifies both endpoints of every supporting
face as actual critical midpoints. The proof perturbs a support form by a
vanishing positive multiple of a tangent coordinate and uses compactness to
retain the maximizing midpoint in the limit. Applying this to the coordinate
and its negative supplies both endpoints, including singleton faces.

`CriticalMidpointBoundaryGaps` proves that every extreme point is a critical
midpoint and that the ordinary convex hull of the midpoint locus equals the
whole minimizing body. Any boundary point still missing from the locus lies
in a nontrivial flat boundary segment with critical endpoints. Choosing the
nearest critical points on either side gives an open gap containing no
critical midpoint. This reduces full coverage to excluding such flat gaps.
The following modules now complete that step.

## Full midpoint coverage and global order

`CriticalMidpointSectors` places the entire boundary in the six triangles
associated with any reference critical hexagon. Strict support inequalities
exclude the triangle sides for points strictly between consecutive midpoint
rays. A finite linear-inequality calculation, using the balance relation and
positive determinant, forces the next two points into the next two triangles.

`CriticalMidpointOrder` excludes the remaining endpoints using the fixed
critical determinant. It proves sector monotonicity for every iterate, then
upgrades this to the global comparison

```
0 < det(N(p),N(q))  iff  0 < det(p,q).
```

`CriticalMidpointArcGaps` propagates an empty midpoint interval through the
successor. The convex-hull reconstruction shows that any such empty angular
interval has endpoints with a common supporting form. After three steps,
the two endpoint hexagons therefore have the same three oriented normals.
`CriticalMidpointCoverage` proves that these normals fix the supporting-line
intersections and hence the same midpoint, contradicting the nontrivial gap.
Thus `criticalMidpointSet = frontier ratioMinimizingBody`, and every boundary
point is the midpoint of a unique critical hexagon region. These are the
coverage and monotonicity conclusions of HV Lemmas 2.2.6 and 2.2.7.

`MinimizerBoundarySuccessor` transports the existing homeomorphism to the
entire boundary, with its balance, sixfold-periodicity, fixed-determinant,
and global-order identities. The local C1 and regular-curve transport results
now apply to arbitrary boundary curves; no additional midpoint-membership
hypothesis is needed. This still does not construct the absolutely continuous
state coordinates or the normalized `FrameTrajectory`/`FrameTrace`.

## Published geometry now checked

The new proofs use actual planar Lebesgue area throughout:

| Source/result | Checked statement | File |
| --- | --- | --- |
| HV Lemma 2.2.5, boundary conclusions | Every supporting face contains a critical midpoint; every boundary point lies on a critical edge and has a unique supporting line | `Certificate/MinimizerSupportFaceMidpoint.lean`, `MinimizerBoundarySupport.lean` |
| Triangle area | Exact determinant formula, including degenerate triangles | `Certificate/TriangleArea.lean` |
| HV Lemma 5.0.4 | Explicit midpoint coordinates, exterior-edge incidences, six triangle areas, and interior-area sum | `Certificate/HVTriangleGeometry.lean` |
| HV Lemma 5.0.5 | Parallel-cut square-root identity for arbitrary planar triangles | `Certificate/ParallelCutArea.lean` |
| Competing hexagon | An actual circumscribed-hexagon candidate; its area and lattice covolume both equal `4-d*e` | `Certificate/CornerCut.lean`, `Certificate/CutHexagonArea.lean` |
| HV 5.0.6, single-corner step | Actual area minimality forces a point on the cut; convexity gives a contained triangle with the stated square-root contribution | `Certificate/HVCornerArea.lean` |
| HV 5.0.6, baseline | The inscribed regular hexagon has area `3*sqrt(3)/2`; any convex body containing its vertices has at least that area | `Certificate/RegularHexagonArea.lean` |
| HV 5.0.6, all corners | Invertible coordinate transport and three rotated corner-contact theorems, including zero-contribution cases | `Certificate/HexagonLinearTransport.lean`, `HVCornerCoordinates.lean`, `HVFirstCorner.lean`, `HVRotation.lean` |
| HV 5.0.6, assembly | Six corner pieces and the regular hexagon overlap only on null sets; their areas add | `Certificate/HVCornerRegions.lean`, `HVAreaAssembly.lean` |
| HV 5.0.6, complete | `areaScore u v w <= area(K)/(2*sqrt(3))`, from actual hexagon-area minimality in the strict star domain | `Certificate/HVAreaBound.lean` |
| Critical hexagon area | Actual Lebesgue area equals `2*sqrt(3)`, agreeing with the computed lattice covolume | `Certificate/NormalizedHexagonArea.lean` |
| Explicit packing hexagon | Constructs the normalized hexagon and its lattice, then pulls it back to the original body | `Certificate/NormalizedHexagon.lean` |
| Radial sector area | Change of variables computes actual area from a convex boundary arc; gauge proves injectivity | `Certificate/RadialSectorArea.lean` |
| Boundary area assembly | A finite arc cover fills the body except for null boundary and endpoint rays | `Certificate/BoundaryArcArea.lean` |
| HV Section 3.2 | Derives the six frame-arc derivatives and proves actual area equals trajectory cost | `Certificate/FrameBoundaryCalculus.lean`, `FrameBoundaryArea.lean` |
| Convex supporting tangents | Convex separation and Fermat's theorem put the whole body on the correct side of each tangent | `Certificate/ConvexBoundarySupport.lean` |
| Canonical enclosing hexagons | Inverts the state matrix; derives contacts and strip containment from the boundary | `Certificate/StateLinearFrame.lean`, `TangentHexagonSides.lean`, `FrameBoundarySupport.lean` |
| Strict interior stars | Equality would force adjacent tangents parallel, contradicting the determinant constraints | `Certificate/FrameBoundaryStar.lean` |
| HV Lemma 2.4.6 | Derives nonnegative signed curvature from the convex supporting tangent and actual second derivatives | `Certificate/ConvexBoundaryCurvature.lean`, `FrameAcceleration.lean` |
| Final integration | Derives curvature, controls, supporting geometry, and both area statements from the normalized boundary and hexagon-area minimality | `Certificate/PackingFromConvexFrame.lean` |
| Certificate normalization | The geometric expression, divided by `2*sqrt(3)`, equals the exact `areaScore` used in compact exclusion | `Certificate/HVAreaExpression.lean` |

The single-corner theorem is in square coordinates. Its assumptions are compactness,
convexity, central symmetry, containment in the square, membership of the adjacent
midpoints, and a lower bound on the area of **every** enclosing symmetric hexagon.
It proves contact rather than assuming it. The numerical parameter is the parallel
cut's scale; the proof constructs a strictly smaller enclosing hexagon if contact
is absent, using compactness to make that strict improvement possible.

**HV Theorem 5.0.6 is now proved in the published strict star domain.**
`hales_vajjha_area_bound` assumes a compact convex centrally symmetric body,
`u,v,w > 0`, `u*v+v*w+w*u=1`, containment in the three explicit supporting
strips, membership of the six regular midpoints, and a lower bound of
`2*sqrt(3)` on every enclosing symmetric hexagon's area. It derives all three
contact contributions and the full normalized area bound. No contact point,
triangle-area bound, or disjointness premise is supplied.
`volume_normalizedHex` also proves the critical hexagon's actual area is
`2*sqrt(3)`. The wrapper `hales_vajjha_area_bound_of_minimal_hexagon` consequently
takes ordinary area minimality of the explicit hexagon and derives the normalized
minimum-area premise, rather than assuming its area/covolume identification.

Strict positivity matches the paper's open star domain; this theorem does not
claim an extension to all degenerate parameter triples. The final
`BoundaryCriticalHexagonFamily` states this strictness explicitly, but the
strongest theorem no longer requires this family as input. It derives strict
interior stars and canonical supporting hexagons from a `FrameTrace` and the
trajectory's weak star and determinant conditions. Convexity supplies the
curvature sign as well. The scalar area estimate is then extended to endpoints
by continuity. Ratio-minimizer existence, scalar normalization, and a Lipschitz
radial boundary are now proved, as are the midpoint contacts of every critical
hexagon of the minimizer. Full boundary midpoint coverage and global order of
the critical family are also proved. The remaining published inputs concern
stronger tangent regularity and construction of the normalized balanced frame.
No existence theorem, minimizer, or boundary curve has been postulated
as an axiom. Source identification and scope are recorded in
`data/published_geometry_provenance.json`.

## Verified confinement and remaining published input

`NewCertificate.OnRegion` is determinant one together with **19 explicit polynomial
inequalities**, enumerated in `Certificate/PrimitiveData.lean`:

- Six angular-sector inequalities for the group matrix and its rotated versions.
- The matrix bound `||g||_F^2 <= 16/5`.
- Three positive denominator bounds `r_k >= 769/10000`.
- The height bounds `1 <= h <= 12/5` and a redundant quadratic bound on `X`.
- Three horoball and three half-plane inequalities.

All nineteen constraints are now proved for the low-cost case that needs the
certificate. The new proof uses simpler arguments than a literal replay of M14:

- A rational inequality bounds the sum of the three star coordinates, giving
  `1 <= h <= 12/5` without numerical maximization.
- Integrating angular velocity constructs an actual continuous angle. Its endpoint
  and cost bound rule out winding; applying the result to the two conjugated paths
  proves the six sector inequalities.
- A scalar energy estimate for
  `E=(g11-g22)^2+(g12+g21)^2=||g||_F^2-2`, using both endpoints,
  gives `E <= 6/5`. This avoids hyperbolic distance and a Taylor bound on cosh.
- A separate theorem upgrades the group equation from a.e. derivatives of an AC
  path to derivatives at every interior point. No extra C1 assumption is added.

The additional compact-exclusion proof uses the symmetric expression

```
A(u,v,w) = 3/4 + (max(0, vw - 2u sqrt(vw))
                  + max(0, uw - 2v sqrt(uw))
                  + max(0, uv - 2w sqrt(uv))) / 4.
```

For nonnegative star coordinates with `uv+vw+wu=1`, `A < 269/300` implies all
six HV compact-domain inequalities. In a cusp, `u+v <= 13/50` is already enough
to prove `A >= 269/300`. Away from a cusp, an ordered least coordinate
`u <= 1/15` forces `vw >= 18/25`, giving the same bound. Both arguments use
rational inequalities and checked square-root identities. This proves the
exclusion needed for the new lower bound, not the stronger published theorem
that compares with the smoothed octagon.

The remaining published geometric work is the balanced-boundary construction:

- Establish Lipschitz tangent bounds and the required regularity of the balanced
  critical family. The radial boundary is now C1 and regular, with its derivative
  explicitly proved. Supporting normals are continuous over the whole boundary,
  and the geometric critical hexagon is unique at each critical midpoint.
- Construct the AC frame coordinates, determinant and weak star conditions,
  `g'=gX`, endpoints, and six-arc coverage with disjoint interiors from that
  geometric family. The existing radial Lipschitz boundary is insufficient.

The exact remaining existence statement is:

```lean
∃ (L : E ≃ₗ[ℝ] E) (path : FrameTrajectory),
  |LinearMap.det (L : E →ₗ[ℝ] E)| = 1 ∧
  FrameTrace path (L '' ratioMinimizingBody)
```

This is documented as an outstanding goal; it has not been introduced as an
axiom or a proved theorem. `all_discs_packing_bound_of_minimizer_frame` supplies
the universal packing conclusion once this statement is proved.

The ratio-to-original-packing comparison, hexagon attainment, exact
area/covolume, and initial coordinate normalization are now proved. No equality
between the full packing supremum and the lattice optimum is needed for the
universal lower-bound reduction.

All conditional theorem inputs remain explicit, with no added axioms. The
hexagon-area lower bound for the chosen minimizer is now a theorem, and the
ratio comparison to all other discs follows from global minimality.
The original benchmark's unproved `reinhardt`
theorem is never imported. `data/geometric_provenance.json` records the original
definitions and the recovered Fable source used for the lattice/hexagon proofs;
those proofs have been adapted and rechecked, not trusted as compiled artifacts.

`RegionSanity.lean` proves that the normalized circle's initial state satisfies all
19 inequalities and both determinant relations. Thus the algebraic domain is nonempty;
this is not a proof that all packing trajectories satisfy the domain assumptions.

## Main files

| File | Purpose |
|---|---|
| `Certificate/Assembly/*Proof.lean` | Four fully assembled polynomial inequalities |
| `Certificate/NewCertificateVertex*.lean` | Convert the three differential targets to actual control inequalities |
| `Certificate/NewCertificateBoundary.lean` | Convert the boundary target to the potential gap |
| `Certificate/TrajectoryCost.lean` | Integrate the potential along an absolutely continuous path |
| `Certificate/ControlTheorem.lean` | Specialize integration to the actual fixed certificate |
| `Certificate/ConfinementRho.lean`, `ConfinementState.lean` | All twelve state constraints from the compact domain |
| `Certificate/ConfinementDomain.lean` | Checked equivalence with the three cusp/wall charts |
| `Certificate/ConfinementPolar.lean`, `ConfinementSector.lean` | Construct the angle and prove the sector bound |
| `Certificate/ConfinementEnergy.lean`, `ConfinementMatrixNorm.lean` | Scalar energy estimate and group norm bound |
| `Certificate/ConfinementGroupPath.lean` | Both rotated paths and all seven group constraints |
| `Certificate/ConfinementRegularity.lean`, `ConfinementFromAC.lean` | Derive the regularity used by confinement |
| `Certificate/ConfinementFinal.lean` | Final compact-trajectory cost and density theorems |
| `Certificate/Final.lean` | Earlier lower-level theorem with explicit region membership |
| `Certificate/CompactExclusion.lean` | Rational compact exclusion from the scalar area estimate |
| `Certificate/AreaControlledTrajectory.lean` | Cost bound without a compact-domain hypothesis |
| `Certificate/PackingDefinitions.lean` | Exact original benchmark packing definitions |
| `Certificate/PackingLattice.lean`, `PackingHexagon.lean` | Actual lattice packing and density comparison |
| `Certificate/PackingGeometry.lean` | Covolume normalization from the side midpoints |
| `Certificate/CurvatureControl.lean` | Reconstruct simplex controls from nonnegative curvature |
| `Certificate/CurvatureTrajectory.lean` | AC derivatives, determinant tangency, and the full control ODE |
| `Certificate/PackingFinal.lean` | Earlier conditional theorem with a supplied area estimate |
| `Certificate/HVAreaBound.lean` | Full HV 5.0.6 in the strict star domain |
| `Certificate/NormalizedHexagon.lean` | Explicit normalized hexagon and its packing lattice |
| `Certificate/PackingFromCriticalHexagons.lean` | Final theorem with the area estimate derived from geometric presentation |
| `Certificate/FrameBoundaryStar.lean` | Derives strict interior star conditions from the convex boundary |
| `Certificate/PackingFromConvexBoundary.lean` | Earlier interface that takes a curvature trajectory |
| `Certificate/FrameTrajectory.lean` | Frame path without assumed curvature or controls |
| `Certificate/ConvexBoundaryCurvature.lean`, `FrameAcceleration.lean` | Convexity implies the matrix curvature sign |
| `Certificate/PackingFromConvexFrame.lean` | Strongest current theorem, deriving curvature as well |
| `Certificate.lean` | Root import for the final result |
| `scripts/status.py` | Current-source component counts and final verification status |
| `scripts/verify_certificate.py` | Final build, axiom audit, and source/artifact manifest |

Successful audits use only `propext`, `Classical.choice`, and `Quot.sound`. The
certificate checks use `decide +kernel`; there are no accepted `sorry` proofs,
new axioms, or `native_decide` in the verified chain. An old failed attempt's log
may contain diagnostic `sorryAx`; such an attempt is not counted as verified.

## Reproduce the build

Pinned versions: Lean `leanprover/lean4:v4.33.0`, mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The tested workflow reuses the existing read-only compiled mathlib cache. Set
`REINHARDT_CACHED_PROJECT` to another matching cache when moving the project.
No changes are made to that external cache. For already checked components:

```sh
python3 scripts/build_sos_assembly.py --identity H1_0 --resume
python3 scripts/build_sos_assembly.py --identity H1_1 --resume
python3 scripts/build_sos_assembly.py --identity H1_2 --resume
python3 scripts/build_sos_assembly.py --identity H2 --resume
python3 scripts/ensure_cached_module.py Mathlib.Analysis.Convex.Measure
python3 scripts/verify_certificate.py --audit-built
python3 scripts/status.py
```

`--audit-built` requires the local modules to have been compiled already. It
rebuilds the root and runs a fresh axiom audit of all 114 named theorems, rejecting
stale local imports. It avoids rerunning expensive proof searches for unchanged
certificates. Without this option the verifier recompiles the final proof stages.

`python3 scripts/verify_certificate.py --rebuild-local` walks the complete local
import graph in dependency order and verifies every local module, reusing only
eligible content-cache hits. This is the longer replay option. A separate clean
standalone `lake build` has not been validated; `lakefile.toml` pins its dependency.

The final verifier checks the original-input and exact-certificate hashes, audits
114 named theorems, and writes `logs/final/verification.json` only after every
stage passes. That report explicitly distinguishes a conditional theorem from an
unconditional packing theorem. It also records all local Lean sources and compiled
artifacts used by the final theorem.

## Efficient exact checks

The generator discards zero terms before ordinary Gram expansion, uses ordered
polynomial merging, and multiplies with the shorter outer factor. The three
104-by-104 blocks use checked row witnesses and a checked tree of additions.
H1 aggregate sums use 74 separately checked additions per identity, grouped into
10 modules. Twenty-five small block-assembly proofs share each module, reducing
repeated import overhead. None of these changes alters the certificate coefficients.

Representative compiler times, excluding queue time:

| Check | Earlier method | Selected method |
|---|---:|---:|
| Ordinary 34-by-34 Gram expansion | 10.61 s | 4.35 s |
| Largest ordinary multiplier product | 10.85 s | 6.56 s |
| 104-by-104 Gram expansion | Monolithic attempts exceeded 180 s | 211.83 s across three modules |
| All 75 H1_0 block assemblies | Individually loaded modules | 20.52 s across three bundles |

These are individual measurements, not a benchmark of total proof speed. The
monolithic H1_0 aggregate sum exceeded 240 seconds; the replacement checked tree
completed successfully. Caching binds source content, compiler options and dependency
artifacts, prevents duplicate builds, and separates queue time from compiler time.
Twenty-seven cache and metadata-conversion regression tests pass. A single compiler remains the default because
concurrent heavy jobs caused memory pressure.

## Build-validation speedup (2026-10-28)

A repeated build of `CriticalMidpointCycle.lean` fell from **273.69 s to
34.72 s** (7.88 times faster). Dependency validation fell from 248.17 s to
12.02 s; Lean compilation itself was 24.58 s before and 22.67 s after. This
is one local before/after measurement, not a claim that all remaining work
will run eight times faster. Both builds compiled freshly: the same 154
legacy imports without provenance still prevented cache hits.

The combined root build and importing axiom audit now take **62.70 s**,
compared with 726.45 s in the prior run, while the audited target count grew
from 242 to 247. All 1,231 prior non-root modules retain identical source,
artifact, and companion hashes. The current audit still uses only `propext`,
`Classical.choice`, and `Quot.sound`; the unconditional theorem remains open.

Two changes remove bookkeeping overhead without relaxing validation:

- Exact dependency comparisons memoize pairs of shared containers within one
  comparison, checking each pair once. Source/artifact/companion hashes,
  compiler options, admission checks, and post-build input checks remain.
- A one-off streaming conversion compacted 111 legacy records from
  29,687,986,237 bytes to 93,031,639 bytes. It compared every parsed JSON event
  against the expanded saved representation before replacing each record.
  This preserves values, scalar types, key order, and array order. No proof
  sources or compiled artifacts were changed by the conversion.

Evidence: `logs/workflow_speed_benchmark.json`,
`logs/cache_compaction.jsonl`, and the two `logs/cache_speed_*.log` files.
The interrupted intermediate benchmark is excluded. The one-off converter is
`scripts/compact_legacy_cache.py` and uses `ijson`; ordinary builds remain
standard-library-only. New records already use compact shared storage.

## Data and provenance

`data/source_manifest.json` identifies the ten bundled original inputs by SHA-256.
`data/exact/manifest.json` identifies the four exact reconstructed certificates.
Both sets of hashes match their recorded values. `data/exact/H*.json` contains the
actual matrices and proposed factor witnesses; `data/polynomials/H*.json` contains
polynomial witnesses. The mathematical checks are performed in Lean, not delegated
to the Python generators or floating-point routines.

There are three identities with one 104-by-104 and 74 34-by-34 Gram matrices each.
The boundary identity has one 9-by-9 and 22 4-by-4 matrices. The exact reconstruction
uses the original dyadic rounding and residual correction in the first block.
The independent Python replay remains useful evidence but is not a substitute for
the now assembled Lean certificate checks.

The geometric continuation reused the 1,136 unchanged dependency modules from
the previous successful certificate audit. Their source and artifact hashes
were all checked, with no differences; see `logs/prior_certificate_integrity.json`
and the archived prior report. A redundant recompile of `NewCertificateVertex1`
hit a 180-second time limit; its unchanged, previously verified artifact was
retained. The new geometric modules were compiled, followed by the root build
and a fresh 32-theorem axiom audit. This is a checked incremental build, not a
claim that every module was recompiled from scratch during this continuation.

The subsequent published-geometry phase added eight modules and increased the
selected axiom audit to 47 results. All 1,145 prior dependency modules (excluding
the changed root import) retained their audited source/artifact hashes; see
`logs/published_geometry_prior_integrity.json`. The full area estimate was then
completed in the 71-theorem phase. The 84-theorem phase proved the boundary area
identity. The 105-theorem phase derives supporting hexagons and strict
interior stars from the normalized convex boundary, eliminating those separate
inputs. The current 114-theorem phase derives the curvature condition from
convexity, eliminating the separate curvature-sign input. The unconditional
density theorem remains explicitly marked unproved.

## Pointwise estimate used in the uniform tangent bound

`HexagonSupportCoercivity` polarizes the exact area-change formula without
assuming that the new normal fixes the old midpoint. Write `D = det(a,b) > 0`,
`S = det(slideA,slideB) < 0`, and `zeta = psi - phi1`. For a valid replacement
support normal, minimality proves

```
(-S) * (zeta(a)^2 + zeta(b)^2)
  <= 2 * D * (1 - psi((a+b)/2)) * (2 + zeta(slideA) + zeta(slideB)).
```

`HexagonSupportRegularity` proves that nearby normal changes are valid,
converts endpoint evaluations into an operator-norm bound, and uses a new
supporting contact `q` to bound the deficit by
`||psi-phi1|| * ||q-(a+b)/2||`. This gives a linear displacement bound.
No hyperbola-envelope or rolling-circle result is assumed.

`MinimizerPointwiseRegularity` applies the bound to every boundary point of
the constructed minimizer and transports it to the chosen tangent direction.
Precisely: for each fixed `p`, there are `C_p > 0` and a neighborhood of `p`
on which `||T(q)-T(p)|| <= C_p * ||q-p||`; the gauge gradient has the same
kind of estimate. These preliminary statements alone do not bound arbitrary pairs in one
neighborhood or provide a constant uniform over the boundary. The later
compact-family argument below now supplies that uniform bound; the normalized
frame is still not inferred from the pointwise statement.

## Uniform tangent regularity and an explicit regular curve

`CriticalFamilyRegularity` bounds the support coefficient and endpoint
evaluation conditioning uniformly over the compact positive critical-hexagon
family. `CriticalFamilyUniformVariation` proves that one neighborhood of zero
normal perturbations is valid for every member of the family. No continuous
choice of a critical-hexagon representative is required.

`MinimizerUniformRegularity` uses these facts to prove a genuine two-point
local Lipschitz bound and then, by compactness, a global one. There is a single
constant L for which `||T(p)-T(q)|| <= L * ||p-q||` for all boundary points,
and an analogous bound for the gauge gradient. Here T is the chosen oriented
tangent normalized by `det(p,T(p)) = 1`; it is not asserted to have unit norm.

`MinimizerAngularBoundary` constructs

```
gamma(t) = (cos(t),sin(t)) / gauge(K,(cos(t),sin(t))).
```

The curve is C1 and Lipschitz, its velocity never vanishes, and
`det(gamma(t),gamma'(t)) > 0`. Its gradient and tangent fields are absolutely
continuous on every bounded parameter interval. The exact velocity formula
`gamma'(t) = gauge(K,(cos(t),sin(t)))^(-2) * T(gamma(t))` proves absolute
continuity of the actual velocity. Its critical successor is also a regular
C1 curve.

The successor velocity and determinant-normalizing clock constructions below
now complete the regularity and time-change steps. A complete fundamental-arc
frame and unconditional packing conclusion are still not claimed.


## Normalized balanced curves and the matrix state

`SuccessorVelocityRegularity` proves absolute continuity of the actual
successor velocity from the explicit tangent transport formula. The positive
support evaluation in its denominator is bounded away from zero on each
compact interval. The remaining four companion curves are sums or negatives,
so all six balanced angular curves have absolutely continuous velocities.

`MinimizerDeterminantClock` constructs the positive speed

```
sigma(t) = sqrt((2/sqrt(3)) * det(gamma_0'(t), gamma_1'(t))).
tau(t) = integral from 0 to t of sigma(s) ds.
```

The adjacent velocity determinant is strictly positive. The speed is
continuous and absolutely continuous on every bounded interval.
`MinimizerClockInverse` uses periodicity to prove a uniform positive lower
bound, constructs the global increasing C1 inverse of tau, and reparametrizes
all six curves. Their adjacent velocity determinant is exactly sqrt(3)/2.
`MinimizerBalancedRegularity` proves that the actual velocities remain
absolutely continuous: the increasing C1 inverse is Lipschitz on compact
intervals and carries disjoint interval collections to disjoint collections.

`MinimizerBalancedState` forms the matrix with columns gamma_0 and
(2*gamma_1-gamma_0)/sqrt(3). The position matrix and its derivative both have
determinant one. Differentiating the first determinant gives the zero-trace
identity needed to assemble the state coordinates. Both determinant
constraints, absolute continuity of all eight certificate coordinates, and
the group differential equations are proved. `MinimizerFrameBoundary`
identifies the state's six root images and their velocities with the actual
boundary curves.

Remaining: establish the weak-star signs for this state, choose a fundamental
arc, normalize its initial frame, prove the rotated terminal state, and prove
that its six arcs cover the boundary with disjoint interiors. These are still
needed to construct `FrameTrajectory` and `FrameTrace` and discharge the
unconditional packing theorem. The existing completed-frame and full-density
status flags remain false.
