#!/usr/bin/env python3
"""Count current-source proofs and report the audited conditional theorem boundary."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[1]
core=['MatrixPositivity','IntervalSoundness','GramSoundness','DiagonalCheck','ListDotSoundness','FastGram']
basehash=hashlib.sha256(b''.join((root/f'Certificate/{name}.lean').read_bytes() for name in core)+(root/'lean-toolchain').read_bytes()+(root/'lakefile.toml').read_bytes()).hexdigest()
reports=[];stale=[]
for p in sorted((root/'logs/matrices').glob('*Proof.json')):
 try:r=json.loads(p.read_text())
 except json.JSONDecodeError:continue
 if not r.get('verified'):continue
 paths=[root/Path(*r[k].split('.')).with_suffix('.lean') for k in ['data_module','proof_module']]
 shash=hashlib.sha256(b''.join(f.read_bytes() for f in paths)).hexdigest()
 current=(r.get('source_sha256')==shash and r.get('core_sha256')==basehash and all(f.with_suffix('.olean').exists() for f in paths) and set(r.get('axioms',[])) <= {'propext','Classical.choice','Quot.sound'})
 if current:reports.append(r)
 else:stale.append(f"{r['identity']}:{r['block']}")
counts={name:sum(r['identity']==name for r in reports) for name in ['H1_0','H1_1','H1_2','H2']}
ideal_count=0
for name in ['H1_0','H1_1','H1_2','H2']:
 p=root/'logs/ideals'/f'{name}.json'
 if not p.exists():continue
 r=json.loads(p.read_text())
 files=[root/'Certificate/SparsePolynomial.lean']+[root/f'Certificate/Identities/{name}{kind}.lean' for kind in ['Data','Proof']]
 if r.get('quotient_stage_verified') and r.get('source_sha256')==hashlib.sha256(b''.join(f.read_bytes() for f in files)).hexdigest() and all(f.with_suffix('.olean').exists() for f in files):ideal_count+=1
multiplier_count=0
p=root/'logs/multipliers_verified.json'
if p.exists():
 r=json.loads(p.read_text())
 files=[root/'Certificate'/(name+'.lean') for name in ['SparsePolynomial','MultiplierSoundness','PrimitiveData','MultiplierCertificates']]
 if r.get('source_sha256')==hashlib.sha256(b''.join(f.read_bytes() for f in files)).hexdigest() and all(f.with_suffix('.olean').exists() for f in files):multiplier_count=r['verified_count']
sos_core=['MatrixPositivity','IntervalSoundness','GramSoundness','DiagonalCheck','ListDotSoundness','FastGram','SparsePolynomial','SOSPolynomial']
sos_hash=hashlib.sha256(b''.join((root/f'Certificate/{name}.lean').read_bytes() for name in sos_core)).hexdigest()
sos_count=0
for p in (root/'logs/sos').glob('*Proof.json'):
 r=json.loads(p.read_text())
 modules=[r['matrix_data'],r['data']]+r.get('auxiliary',[])+[r['proof']]
 files=[root/Path(*module.split('.')).with_suffix('.lean') for module in modules]
 prooftext=files[-1].read_text()
 chunked=bool(r.get('auxiliary'))
 short='import Certificate.ShortMultiplication' in prooftext
 jobcore=sos_core+(['FastExpansion'] if chunked or 'import Certificate.FastExpansion' in prooftext or 'import Certificate.SparseExpansion' in prooftext else [])
 jobcore += [name for name in ['SparseExpansion','MergeArithmetic','ChunkedExpansion','ShortMultiplication'] if 'import Certificate.'+name in prooftext or name=='MergeArithmetic' and (short or chunked) or name=='ChunkedExpansion' and chunked]
 jobhash=hashlib.sha256(b''.join((root/f'Certificate/{name}.lean').read_bytes() for name in jobcore)).hexdigest()
 if r.get('expansion_verified') and r.get('core_sha256')==jobhash and r.get('source_sha256')==hashlib.sha256(b''.join(f.read_bytes() for f in files)).hexdigest() and all(f.with_suffix('.olean').exists() for f in files):sos_count+=1
def assembly_current(tag):
 report=root/'logs/assembly'/(tag+'.json')
 if not report.exists():return False
 r=json.loads(report.read_text())
 source=root/Path(*r['module'].split('.')).with_suffix('.lean')
 imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
 deps=[root/Path(*i.split('.')).with_suffix('.olean') for i in imports if i.startswith('Certificate.')]
 return (r.get('verified') and source.with_suffix('.olean').exists()
  and set(r.get('axioms',[])) <= {'propext','Classical.choice','Quot.sound'}
  and r.get('source_sha256')==hashlib.sha256(source.read_bytes()).hexdigest()
  and all(p.exists() for p in deps)
  and r.get('imports_sha256')==hashlib.sha256(b''.join(p.read_bytes() for p in deps)).hexdigest())
assembled={(ident,b) for ident,n in [('H1_0',75),('H1_1',75),('H1_2',75),('H2',23)]
 for b in range(n) if assembly_current(f'{ident}B{b:03d}')}
bundles=root/'Certificate/Assembly/block_bundles.json'
if bundles.exists():
 for bundle in json.loads(bundles.read_text()):
  if assembly_current(bundle['module'].split('.')[-1]):
   assembled.update((bundle['identity'],b) for b in bundle['blocks'])
assembly_blocks=len(assembled)
assembly_identities=[ident for ident in ['H1_0','H1_1','H1_2','H2'] if assembly_current(ident+'Proof')]
conditional=False
confinement=False
packing_bridge=False
compact_exclusion=False
curvature_controls=False
published_geometry=False
full_hv_area=False
critical_family_area=False
boundary_area=False
frame_boundary_area=False
boundary_support=False
interior_stars=False
convex_curvature=False
minimizing_hexagon_ratio_body_verified=False
normalized_minimizer_verified=False
radial_boundary_construction_verified=False
radial_boundary_lipschitz_verified=False
global_ratio_comparison_verified=False
general_hexagon_area_verified=False
critical_hexagon_at_midpoint_uniqueness_verified=False
supporting_face_midpoint_verified=False
critical_boundary_contact_coverage_verified=False
global_support_uniqueness_verified=False
critical_midpoint_regular_curve_transport_verified=False
critical_midpoint_support_face_endpoints_verified=False
critical_midpoint_extreme_point_coverage_verified=False
critical_midpoint_hull_reconstruction_verified=False
critical_midpoint_flat_gap_reduction_verified=False
critical_midpoint_global_order_verified=False
critical_midpoint_full_boundary_coverage_verified=False
boundary_successor_homeomorphism_verified=False
boundary_successor_regular_curve_transport_verified=False
support_deficit_coercivity_verified=False
boundary_pointwise_gradient_bound_verified=False
boundary_pointwise_tangent_bound_verified=False
boundary_uniform_tangent_lipschitz_verified=False
boundary_uniform_gradient_lipschitz_verified=False
angular_boundary_regular_verified=False
angular_boundary_velocity_ac_verified=False
balanced_successor_velocity_ac_verified=False
determinant_clock_bijection_verified=False
normalized_balanced_velocity_ac_verified=False
balanced_state_dynamics_verified=False
balanced_state_boundary_values_verified=False
critical_midpoint_local_c1_extension_verified=False
critical_midpoint_c1_curve_transport_verified=False
critical_midpoint_positive_tangent_transport_verified=False
critical_midpoint_uniform_tangent_scale_verified=False
critical_midpoint_adjacent_velocity_nondegeneracy_verified=False
critical_midpoint_transversality_verified=False
minimizer_gauge_c1_verified=False
radial_boundary_c1_verified=False
radial_boundary_regular_verified=False
critical_midpoint_successor_continuity_verified=False
critical_midpoint_cycle_verified=False
global_support_normal_continuity_verified=False
global_tangent_direction_continuity_verified=False
supporting_face_contact_verified=False
exposed_point_contact_verified=False
contact_hull_reconstruction_verified=False
critical_midpoint_unique_support_verified=False
critical_midpoint_normal_continuity_verified=False
critical_hexagon_midpoint_contacts_verified=False
critical_hexagon_nondegeneracy_verified=False
normalized_boundary_root_contacts_verified=False
general_hexagon_ratio_packing_comparison_verified=False
critical_hexagon_attainment_verified=False
critical_contact_compactness_verified=False
minimizer_irreducibility_verified=False
initial_critical_hexagon_normalization_verified=False
universal_packing_reduction_verified=False
constructed_state_strict_stars_verified=False
fundamental_arc_verified=False
frame_endpoint_matching_verified=False
normalized_frame_trajectory_constructed=False
balanced_frame_boundary_constructed=False
unconditional_packing_density_theorem_verified=False
unconditional_hexagon_ratio_theorem_verified=False
final_report=root/'logs/final/verification.json'
if final_report.exists():
 r=json.loads(final_report.read_text())
 conditional=bool(r.get('conditional_density_theorem_verified'))
 conditional=conditional and r.get('lakefile_sha256')==hashlib.sha256((root/'lakefile.toml').read_bytes()).hexdigest()
 conditional=conditional and r.get('lean_toolchain')==(root/'lean-toolchain').read_text().strip()
 for item in r.get('source_and_artifact_manifest',[]):
  for kind in ['source','artifact']:
   p=root/item[kind]
   if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=item[kind+'_sha256']:
    conditional=False
  for suffix,expected in item.get('artifact_companions',{}).items():
   p=root/(item['artifact']+suffix)
   if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:conditional=False
 if r.get('geometric_provenance_sha256'):
  conditional=conditional and r['geometric_provenance_sha256']==hashlib.sha256((root/'data/geometric_provenance.json').read_bytes()).hexdigest()
 if r.get('published_geometry_provenance_sha256'):
  conditional=conditional and r['published_geometry_provenance_sha256']==hashlib.sha256((root/'data/published_geometry_provenance.json').read_bytes()).hexdigest()
 published_geometry=conditional and bool(r.get('published_geometry_components_verified'))
 full_hv_area=conditional and bool(r.get('full_hales_vajjha_area_estimate_verified'))
 critical_family_area=conditional and bool(r.get('area_estimate_from_critical_hexagon_family_verified'))
 boundary_area=conditional and bool(r.get('boundary_integral_area_identity_verified'))
 frame_boundary_area=conditional and bool(r.get('area_identity_from_frame_boundary_verified'))
 boundary_support=conditional and bool(r.get('supporting_hexagons_from_convex_boundary_verified'))
 interior_stars=conditional and bool(r.get('strict_interior_stars_from_convex_boundary_verified'))
 convex_curvature=conditional and bool(r.get('curvature_from_convex_boundary_verified'))
 minimizing_hexagon_ratio_body_verified=conditional and bool(r.get('minimizing_hexagon_ratio_body_verified'))
 normalized_minimizer_verified=conditional and bool(r.get('normalized_minimizer_verified'))
 radial_boundary_construction_verified=conditional and bool(r.get('radial_boundary_construction_verified'))
 radial_boundary_lipschitz_verified=conditional and bool(r.get('radial_boundary_lipschitz_verified'))
 global_ratio_comparison_verified=conditional and bool(r.get('global_ratio_comparison_verified'))
 general_hexagon_area_verified=conditional and bool(r.get('general_hexagon_area_verified'))
 critical_hexagon_at_midpoint_uniqueness_verified=conditional and bool(r.get('critical_hexagon_at_midpoint_uniqueness_verified'))
 supporting_face_midpoint_verified=conditional and bool(r.get('supporting_face_midpoint_verified'))
 critical_boundary_contact_coverage_verified=conditional and bool(r.get('critical_boundary_contact_coverage_verified'))
 global_support_uniqueness_verified=conditional and bool(r.get('global_support_uniqueness_verified'))
 critical_midpoint_regular_curve_transport_verified=conditional and bool(r.get('critical_midpoint_regular_curve_transport_verified'))
 critical_midpoint_support_face_endpoints_verified=conditional and bool(r.get('critical_midpoint_support_face_endpoints_verified'))
 critical_midpoint_extreme_point_coverage_verified=conditional and bool(r.get('critical_midpoint_extreme_point_coverage_verified'))
 critical_midpoint_hull_reconstruction_verified=conditional and bool(r.get('critical_midpoint_hull_reconstruction_verified'))
 critical_midpoint_flat_gap_reduction_verified=conditional and bool(r.get('critical_midpoint_flat_gap_reduction_verified'))
 critical_midpoint_global_order_verified=conditional and bool(r.get('critical_midpoint_global_order_verified'))
 critical_midpoint_full_boundary_coverage_verified=conditional and bool(r.get('critical_midpoint_full_boundary_coverage_verified'))
 boundary_successor_homeomorphism_verified=conditional and bool(r.get('boundary_successor_homeomorphism_verified'))
 boundary_successor_regular_curve_transport_verified=conditional and bool(r.get('boundary_successor_regular_curve_transport_verified'))
 support_deficit_coercivity_verified=conditional and bool(r.get('support_deficit_coercivity_verified'))
 boundary_pointwise_gradient_bound_verified=conditional and bool(r.get('boundary_pointwise_gradient_bound_verified'))
 boundary_pointwise_tangent_bound_verified=conditional and bool(r.get('boundary_pointwise_tangent_bound_verified'))
 boundary_uniform_tangent_lipschitz_verified=conditional and bool(r.get('boundary_uniform_tangent_lipschitz_verified'))
 boundary_uniform_gradient_lipschitz_verified=conditional and bool(r.get('boundary_uniform_gradient_lipschitz_verified'))
 angular_boundary_regular_verified=conditional and bool(r.get('angular_boundary_regular_verified'))
 angular_boundary_velocity_ac_verified=conditional and bool(r.get('angular_boundary_velocity_ac_verified'))
 constructed_state_strict_stars_verified=conditional and bool(r.get('constructed_state_strict_stars_verified'))
 fundamental_arc_verified=conditional and bool(r.get('fundamental_arc_verified'))
 frame_endpoint_matching_verified=conditional and bool(r.get('frame_endpoint_matching_verified'))
 normalized_frame_trajectory_constructed=conditional and bool(r.get('normalized_frame_trajectory_constructed'))
 balanced_frame_boundary_constructed=conditional and bool(r.get('balanced_frame_boundary_constructed'))
 unconditional_packing_density_theorem_verified=conditional and bool(r.get('unconditional_packing_density_theorem_verified'))
 unconditional_hexagon_ratio_theorem_verified=conditional and bool(r.get('unconditional_hexagon_ratio_theorem_verified'))
 balanced_successor_velocity_ac_verified=conditional and bool(r.get('balanced_successor_velocity_ac_verified'))
 determinant_clock_bijection_verified=conditional and bool(r.get('determinant_clock_bijection_verified'))
 normalized_balanced_velocity_ac_verified=conditional and bool(r.get('normalized_balanced_velocity_ac_verified'))
 balanced_state_dynamics_verified=conditional and bool(r.get('balanced_state_dynamics_verified'))
 balanced_state_boundary_values_verified=conditional and bool(r.get('balanced_state_boundary_values_verified'))
 critical_midpoint_local_c1_extension_verified=conditional and bool(r.get('critical_midpoint_local_c1_extension_verified'))
 critical_midpoint_c1_curve_transport_verified=conditional and bool(r.get('critical_midpoint_c1_curve_transport_verified'))
 critical_midpoint_positive_tangent_transport_verified=conditional and bool(r.get('critical_midpoint_positive_tangent_transport_verified'))
 critical_midpoint_uniform_tangent_scale_verified=conditional and bool(r.get('critical_midpoint_uniform_tangent_scale_verified'))
 critical_midpoint_adjacent_velocity_nondegeneracy_verified=conditional and bool(r.get('critical_midpoint_adjacent_velocity_nondegeneracy_verified'))
 critical_midpoint_transversality_verified=conditional and bool(r.get('critical_midpoint_transversality_verified'))
 minimizer_gauge_c1_verified=conditional and bool(r.get('minimizer_gauge_c1_verified'))
 radial_boundary_c1_verified=conditional and bool(r.get('radial_boundary_c1_verified'))
 radial_boundary_regular_verified=conditional and bool(r.get('radial_boundary_regular_verified'))
 critical_midpoint_successor_continuity_verified=conditional and bool(r.get('critical_midpoint_successor_continuity_verified'))
 critical_midpoint_cycle_verified=conditional and bool(r.get('critical_midpoint_cycle_verified'))
 global_support_normal_continuity_verified=conditional and bool(r.get('global_support_normal_continuity_verified'))
 global_tangent_direction_continuity_verified=conditional and bool(r.get('global_tangent_direction_continuity_verified'))
 supporting_face_contact_verified=conditional and bool(r.get('supporting_face_contact_verified'))
 exposed_point_contact_verified=conditional and bool(r.get('exposed_point_contact_verified'))
 contact_hull_reconstruction_verified=conditional and bool(r.get('contact_hull_reconstruction_verified'))
 critical_midpoint_unique_support_verified=conditional and bool(r.get('critical_midpoint_unique_support_verified'))
 critical_midpoint_normal_continuity_verified=conditional and bool(r.get('critical_midpoint_normal_continuity_verified'))
 critical_hexagon_midpoint_contacts_verified=conditional and bool(r.get('critical_hexagon_midpoint_contacts_verified'))
 critical_hexagon_nondegeneracy_verified=conditional and bool(r.get('critical_hexagon_nondegeneracy_verified'))
 normalized_boundary_root_contacts_verified=conditional and bool(r.get('normalized_boundary_root_contacts_verified'))
 general_hexagon_ratio_packing_comparison_verified=conditional and bool(r.get('general_hexagon_ratio_packing_comparison_verified'))
 critical_hexagon_attainment_verified=conditional and bool(r.get('critical_hexagon_attainment_verified'))
 critical_contact_compactness_verified=conditional and bool(r.get('critical_contact_compactness_verified'))
 minimizer_irreducibility_verified=conditional and bool(r.get('minimizer_irreducibility_verified'))
 initial_critical_hexagon_normalization_verified=conditional and bool(r.get('initial_critical_hexagon_normalization_verified'))
 universal_packing_reduction_verified=conditional and bool(r.get('universal_packing_reduction_verified'))
 confinement=conditional and bool(r.get('new_geometric_confinement_deductions_verified'))
 packing_bridge=conditional and bool(r.get('conditional_convex_body_packing_theorem_verified'))
 compact_exclusion=conditional and bool(r.get('compact_exclusion_from_area_estimate_verified'))
 curvature_controls=conditional and bool(r.get('simplex_control_reconstruction_from_curvature_verified'))
print(json.dumps(dict(generated_matrix_proofs_passed=len(reports),required=248,per_identity=counts,stale_reports=stale,polynomial_reductions_passed=ideal_count,polynomial_reductions_required=4,multipliers_passed=multiplier_count,multipliers_required=75,gram_expansions_passed=sos_count,gram_expansions_required=248,assembled_blocks_passed=assembly_blocks,assembled_blocks_required=248,assembled_identities=assembly_identities,conditional_density_theorem_verified=conditional,new_geometric_confinement_deductions_verified=confinement,conditional_convex_body_packing_theorem_verified=packing_bridge,compact_exclusion_from_area_estimate_verified=compact_exclusion,simplex_control_reconstruction_from_curvature_verified=curvature_controls,published_geometry_components_verified=published_geometry,full_hales_vajjha_area_estimate_verified=full_hv_area,area_estimate_from_critical_hexagon_family_verified=critical_family_area,boundary_integral_area_identity_verified=boundary_area,area_identity_from_frame_boundary_verified=frame_boundary_area,supporting_hexagons_from_convex_boundary_verified=boundary_support,strict_interior_stars_from_convex_boundary_verified=interior_stars,curvature_from_convex_boundary_verified=convex_curvature,minimizing_hexagon_ratio_body_verified=minimizing_hexagon_ratio_body_verified,normalized_minimizer_verified=normalized_minimizer_verified,radial_boundary_construction_verified=radial_boundary_construction_verified,radial_boundary_lipschitz_verified=radial_boundary_lipschitz_verified,global_ratio_comparison_verified=global_ratio_comparison_verified,general_hexagon_area_verified=general_hexagon_area_verified,general_hexagon_ratio_packing_comparison_verified=general_hexagon_ratio_packing_comparison_verified,critical_hexagon_attainment_verified=critical_hexagon_attainment_verified,critical_contact_compactness_verified=critical_contact_compactness_verified,minimizer_irreducibility_verified=minimizer_irreducibility_verified,initial_critical_hexagon_normalization_verified=initial_critical_hexagon_normalization_verified,universal_packing_reduction_verified=universal_packing_reduction_verified,critical_hexagon_midpoint_contacts_verified=critical_hexagon_midpoint_contacts_verified,critical_hexagon_nondegeneracy_verified=critical_hexagon_nondegeneracy_verified,normalized_boundary_root_contacts_verified=normalized_boundary_root_contacts_verified,critical_midpoint_unique_support_verified=critical_midpoint_unique_support_verified,critical_midpoint_normal_continuity_verified=critical_midpoint_normal_continuity_verified,critical_hexagon_at_midpoint_uniqueness_verified=critical_hexagon_at_midpoint_uniqueness_verified,supporting_face_contact_verified=supporting_face_contact_verified,exposed_point_contact_verified=exposed_point_contact_verified,contact_hull_reconstruction_verified=contact_hull_reconstruction_verified,supporting_face_midpoint_verified=supporting_face_midpoint_verified,critical_boundary_contact_coverage_verified=critical_boundary_contact_coverage_verified,global_support_uniqueness_verified=global_support_uniqueness_verified,critical_midpoint_regular_curve_transport_verified=critical_midpoint_regular_curve_transport_verified,critical_midpoint_support_face_endpoints_verified=critical_midpoint_support_face_endpoints_verified,critical_midpoint_extreme_point_coverage_verified=critical_midpoint_extreme_point_coverage_verified,critical_midpoint_hull_reconstruction_verified=critical_midpoint_hull_reconstruction_verified,critical_midpoint_flat_gap_reduction_verified=critical_midpoint_flat_gap_reduction_verified,critical_midpoint_global_order_verified=critical_midpoint_global_order_verified,critical_midpoint_full_boundary_coverage_verified=critical_midpoint_full_boundary_coverage_verified,boundary_successor_homeomorphism_verified=boundary_successor_homeomorphism_verified,boundary_successor_regular_curve_transport_verified=boundary_successor_regular_curve_transport_verified,critical_midpoint_local_c1_extension_verified=critical_midpoint_local_c1_extension_verified,critical_midpoint_c1_curve_transport_verified=critical_midpoint_c1_curve_transport_verified,critical_midpoint_positive_tangent_transport_verified=critical_midpoint_positive_tangent_transport_verified,critical_midpoint_uniform_tangent_scale_verified=critical_midpoint_uniform_tangent_scale_verified,critical_midpoint_adjacent_velocity_nondegeneracy_verified=critical_midpoint_adjacent_velocity_nondegeneracy_verified,critical_midpoint_transversality_verified=critical_midpoint_transversality_verified,minimizer_gauge_c1_verified=minimizer_gauge_c1_verified,radial_boundary_c1_verified=radial_boundary_c1_verified,radial_boundary_regular_verified=radial_boundary_regular_verified,critical_midpoint_successor_continuity_verified=critical_midpoint_successor_continuity_verified,critical_midpoint_cycle_verified=critical_midpoint_cycle_verified,global_support_normal_continuity_verified=global_support_normal_continuity_verified,global_tangent_direction_continuity_verified=global_tangent_direction_continuity_verified,support_deficit_coercivity_verified=support_deficit_coercivity_verified,boundary_pointwise_gradient_bound_verified=boundary_pointwise_gradient_bound_verified,boundary_pointwise_tangent_bound_verified=boundary_pointwise_tangent_bound_verified,boundary_uniform_tangent_lipschitz_verified=boundary_uniform_tangent_lipschitz_verified,boundary_uniform_gradient_lipschitz_verified=boundary_uniform_gradient_lipschitz_verified,angular_boundary_regular_verified=angular_boundary_regular_verified,angular_boundary_velocity_ac_verified=angular_boundary_velocity_ac_verified,balanced_successor_velocity_ac_verified=balanced_successor_velocity_ac_verified,determinant_clock_bijection_verified=determinant_clock_bijection_verified,normalized_balanced_velocity_ac_verified=normalized_balanced_velocity_ac_verified,balanced_state_dynamics_verified=balanced_state_dynamics_verified,balanced_state_boundary_values_verified=balanced_state_boundary_values_verified,constructed_state_strict_stars_verified=constructed_state_strict_stars_verified,fundamental_arc_verified=fundamental_arc_verified,frame_endpoint_matching_verified=frame_endpoint_matching_verified,normalized_frame_trajectory_constructed=normalized_frame_trajectory_constructed,balanced_frame_boundary_constructed=balanced_frame_boundary_constructed,unconditional_packing_density_theorem_verified=unconditional_packing_density_theorem_verified,unconditional_hexagon_ratio_theorem_verified=unconditional_hexagon_ratio_theorem_verified,full_density_theorem_verified=unconditional_packing_density_theorem_verified),indent=2))
