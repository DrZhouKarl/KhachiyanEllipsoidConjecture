import Khachiyan

/-!
# Current development axiom audit

This audit covers all completed nodes through T01 and C01--C03/T02 of `formalization_plan.md`,
including the smoke theorem, interface probes, and public mathematical declarations.
G04 includes actual affine volume transport and the retained-side N01 interface.
T01 is certified for actual volume and the canonical center in all positive dimensions.
T02 certifies uniform optimality using the actual cone family and its volume-ratio limit.
M05 and T03--T05, including the exact one-dimensional ratio, are also audited below.
The complete independent resolvent proof A01/M04R, including scalar integration
by parts, endpoint limits, and the general inequality, is also audited below.
-/

#print axioms Khachiyan.Smoke.log_le_sub_one
#print axioms Khachiyan.MathlibProbe.loewner_iff
#print axioms Khachiyan.MathlibProbe.strict_positive_iff
#print axioms Khachiyan.MathlibProbe.sqrt_squared
#print axioms Khachiyan.MathlibProbe.sqrt_of_square
#print axioms Khachiyan.MathlibProbe.sqrt_eq_half_power
#print axioms Khachiyan.MathlibProbe.euclidean_action
#print axioms Khachiyan.MathlibProbe.euclidean_inner
#print axioms Khachiyan.MathlibProbe.complex_rpow_monotone
#print axioms Khachiyan.MathlibProbe.eigenvalue_positive
#print axioms Khachiyan.MathlibProbe.determinant_product
#print axioms Khachiyan.MathlibProbe.trace_sum
#print axioms Khachiyan.MathlibProbe.determinant_positive
#print axioms Khachiyan.MathlibProbe.volume_linear_image

-- B01: foundational definitions and all explicit theorems.
#print axioms Khachiyan.V
#print axioms Khachiyan.MatR
#print axioms Khachiyan.rStar
#print axioms Khachiyan.unitBall
#print axioms Khachiyan.ellipsoid
#print axioms Khachiyan.outer
#print axioms Khachiyan.IsConvexBody
#print axioms Khachiyan.IsFeasible
#print axioms Khachiyan.maxEllipsoidVolume
#print axioms Khachiyan.IsMaxDet
#print axioms Khachiyan.IsJohnNormalized
#print axioms Khachiyan.centralHalfspace
#print axioms Khachiyan.rStar_pos
#print axioms Khachiyan.mem_unitBall
#print axioms Khachiyan.matrix_le_iff
#print axioms Khachiyan.matrix_strictlyPositive_iff
#print axioms Khachiyan.matrix_action_ofLp
#print axioms Khachiyan.inner_matrix_action
#print axioms Khachiyan.inner_eq_dotProduct
#print axioms Khachiyan.outer_apply
#print axioms Khachiyan.outer_eq_vecMulVec
#print axioms Khachiyan.outer_posSemidef
#print axioms Khachiyan.outer_action
#print axioms Khachiyan.trace_outer
#print axioms Khachiyan.mem_ellipsoid
#print axioms Khachiyan.center_mem_ellipsoid
#print axioms Khachiyan.ellipsoid_zero_one
#print axioms Khachiyan.isCompact_ellipsoid
#print axioms Khachiyan.measurableSet_ellipsoid
#print axioms Khachiyan.volume_ellipsoid_lt_top
#print axioms Khachiyan.IsFeasible.center_mem
#print axioms Khachiyan.volume_le_maxEllipsoidVolume
#print axioms Khachiyan.maxEllipsoidVolume_le_volume
#print axioms Khachiyan.maxEllipsoidVolume_mono
#print axioms Khachiyan.IsConvexBody.maxEllipsoidVolume_lt_top
#print axioms Khachiyan.IsMaxDet.posDef
#print axioms Khachiyan.IsMaxDet.subset
#print axioms Khachiyan.IsJohnNormalized.unitBall_subset

-- S01: all explicit scalar definitions and theorems, including the weighted certificate.
#print axioms Khachiyan.Scalar.f1
#print axioms Khachiyan.Scalar.f2
#print axioms Khachiyan.Scalar.R1
#print axioms Khachiyan.Scalar.R2
#print axioms Khachiyan.Scalar.F1
#print axioms Khachiyan.Scalar.F2
#print axioms Khachiyan.Scalar.crossing
#print axioms Khachiyan.Scalar.logConstant
#print axioms Khachiyan.Scalar.weightedEnvelope
#print axioms Khachiyan.Scalar.logAddExp
#print axioms Khachiyan.Scalar.logAddExp_mono
#print axioms Khachiyan.Scalar.exp_normalized_sum
#print axioms Khachiyan.Scalar.logAddExp_weighted_le
#print axioms Khachiyan.Scalar.convexOn_logAddExp
#print axioms Khachiyan.Scalar.convexOn_exp_comp
#print axioms Khachiyan.Scalar.f1_pos
#print axioms Khachiyan.Scalar.f2_pos
#print axioms Khachiyan.Scalar.f1_sq
#print axioms Khachiyan.Scalar.f2_sq
#print axioms Khachiyan.Scalar.exp_double_sub_log
#print axioms Khachiyan.Scalar.log_f1_exp
#print axioms Khachiyan.Scalar.log_f2_exp
#print axioms Khachiyan.Scalar.convexOn_double_sub
#print axioms Khachiyan.Scalar.convexOn_log_f1_exp
#print axioms Khachiyan.Scalar.convexOn_log_f2_exp
#print axioms Khachiyan.Scalar.convexOn_f1_exp
#print axioms Khachiyan.Scalar.convexOn_f2_exp
#print axioms Khachiyan.Scalar.concaveOn_F1
#print axioms Khachiyan.Scalar.concaveOn_F2
#print axioms Khachiyan.Scalar.f1_half
#print axioms Khachiyan.Scalar.f2_half
#print axioms Khachiyan.Scalar.exp_crossing
#print axioms Khachiyan.Scalar.F1_crossing
#print axioms Khachiyan.Scalar.F2_crossing
#print axioms Khachiyan.Scalar.hasDerivAt_f1
#print axioms Khachiyan.Scalar.hasDerivAt_f2
#print axioms Khachiyan.Scalar.hasDerivAt_f1_half
#print axioms Khachiyan.Scalar.hasDerivAt_f2_half
#print axioms Khachiyan.Scalar.hasDerivAt_F1_crossing
#print axioms Khachiyan.Scalar.hasDerivAt_F2_crossing
#print axioms Khachiyan.Scalar.concave_le_tangent
#print axioms Khachiyan.Scalar.F1_le_tangent
#print axioms Khachiyan.Scalar.F2_le_tangent
#print axioms Khachiyan.Scalar.joint_log_bound
#print axioms Khachiyan.Scalar.joint_log_eq_iff
#print axioms Khachiyan.Scalar.concaveOn_weightedEnvelope
#print axioms Khachiyan.Scalar.weightedEnvelope_crossing
#print axioms Khachiyan.Scalar.hasDerivAt_weightedEnvelope_crossing
#print axioms Khachiyan.Scalar.weightedEnvelope_le
#print axioms Khachiyan.Scalar.min_le_weightedEnvelope
#print axioms Khachiyan.Scalar.exp_logConstant
#print axioms Khachiyan.Scalar.rStar_eq_sqrt_exp_one
#print axioms Khachiyan.Scalar.exp_F1_log
#print axioms Khachiyan.Scalar.exp_F2_log
#print axioms Khachiyan.Scalar.log_R1
#print axioms Khachiyan.Scalar.log_R2
#print axioms Khachiyan.Scalar.log_R1_exp
#print axioms Khachiyan.Scalar.log_R2_exp
#print axioms Khachiyan.Scalar.exp_min
#print axioms Khachiyan.Scalar.log_eq_crossing_iff
#print axioms Khachiyan.Scalar.R1_half
#print axioms Khachiyan.Scalar.R2_half
#print axioms Khachiyan.Scalar.joint_bound
#print axioms Khachiyan.Scalar.joint_eq_iff
#print axioms Khachiyan.Scalar.joint_lt_of_ne_half
#print axioms Khachiyan.Scalar.joint_isGreatest
#print axioms Khachiyan.Scalar.R1_eq_R2_iff

-- M01: spectral definitions, matrix inequalities, and all supporting declarations.
#print axioms Khachiyan.Spectral.eigenvalue_pos
#print axioms Khachiyan.Spectral.det_eq_prod
#print axioms Khachiyan.Spectral.trace_eq_sum
#print axioms Khachiyan.Spectral.trace_mono
#print axioms Khachiyan.Spectral.rpow_eq_cfc
#print axioms Khachiyan.Spectral.cfc_spectral
#print axioms Khachiyan.Spectral.trace_cfc
#print axioms Khachiyan.Spectral.det_cfc
#print axioms Khachiyan.Spectral.trace_rpow
#print axioms Khachiyan.Spectral.det_rpow_eq_prod
#print axioms Khachiyan.Spectral.rpow_spectral
#print axioms Khachiyan.Spectral.det_rpow
#print axioms Khachiyan.Spectral.trace_sqrt
#print axioms Khachiyan.Spectral.det_sqrt
#print axioms Khachiyan.Spectral.rpow_posDef
#print axioms Khachiyan.Spectral.cfc_le_of_eigenvalues
#print axioms Khachiyan.Spectral.quadratic_mono
#print axioms Khachiyan.Spectral.scalar_lower_quadratic
#print axioms Khachiyan.Spectral.minIndex
#print axioms Khachiyan.Spectral.minEigenvalue
#print axioms Khachiyan.Spectral.minEigenvalue_le
#print axioms Khachiyan.Spectral.minEigenvalue_pos
#print axioms Khachiyan.Spectral.minEigenvalue_le_of_mem_spectrum
#print axioms Khachiyan.Spectral.minEigenvalue_mem_spectrum
#print axioms Khachiyan.Spectral.exists_unit_min_eigenvector
#print axioms Khachiyan.Spectral.minEigenvalue_smul_one_le
#print axioms Khachiyan.Spectral.le_inv_minEigenvalue_smul_sq
#print axioms Khachiyan.Spectral.minEigenvalue_rpow_smul_one_le
#print axioms Khachiyan.Spectral.minEigenvalue_rpow_le_quadratic
#print axioms Khachiyan.Spectral.minEigenvalue_two_mul_rpow_le_quadratic
#print axioms Khachiyan.Spectral.trace_rpow_eq_min_add_sum_erase
#print axioms Khachiyan.Spectral.det_eq_min_mul_prod_erase

-- M02: real matrix order adapter, inverse powers, and the exact integral formula.
#print axioms Khachiyan.MatrixPowers.MatC
#print axioms Khachiyan.MatrixPowers.complexify
#print axioms Khachiyan.MatrixPowers.complexify_apply
#print axioms Khachiyan.MatrixPowers.complexify_injective
#print axioms Khachiyan.MatrixPowers.continuous_complexify
#print axioms Khachiyan.MatrixPowers.complexify_isHermitian
#print axioms Khachiyan.MatrixPowers.complexify_posSemidef
#print axioms Khachiyan.MatrixPowers.complexify_quadratic
#print axioms Khachiyan.MatrixPowers.posSemidef_of_complexify
#print axioms Khachiyan.MatrixPowers.complexify_posSemidef_iff
#print axioms Khachiyan.MatrixPowers.complexify_le_iff
#print axioms Khachiyan.MatrixPowers.complexify_posDef
#print axioms Khachiyan.MatrixPowers.complexify_cfc
#print axioms Khachiyan.MatrixPowers.complexify_rpow
#print axioms Khachiyan.MatrixPowers.rpow_mono
#print axioms Khachiyan.MatrixPowers.sqrt_mono
#print axioms Khachiyan.MatrixPowers.posDef_of_le
#print axioms Khachiyan.MatrixPowers.inv_eq_rpow_neg_one
#print axioms Khachiyan.MatrixPowers.complexify_inv
#print axioms Khachiyan.MatrixPowers.inv_antitone
#print axioms Khachiyan.MatrixPowers.inv_rpow
#print axioms Khachiyan.MatrixPowers.rpow_antitone
#print axioms Khachiyan.MatrixPowers.rpow_sub_one_antitone
#print axioms Khachiyan.PowerIntegral.powerNormalization
#print axioms Khachiyan.PowerIntegral.scalar_kernel_one_eq
#print axioms Khachiyan.PowerIntegral.integrable_normalization_kernel
#print axioms Khachiyan.PowerIntegral.normalization_eq_inverse_integral
#print axioms Khachiyan.PowerIntegral.powerNormalization_pos
#print axioms Khachiyan.PowerIntegral.spectralCLM
#print axioms Khachiyan.PowerIntegral.spectralCLM_apply
#print axioms Khachiyan.PowerIntegral.spectralCLM_cfc
#print axioms Khachiyan.PowerIntegral.integrable_cfc_spectrum
#print axioms Khachiyan.PowerIntegral.integral_cfc_spectrum
#print axioms Khachiyan.PowerIntegral.integrable_cfc_kernel
#print axioms Khachiyan.PowerIntegral.rpow_eq_normalization_smul_integral_cfc
#print axioms Khachiyan.PowerIntegral.resolventKernel
#print axioms Khachiyan.PowerIntegral.cfc_kernel_eq_resolvent
#print axioms Khachiyan.PowerIntegral.integrable_resolvent_kernel
#print axioms Khachiyan.PowerIntegral.rpow_eq_integral

-- M03: self-adjoint path derivatives, uniform domination, and the trace formula.
#print axioms Khachiyan.TraceDerivative.line
#print axioms Khachiyan.TraceDerivative.kernelDeriv
#print axioms Khachiyan.TraceDerivative.hermitian_lower_of_norm_le
#print axioms Khachiyan.TraceDerivative.norm_inv_le
#print axioms Khachiyan.TraceDerivative.line_isHermitian
#print axioms Khachiyan.TraceDerivative.exists_uniform_lower
#print axioms Khachiyan.TraceDerivative.posDef_add_smul_one
#print axioms Khachiyan.TraceDerivative.norm_resolvent_le
#print axioms Khachiyan.TraceDerivative.hasDerivAt_line
#print axioms Khachiyan.TraceDerivative.hasDerivAt_matrix_inv
#print axioms Khachiyan.TraceDerivative.mul_resolvent
#print axioms Khachiyan.TraceDerivative.kernel_deriv_algebra
#print axioms Khachiyan.TraceDerivative.hasDerivAt_resolventKernel
#print axioms Khachiyan.TraceDerivative.derivBound
#print axioms Khachiyan.TraceDerivative.integrable_derivBound
#print axioms Khachiyan.TraceDerivative.norm_kernelDeriv_le
#print axioms Khachiyan.TraceDerivative.continuousOn_resolvent
#print axioms Khachiyan.TraceDerivative.continuousOn_kernelDeriv
#print axioms Khachiyan.TraceDerivative.hasDerivAt_rpow_integral
#print axioms Khachiyan.TraceDerivative.rpow_line_one
#print axioms Khachiyan.TraceDerivative.hasDerivAt_rpow_shift
#print axioms Khachiyan.TraceDerivative.normalization_smul_integral_kernel_one
#print axioms Khachiyan.TraceDerivative.traceCLM
#print axioms Khachiyan.TraceDerivative.traceCLM_apply
#print axioms Khachiyan.TraceDerivative.traceMulCLM
#print axioms Khachiyan.TraceDerivative.traceMulCLM_apply
#print axioms Khachiyan.TraceDerivative.trace_kernel_cyclic
#print axioms Khachiyan.TraceDerivative.trace_integral_kernel
#print axioms Khachiyan.TraceDerivative.hasDerivAt_trace_rpow

-- M04: the general rank-one inequality, equality case, and all supporting declarations.
#print axioms Khachiyan.RankOne.path
#print axioms Khachiyan.RankOne.posSemidef_of_inner_nonneg
#print axioms Khachiyan.RankOne.outer_le_one
#print axioms Khachiyan.RankOne.outer_image
#print axioms Khachiyan.RankOne.outer_image_le_sq
#print axioms Khachiyan.RankOne.trace_mul_outer
#print axioms Khachiyan.RankOne.inner_sandwich
#print axioms Khachiyan.RankOne.path_posDef
#print axioms Khachiyan.RankOne.scalar_sandwich
#print axioms Khachiyan.RankOne.sandwich_scaled_sq_rpow
#print axioms Khachiyan.RankOne.scalar_scale_min
#print axioms Khachiyan.RankOne.scaled_sq_posDef
#print axioms Khachiyan.RankOne.cfc_action_of_eigenvector
#print axioms Khachiyan.RankOne.rpow_action_of_eigenvector
#print axioms Khachiyan.RankOne.quadratic_rpow_eigen
#print axioms Khachiyan.RankOne.hasDerivAt_scalar_curve
#print axioms Khachiyan.RankOne.increment_le_of_derivative_le
#print axioms Khachiyan.RankOne.increment_eq_of_derivative_eq
#print axioms Khachiyan.RankOne.hasDerivAt_trace_path
#print axioms Khachiyan.RankOne.path_le_scaled_sq
#print axioms Khachiyan.RankOne.quadratic_path_lower
#print axioms Khachiyan.RankOne.trace_increment_lower_bound
#print axioms Khachiyan.RankOne.equalityBase
#print axioms Khachiyan.RankOne.equalityBase_posDef
#print axioms Khachiyan.RankOne.equality_path_eigen
#print axioms Khachiyan.RankOne.trace_increment_eq
#print axioms Khachiyan.RankOne.exists_equality_direction

-- G01S: support, separation, and general invertible affine images.
#print axioms Khachiyan.inner_matrix_action_symm
#print axioms Khachiyan.ellipsoid_support_le
#print axioms Khachiyan.ellipsoid_support_attained
#print axioms Khachiyan.mem_of_forall_strongDual_support
#print axioms Khachiyan.affineShape
#print axioms Khachiyan.affineShape_isSymm
#print axioms Khachiyan.affineShape_posDef
#print axioms Khachiyan.inner_transpose_action
#print axioms Khachiyan.affineShape_action_norm
#print axioms Khachiyan.linear_image_support_le
#print axioms Khachiyan.linear_image_support_attained
#print axioms Khachiyan.isCompact_linear_image_unitBall
#print axioms Khachiyan.convex_linear_image_unitBall
#print axioms Khachiyan.linear_image_unitBall_eq_affineShape
#print axioms Khachiyan.affine_image_unitBall_eq_ellipsoid

-- G02: the intermediate ellipsoid contained in a convex body containing two ellipsoids.
#print axioms Khachiyan.intermediateShape
#print axioms Khachiyan.intermediateShape_posDef
#print axioms Khachiyan.intermediateShape_isSymm
#print axioms Khachiyan.inner_outer_action
#print axioms Khachiyan.intermediateShape_norm_sq
#print axioms Khachiyan.intermediate_support_bound
#print axioms Khachiyan.intermediate_ellipsoid_subset

-- G05: the trace constraint derived from actual normalized maximality.
#print axioms Khachiyan.convexShape
#print axioms Khachiyan.convexShape_posDef
#print axioms Khachiyan.convexShape_action
#print axioms Khachiyan.convex_combination_ellipsoid_subset
#print axioms Khachiyan.detPath
#print axioms Khachiyan.detRemainder
#print axioms Khachiyan.convexShape_eq_one_add
#print axioms Khachiyan.detPath_eq_expansion
#print axioms Khachiyan.hasDerivAt_detPath_zero
#print axioms Khachiyan.detPath_le_one_of_isJohnNormalized
#print axioms Khachiyan.trace_le_of_isJohnNormalized

-- R01 infrastructure, the three M04 increments, their trace cancellation,
-- and the two final spectral constraints.
#print axioms Khachiyan.inv_action_mul_action
#print axioms Khachiyan.shortened_direction
#print axioms Khachiyan.r01Shape₁
#print axioms Khachiyan.r01Shape₂
#print axioms Khachiyan.r01Shape₁_posDef
#print axioms Khachiyan.r01Shape₂_posDef
#print axioms Khachiyan.r01Shape₁_trace_le
#print axioms Khachiyan.r01Shape₂_trace_le
#print axioms Khachiyan.shortened_outer_le
#print axioms Khachiyan.shortened_shape_le
#print axioms Khachiyan.r01_first_increment
#print axioms Khachiyan.sqrt_smul_sq
#print axioms Khachiyan.r01_m1_le_scaled_sq
#print axioms Khachiyan.trace_rpow_sqrt_half
#print axioms Khachiyan.r01_m2_le_original
#print axioms Khachiyan.r01_second_increment
#print axioms Khachiyan.r01_third_increment
#print axioms Khachiyan.r01_second_third_combined
#print axioms Khachiyan.r01_constraint_one
#print axioms Khachiyan.r01_constraint_two

-- R02: logarithmic and AM--GM determinant estimates.
#print axioms Khachiyan.r02_log_det_bound
#print axioms Khachiyan.r02_log_bound_one
#print axioms Khachiyan.r02_log_bound_two
#print axioms Khachiyan.r02_exp_bounds
#print axioms Khachiyan.r02_amgm_det_bound
#print axioms Khachiyan.r02_amgm_bound_one
#print axioms Khachiyan.r02_amgm_bound_two

-- N01: the dimension-independent normalized determinant bound.
#print axioms Khachiyan.n01_normalized_det_bound

-- G01V: actual Lebesgue volume and determinant bridge.
#print axioms Khachiyan.unitBall_volume_pos
#print axioms Khachiyan.matrix_action_det_eq
#print axioms Khachiyan.volume_translate
#print axioms Khachiyan.volume_linear_image
#print axioms Khachiyan.volume_ellipsoid_eq
#print axioms Khachiyan.volume_ellipsoid_eq_det
#print axioms Khachiyan.volume_ellipsoid_pos
#print axioms Khachiyan.volume_ellipsoid_ne_zero

-- G03E: positive feasible witness and direct-method volume foundations.
#print axioms Khachiyan.exists_positive_ball_subset
#print axioms Khachiyan.exists_positive_feasible_ellipsoid
#print axioms Khachiyan.feasible_volume_pos
#print axioms Khachiyan.feasible_volume_lt_top
#print axioms Khachiyan.feasible_center_mem
#print axioms Khachiyan.feasible_shape_opNorm_le
#print axioms Khachiyan.feasible_parameter_bounds
#print axioms Khachiyan.feasiblePSDParameters
#print axioms Khachiyan.isClosed_posSemidef_set
#print axioms Khachiyan.isClosed_feasiblePSDParameters
#print axioms Khachiyan.isBounded_feasiblePSDParameters
#print axioms Khachiyan.isCompact_feasiblePSDParameters
#print axioms Khachiyan.exists_max_det_feasiblePSDParameters
#print axioms Khachiyan.exists_isMaxDet
#print axioms Khachiyan.midpoint_feasible_of_feasible
#print axioms Khachiyan.maxDet_midpoint_le_of_isMaxDet
#print axioms Khachiyan.maxDet_same_shape_of_isMaxDet
#print axioms Khachiyan.strict_scalar_midpoint_prod
#print axioms Khachiyan.strict_affine_det_of_eigenvalues

-- G03U: strict determinant midpoint inequality and uniqueness.
#print axioms Khachiyan.relativeShape
#print axioms Khachiyan.sqrt_posDef
#print axioms Khachiyan.relativeShape_posDef
#print axioms Khachiyan.sqrt_mul_self
#print axioms Khachiyan.relativeShape_reconstruct
#print axioms Khachiyan.relativeShape_eq_one_iff
#print axioms Khachiyan.relativeShape_exists_eigenvalue_ne_one
#print axioms Khachiyan.relativeShape_det
#print axioms Khachiyan.midpoint_det_factor
#print axioms Khachiyan.det_eq_of_isMaxDet
#print axioms Khachiyan.strict_midpoint_det
#print axioms Khachiyan.maxDet_shape_unique
#print axioms Khachiyan.affineShape_det
#print axioms Khachiyan.ellipsoid_affine_preimage
#print axioms Khachiyan.image_subset_image
#print axioms Khachiyan.maxDet_center_unique_same_shape
#print axioms Khachiyan.isMaxDet_unique
#print axioms Khachiyan.existsUnique_isMaxDet

-- G04: affine normalization, center exclusion, maximality, halfspaces, and actual volume.
#print axioms Khachiyan.normalizePoint
#print axioms Khachiyan.denormalizePoint
#print axioms Khachiyan.normalize_denormalize
#print axioms Khachiyan.denormalize_normalize
#print axioms Khachiyan.normalizationHomeomorph
#print axioms Khachiyan.normalize_ellipsoid_self
#print axioms Khachiyan.mem_interior_ellipsoid_iff
#print axioms Khachiyan.center_exclusion_iff
#print axioms Khachiyan.mem_interior_ellipsoid_iff_norm
#print axioms Khachiyan.center_mem_interior_ellipsoid
#print axioms Khachiyan.IsMaxDet.center_mem_interior
#print axioms Khachiyan.ellipsoid_subset_centralHalfspace_zero_iff
#print axioms Khachiyan.norm_inv_center_ge_one_of_halfspace
#print axioms Khachiyan.inverse_square_normal_separates
#print axioms Khachiyan.center_exclusion_iff_exists_halfspace
#print axioms Khachiyan.normalizedBody
#print axioms Khachiyan.normalizedBody_eq_preimage
#print axioms Khachiyan.denormalize_normalizedBody
#print axioms Khachiyan.normalizedBody_convex
#print axioms Khachiyan.IsConvexBody.normalizedBody
#print axioms Khachiyan.denormalize_ellipsoid
#print axioms Khachiyan.normalize_ellipsoid
#print axioms Khachiyan.denormalized_shape_posDef
#print axioms Khachiyan.normalized_shape_posDef
#print axioms Khachiyan.denormalized_shape_det
#print axioms Khachiyan.normalized_shape_det
#print axioms Khachiyan.IsFeasible.normalize
#print axioms Khachiyan.IsFeasible.denormalize
#print axioms Khachiyan.IsMaxDet.isJohnNormalized
#print axioms Khachiyan.IsMaxDet.maxEllipsoidVolume_eq
#print axioms Khachiyan.IsMaxDet.maxEllipsoidVolume_eq_det
#print axioms Khachiyan.IsConvexBody.exists_maxEllipsoidVolume
#print axioms Khachiyan.IsConvexBody.maxEllipsoidVolume_pos
#print axioms Khachiyan.volume_denormalizePoint
#print axioms Khachiyan.volume_normalizePoint
#print axioms Khachiyan.volume_normalize_ratio
#print axioms Khachiyan.volume_ellipsoid_div_unitBall
#print axioms Khachiyan.volume_normalized_ellipsoid_ratio
#print axioms Khachiyan.IsMaxDet.normalized_maxEllipsoidVolume
#print axioms Khachiyan.IsMaxDet.maxEllipsoidVolume_normalize
#print axioms Khachiyan.denormalize_centralHalfspace
#print axioms Khachiyan.normalize_centralHalfspace
#print axioms Khachiyan.normalized_normal_ne_zero
#print axioms Khachiyan.normalizedBody_cut
#print axioms Khachiyan.normalized_cut_det_bound
#print axioms Khachiyan.isClosed_centralHalfspace
#print axioms Khachiyan.convex_centralHalfspace
#print axioms Khachiyan.interior_cut_nonempty
#print axioms Khachiyan.IsConvexBody.centralCut
#print axioms Khachiyan.maxEllipsoidVolume_normalizedBody
#print axioms Khachiyan.maxEllipsoidVolume_normalize_ratio
#print axioms Khachiyan.volume_ellipsoid_div_maxEllipsoidVolume
#print axioms Khachiyan.IsMaxDet.maxEllipsoidVolume_toReal_pos
#print axioms Khachiyan.volume_ellipsoid_real_ratio

-- T01: actual central-cut volume, canonical maximizing ellipsoid, and statement bridges.
#print axioms Khachiyan.central_cut_candidate_det_le
#print axioms Khachiyan.central_cut_candidate_volume_le
#print axioms Khachiyan.center_cut_volume_le
#print axioms Khachiyan.johnParameters
#print axioms Khachiyan.johnCenter
#print axioms Khachiyan.johnShape
#print axioms Khachiyan.johnEllipsoid
#print axioms Khachiyan.john_isMaxDet
#print axioms Khachiyan.johnCenter_eq_of_isMaxDet
#print axioms Khachiyan.johnShape_eq_of_isMaxDet
#print axioms Khachiyan.johnShape_posDef
#print axioms Khachiyan.johnEllipsoid_subset
#print axioms Khachiyan.volume_johnEllipsoid
#print axioms Khachiyan.johnCenter_mem_interior
#print axioms Khachiyan.isMaxDet_iff_attains_volume
#print axioms Khachiyan.john_eq_of_volume_maximal
#print axioms Khachiyan.john_center_cut_isConvexBody
#print axioms Khachiyan.john_center_cut_volume_le
#print axioms Khachiyan.t01
#print axioms Khachiyan.john_center_cut_volume_le_real
#print axioms Khachiyan.john_center_cut_volume_ratio_le

-- ContactCertificate: completed public declarations.
#print axioms Khachiyan.det_le_one_of_trace_le
#print axioms Khachiyan.contact_weights_sum
#print axioms Khachiyan.contact_trace_bound
#print axioms Khachiyan.isJohnNormalized_of_contacts

-- ConeGeometry: completed public declarations.
#print axioms Khachiyan.Cone.join
#print axioms Khachiyan.Cone.tail
#print axioms Khachiyan.Cone.join_zero
#print axioms Khachiyan.Cone.join_succ
#print axioms Khachiyan.Cone.tail_apply
#print axioms Khachiyan.Cone.tail_join
#print axioms Khachiyan.Cone.norm_sq_split
#print axioms Khachiyan.Cone.norm_join_sq
#print axioms Khachiyan.Cone.inner_join
#print axioms Khachiyan.Cone.tail_add
#print axioms Khachiyan.Cone.tail_smul
#print axioms Khachiyan.Cone.continuous_tail
#print axioms Khachiyan.Cone.axial_support_le
#print axioms Khachiyan.Cone.slope
#print axioms Khachiyan.Cone.body
#print axioms Khachiyan.Cone.slope_nonneg
#print axioms Khachiyan.Cone.slope_sq
#print axioms Khachiyan.Cone.slope_pos
#print axioms Khachiyan.Cone.unitBall_subset_body
#print axioms Khachiyan.Cone.isClosed_body
#print axioms Khachiyan.Cone.convex_body
#print axioms Khachiyan.Cone.body_coordinate_bounds
#print axioms Khachiyan.Cone.isBounded_body
#print axioms Khachiyan.Cone.isConvexBody_body
#print axioms Khachiyan.Cone.inner_join_left
#print axioms Khachiyan.Cone.ContactIndex
#print axioms Khachiyan.Cone.sideNormal
#print axioms Khachiyan.Cone.contactNormal
#print axioms Khachiyan.Cone.baseWeight
#print axioms Khachiyan.Cone.sideWeight
#print axioms Khachiyan.Cone.contactWeight
#print axioms Khachiyan.Cone.side_scales_sq
#print axioms Khachiyan.Cone.side_scale_eq_sqrt
#print axioms Khachiyan.Cone.sideNormal_norm
#print axioms Khachiyan.Cone.contactNormal_norm
#print axioms Khachiyan.Cone.contactWeight_pos
#print axioms Khachiyan.Cone.sideNormal_support
#print axioms Khachiyan.Cone.contactNormal_support
#print axioms Khachiyan.Cone.contact_first_moment
#print axioms Khachiyan.Cone.contact_second_moment
#print axioms Khachiyan.Cone.isJohnNormalized_body
#print axioms Khachiyan.Cone.johnCenter_body
#print axioms Khachiyan.Cone.maxEllipsoidVolume_body
#print axioms Khachiyan.Cone.cutNormal
#print axioms Khachiyan.Cone.cut
#print axioms Khachiyan.Cone.cutNormal_ne_zero
#print axioms Khachiyan.Cone.centralHalfspace_cutNormal
#print axioms Khachiyan.Cone.cut_eq_canonical_cut
#print axioms Khachiyan.Cone.isConvexBody_cut
#print axioms Khachiyan.Cone.transverseScale
#print axioms Khachiyan.Cone.candidateCenter
#print axioms Khachiyan.Cone.candidateShape
#print axioms Khachiyan.Cone.transverseScale_pos
#print axioms Khachiyan.Cone.transverseScale_sq
#print axioms Khachiyan.Cone.slope_scale_sq
#print axioms Khachiyan.Cone.candidateShape_posDef
#print axioms Khachiyan.Cone.candidateShape_action
#print axioms Khachiyan.Cone.candidate_subset_cut
#print axioms Khachiyan.Cone.candidate_feasible
#print axioms Khachiyan.Cone.candidateShape_det

-- ConeLimit: completed public declarations.
#print axioms Khachiyan.Cone.lowerBound
#print axioms Khachiyan.Cone.volumeRatio
#print axioms Khachiyan.Cone.candidateShape_det_eq_lowerBound
#print axioms Khachiyan.Cone.candidate_volume_ratio
#print axioms Khachiyan.Cone.lowerBound_le_volumeRatio
#print axioms Khachiyan.Cone.volumeRatio_pos
#print axioms Khachiyan.Cone.volumeRatio_le_rStar
#print axioms Khachiyan.Cone.tendsto_lowerBound
#print axioms Khachiyan.Cone.tendsto_volumeRatio
#print axioms Khachiyan.Cone.exists_volumeRatio_gt

-- Sharpness: completed public declarations.
#print axioms Khachiyan.sharp_constant

-- M05: diminishing increments and the positive-semidefinite boundary.
#print axioms Khachiyan.Diminishing.trace_mul_nonneg
#print axioms Khachiyan.Diminishing.trace_mul_mono
#print axioms Khachiyan.Diminishing.hasDerivAt_trace_line
#print axioms Khachiyan.Diminishing.trace_increment_antitone
#print axioms Khachiyan.Diminishing.continuousOn_rpow_nonneg
#print axioms Khachiyan.Diminishing.trace_regularized_tendsto
#print axioms Khachiyan.Diminishing.regularized_posDef
#print axioms Khachiyan.Diminishing.trace_strong_subadditivity

-- T03: strict determinant and geometric volume bounds in every finite positive dimension.
#print axioms Khachiyan.sum_log_lt_of_sum_le
#print axioms Khachiyan.det_lt_rStar_at_half
#print axioms Khachiyan.normalized_det_lt_rStar
#print axioms Khachiyan.normalized_cut_det_lt

-- Nonattainment: completed public declarations.
#print axioms Khachiyan.central_cut_candidate_volume_ratio_lt
#print axioms Khachiyan.center_cut_volume_lt
#print axioms Khachiyan.t03
#print axioms Khachiyan.john_center_cut_volume_ratio_lt

-- OneDimensional: completed public declarations.
#print axioms Khachiyan.OneDimensional.point
#print axioms Khachiyan.OneDimensional.point_apply
#print axioms Khachiyan.OneDimensional.point_coordinate
#print axioms Khachiyan.OneDimensional.norm_point
#print axioms Khachiyan.OneDimensional.norm_eq_abs_coordinate
#print axioms Khachiyan.OneDimensional.inner_eq_coordinate
#print axioms Khachiyan.OneDimensional.lineHomeomorph
#print axioms Khachiyan.OneDimensional.scalar_shape_action
#print axioms Khachiyan.OneDimensional.mem_scalar_ellipsoid
#print axioms Khachiyan.OneDimensional.exists_interval
#print axioms Khachiyan.OneDimensional.exists_eq_scalar_ellipsoid
#print axioms Khachiyan.OneDimensional.scalar_ellipsoid_isMaxDet
#print axioms Khachiyan.OneDimensional.johnEllipsoid_eq
#print axioms Khachiyan.OneDimensional.maxEllipsoidVolume_eq_volume
#print axioms Khachiyan.OneDimensional.scalar_cut_of_pos
#print axioms Khachiyan.OneDimensional.scalar_cut_of_neg
#print axioms Khachiyan.OneDimensional.coordinate_ne_zero
#print axioms Khachiyan.OneDimensional.scalar_cut_eq_half_ellipsoid
#print axioms Khachiyan.OneDimensional.scalar_cut_volume_eq_half
#print axioms Khachiyan.OneDimensional.center_cut_volume_eq_half
#print axioms Khachiyan.OneDimensional.center_cut_volume_ratio_eq_half
#print axioms Khachiyan.OneDimensional.sharp_half

-- T04: logarithmic deficit, smallest semiaxis, and actual-volume near equality.
#print axioms Khachiyan.log_rStar
#print axioms Khachiyan.t04_log_det_tangents
#print axioms Khachiyan.t04_log_deficit_bounds
#print axioms Khachiyan.t04_log_deficit
#print axioms Khachiyan.t04
#print axioms Khachiyan.t04_of_central_cut
#print axioms Khachiyan.t04_of_john_center_cut

-- T05: arbitrary and explicitly generated exact central-cut sequences.
#print axioms Khachiyan.centralCutSequence_isConvexBody
#print axioms Khachiyan.centralCutSequence_volume_le
#print axioms Khachiyan.centralCutSequence_volume_bounds
#print axioms Khachiyan.centralCutSequence_volume_le_real
#print axioms Khachiyan.centralCutSequence_log_ratio_ge
#print axioms Khachiyan.t05
#print axioms Khachiyan.centralCuts
#print axioms Khachiyan.t05_centralCuts

-- D01 / A01 foundation: independent rank-one determinant and logarithm identities.
#print axioms Khachiyan.Resolvent.det_add_smul_outer
#print axioms Khachiyan.Resolvent.one_add_mul_inv_quadratic_pos
#print axioms Khachiyan.Resolvent.log_det_add_smul_outer

-- A01 / M04R: complete independent scalar and matrix resolvent proof.
#print axioms Khachiyan.ResolventScalar.logDiff
#print axioms Khachiyan.ResolventScalar.log_sub_log_le
#print axioms Khachiyan.ResolventScalar.abs_log_sub_log_le
#print axioms Khachiyan.ResolventScalar.abs_logDiff_le
#print axioms Khachiyan.ResolventScalar.powerKernel
#print axioms Khachiyan.ResolventScalar.powerKernel_eq
#print axioms Khachiyan.ResolventScalar.integrable_powerKernel
#print axioms Khachiyan.ResolventScalar.power_eq_integral_powerKernel
#print axioms Khachiyan.ResolventScalar.integrable_weighted_inv
#print axioms Khachiyan.ResolventScalar.integrable_weighted_logDiff
#print axioms Khachiyan.ResolventScalar.boundary_zero
#print axioms Khachiyan.ResolventScalar.abs_logDiff_le_div
#print axioms Khachiyan.ResolventScalar.boundary_infty
#print axioms Khachiyan.ResolventScalar.hasDerivAt_logDiff
#print axioms Khachiyan.ResolventScalar.weighted_logDiff_derivative
#print axioms Khachiyan.ResolventScalar.integrable_weighted_logDiff_derivative
#print axioms Khachiyan.ResolventScalar.integral_logDiff
#print axioms Khachiyan.ResolventScalar.rpow_sub_eq_integral_logDiff
#print axioms Khachiyan.ResolventScalar.logDiff_add
#print axioms Khachiyan.ResolventScalar.integrable_weighted_log_one_add_div
#print axioms Khachiyan.ResolventScalar.rpow_add_sub_eq_integral_log
#print axioms Khachiyan.Resolvent.posDef_add_smul_one
#print axioms Khachiyan.Resolvent.inner_action_left
#print axioms Khachiyan.Resolvent.inverse_scaled_sq_quadratic
#print axioms Khachiyan.Resolvent.cfc_shift
#print axioms Khachiyan.Resolvent.log_det_shift_eq_sum
#print axioms Khachiyan.Resolvent.logDetDiff
#print axioms Khachiyan.Resolvent.logDetDiff_eq_sum
#print axioms Khachiyan.Resolvent.integrable_weighted_logDetDiff
#print axioms Khachiyan.Resolvent.trace_rpow_sub_eq_integral_logDetDiff
#print axioms Khachiyan.Resolvent.trace_inv_shift_eq_sum
#print axioms Khachiyan.Resolvent.hasDerivAt_logDetDiff
#print axioms Khachiyan.Resolvent.logDetDiff_boundary_zero
#print axioms Khachiyan.Resolvent.logDetDiff_boundary_infty
#print axioms Khachiyan.Resolvent.posDef_add_smul_outer
#print axioms Khachiyan.Resolvent.logDetDiff_rank_one
#print axioms Khachiyan.Resolvent.integrable_rank_one_log_kernel
#print axioms Khachiyan.Resolvent.trace_rpow_rank_one_eq_integral_log
#print axioms Khachiyan.Resolvent.resolvent_quadratic_lower_bound
#print axioms Khachiyan.Resolvent.trace_increment_lower_bound
