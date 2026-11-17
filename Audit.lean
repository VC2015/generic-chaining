import GenericChaining
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Check the transitive axioms of each mathematical entry point of this release.
A dependency on an admission or an additional axiom makes the command fail. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``GenericChaining.capacity_pos, ``GenericChaining.exists_surjection_fin,
    ``GenericChaining.gamma, ``GenericChaining.gamma1,
    ``GenericChaining.gamma2, ``GenericChaining.cost_pullback,
    ``GenericChaining.gamma_pullback, ``GenericChaining.gamma_eq_finset,
    ``GenericChaining.gamma1_discrete_le_cutoff, ``GenericChaining.gamma1_discrete_le_log2,
    ``GenericChaining.gamma1_discrete_singleton, ``GenericChaining.exists_common_representatives,
    ``GenericChaining.HasMixedTail.level_bound, ``GenericChaining.HasMixedTail.dyadic_edge_bound,
    ``GenericChaining.ae_eq_of_zero_contrast, ``GenericChaining.maximum_ae_eq_of_zero_contrasts]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
