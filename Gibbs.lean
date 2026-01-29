import Mathlib

/-! # Gibbs

Mean-field theory meets multiparty session types.

This library formalizes the relationship between:
- Multi-party session types (MPST): Global protocol -> local endpoint views
- Mean-field theory: Many local agents -> global aggregate behavior

Both frameworks perform "causal erasure" - quotienting out extensional detail
while preserving intensional structure. See `work/global_local.md` for the
theoretical foundation.

## Main Modules

- `Gibbs.Core`: Core types (SessionId, Role, Endpoint, Edge)
- `Gibbs.LocalType`: Local session types with role-directed actions
- `Gibbs.GlobalType`: Global choreographic types
- `Gibbs.Projection`: Global -> local type projection
- `Gibbs.MeanField`: Population CTMC and fluid limit semantics
-/

-- Submodules will be imported here as they are developed
-- import Gibbs.Core
-- import Gibbs.LocalType
