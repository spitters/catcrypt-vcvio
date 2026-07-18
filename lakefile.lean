import Lake
open Lake DSL

package catcryptVcvio where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib CatCryptVCVio where
  -- Module root `CatCryptVCVio.*`; declared namespaces stay `CatCrypt.Crypto.VCVioBridge`.
  -- The VCVio interoperability bridge, split out of CatCryptCore so core does not
  -- carry a VCVio dependency. Downstream `CatCrypt.Crypto.Bridges.VCVioBridge` shims
  -- re-export this package.
  globs := #[.andSubmodules `CatCryptVCVio]

require catcryptCore from "../CatCrypt-core"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io" @ "v4.30.0"

-- mathlib last so its pinned transitive deps win, matching the shared olean cache.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"
