import Lake
open Lake DSL

package catcryptVcvio where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

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
