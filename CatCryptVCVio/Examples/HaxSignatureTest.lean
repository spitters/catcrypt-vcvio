/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.HaxSignature

/-!
# Tests of hax-lean's `RustM` as programs of the Rust-effect signature

Each example reads a `RustM` computation as a Rust program with `toRustProg` and interprets it:
a value followed by a continuation and a panic through the interpretation into
`RustOracleComp spec`, divergence through the failure-only interpretation, and a bind through
the interpretation into `RustM`, which returns the computation unchanged.
-/

set_option autoImplicit false

namespace CatCrypt.VCVio.Rust

open RustProg

variable {ι : Type} {spec : OracleSpec ι}

example (v : Nat) (f : Nat → RustM Nat) :
    RustProg.interp (toRustProg (RustM.ok v >>= f) : RustProg spec Nat) = liftRustM (f v) := by
  simp only [toRustProg_bind, interp_bind, interp_toRustProg, liftRustM_ok]
  rfl

example (f : Nat → RustM Nat) :
    (RustProg.interp (toRustProg (RustM.fail .panic >>= f) : RustProg spec Nat)).run.run =
      pure (some (Except.error Error.panic)) := by
  simp only [interp_toRustProg, run_run_liftRustM]
  rfl

example :
    RustProg.interpFail (toRustProg (RustM.div : RustM Nat) : RustProg spec Nat) = failure := by
  rw [interpFail_toRustProg]
  rfl

example (spec₀ : OracleSpec PEmpty) (f : Nat → RustM Nat) (x : RustM Nat) :
    interpHax (toRustProg (x >>= f) : RustProg spec₀ Nat) = x >>= f := by
  simp only [interpHax_toRustProg]

end CatCrypt.VCVio.Rust
