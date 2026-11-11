/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptVCVio.Rust.Signature

/-!
# Tests of the Rust effect signature

Each example runs a small Rust program with oracle access through one of the two handlers of
`CatCryptVCVio.Rust.Signature`: a query followed by a panic and an oracle computation followed
by divergence through the interpretation into `RustOracleComp spec`, and a panic after an
oracle computation and a total oracle computation through the failure-only interpretation.
-/

namespace CatCrypt.VCVio.Rust

open PFunctor RustProg

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

example (e : Error) (t : ι) :
    (interp (query t >>= fun _ => (fail e : RustProg spec Unit))).run.run =
      OracleComp.ofFreeM (FreeM.lift (P := spec.toPFunctor) t) >>= fun _ =>
        pure (some (Except.error e)) := by
  simp only [run_run_interp_query_bind, run_run_interp_fail]

example (oa : OracleComp spec α) :
    (interp (liftOracleComp oa >>= fun _ => (div : RustProg spec α))).run.run =
      oa >>= fun _ => pure none := by
  simp only [run_run_interp_liftOracleComp_bind, run_run_interp_div]

example (oa : OracleComp spec α) (e : Error) :
    (interpFail (liftOracleComp oa >>= fun _ => (fail e : RustProg spec α))).run =
      oa >>= fun _ => pure none := by
  rw [run_interpFail]
  simp [Except.toOption]

example (oa : OracleComp spec α) :
    (interpFail (liftOracleComp oa)).run = some <$> oa := by
  rw [run_interpFail]
  simp [Except.toOption]

end CatCrypt.VCVio.Rust
