/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptVCVio.Rust.HaxRustM

/-!
# Tests of `liftRustM`

A checked byte addition in `RustM` that panics on overflow, lifted into `RustOracleComp`: a
value, an overflow, a bind of two calls, the monad lift, and the square with `liftSpec` at
`unifSpec`.
-/

set_option autoImplicit false

open CatCrypt.VCVio.Rust

/-- Addition of two bytes that fails with a panic on overflow. -/
def checkedAddU8 (x y : Nat) : RustM Nat :=
  if x + y < 256 then .ok (x + y) else .fail .panic

example : (liftRustM (checkedAddU8 1 2) : RustOracleComp unifSpec Nat) = RustOracleComp.ok 3 := by
  simp [checkedAddU8]

example : (liftRustM (checkedAddU8 200 100) : RustOracleComp unifSpec Nat) =
    RustOracleComp.fail .panic := by
  simp [checkedAddU8, errorOfHax]

example : (liftRustM (checkedAddU8 1 2 >>= fun s => checkedAddU8 s 250) :
    RustOracleComp unifSpec Nat).run.run = pure (some (.ok 253)) := by
  simp [checkedAddU8]

example (x y z : Nat) : (liftRustM (checkedAddU8 x y >>= fun s => checkedAddU8 s z) :
    RustOracleComp unifSpec Nat) =
      liftRustM (checkedAddU8 x y) >>= fun s => liftRustM (checkedAddU8 s z) :=
  liftRustM_bind _ _

example (x y : Nat) : (liftM (checkedAddU8 x y) : RustOracleComp unifSpec Nat) =
    liftRustM (checkedAddU8 x y) := rfl

example {τ : Type} (superSpec : OracleSpec τ) [unifSpec ⊂ₒ superSpec] (x y z : Nat) :
    RustOracleComp.liftSpec superSpec
        (liftRustM (checkedAddU8 x y) >>= fun s => liftRustM (checkedAddU8 s z) :
          RustOracleComp unifSpec Nat) =
      liftRustM (checkedAddU8 x y) >>= fun s => liftRustM (checkedAddU8 s z) := by
  simp [RustOracleComp.liftSpec_liftRustM_bind]


