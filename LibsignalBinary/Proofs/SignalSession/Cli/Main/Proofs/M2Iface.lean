/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops

/-!
# Collect / Dispatch Boundary Invariant for `main` M2 (`AtM2Dispatch`)

Defines the intermediate machine and heap invariant `AtM2Dispatch` between `M2Collect`
(`M+0xc0 → M+0x2f4 / M+0x1b0`) and `M2Dispatch` (`M+0x2f4 / M+0x1b0 → M+0x560 / M+0xb24`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Boundary invariant between `M2Collect` and `M2Dispatch`: `Vec<&str>` holds all
`n = i.argv.length ≥ 1` slices `(p_k, |bs_k|)` in `argsBuf A vcap vptr ps` (`vcap ≠ 0`,
`x20 = vptr`, `x23 = vcap`, `x21 = n`), stack locals are `locals fsp []`, `args` is in
`(x19 = buf, x24 = n)`, and `pc` is `M+0x2f4` if `n = 2` or `M+0x1b0` if `n ≠ 2`. -/
structure AtM2Dispatch (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (n : Nat) (buf vcap vptr : BitVec 64) : Prop where
  base : InMain img ext s0 s (if n = 2 then 0x2f4 else 0x1b0)
  spAligned : s0.spAligned = true
  x19 : s.readReg64 (.gpr 19#5) = buf
  x20 : s.readReg64 (.gpr 20#5) = vptr
  x21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n
  x23 : s.readReg64 (.gpr 23#5) = vcap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  vcap_ne : vcap ≠ 0#64
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

end CryptoVerification.SignalSession.Cli.MainHops
