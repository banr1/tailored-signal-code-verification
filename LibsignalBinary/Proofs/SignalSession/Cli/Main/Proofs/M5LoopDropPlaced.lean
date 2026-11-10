/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5BufDeallocPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable M5 Post-Commit Entry Drop Loop (`M+0xa90 .. M+0xabc`, Block `617`)

Verifies `m5_entry_drop_loop_placed` (`M+0xa90 .. M+0xabc`) on Block `617` under
`[LibsignalPlacement]` via `m5_drop_loop_body_0xa84_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops.LoopDrop

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Drop a non-empty array of `(String, Vec<u8>)` entries starting at `M+0xa90` (`x21 = base + 32`,
`x20 = es.length`), looping via `M+0xa84 .. M+0xa8c` until `x20 = 0` branches to `M+0xabc`. -/
theorem m5_entry_drop_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {base : BitVec 64}
    (es : List (List (BitVec 8) × List (BitVec 8)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hne : es ≠ [])
    (hlen : es.length * 48 < 2 ^ 63)
    (hs : InMainPlaced CodeOk s0 s 0xa90)
    (hx21 : s.readReg64 (.gpr 21#5) = base + 32#64)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 es.length)
    (hP : P ⊢ arrayAt (dirEntryAt A) 48 base es ∗ A.pool ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm 0xabc →
      sm.fs = s.fs →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (memRegion base (es.length * 48) ∗ A.pool ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  refine SepWPp.weaken_pre (Entails.trans hP (Entails.of_eq (by rw [← hs.sp]))) ?_
  refine m5_drop_loop_body_0xa84_placed hA hstk (by omega) hne hlen hs hx20 hx21 ?_
  intro sm hsm hkeeps hfs htr
  rw [hs.sp]
  exact hnext sm hsm hfs htr
    (hkeeps 19#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 22#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 23#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 24#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 25#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 26#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 27#5 (by decide) (by decide) (by decide) (by decide))

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
