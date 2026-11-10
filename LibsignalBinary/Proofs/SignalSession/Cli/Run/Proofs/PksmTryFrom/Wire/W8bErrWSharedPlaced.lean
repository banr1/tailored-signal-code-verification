/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Shared `+0x504` Error-Epilogue Closing

Re-exports stack-frame reassembly helpers from `W8bErrWShared` and proves
`w8b_errTail_close_placed` (`+0x504 → ret`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Shared `+0x504` (`1284`) error-epilogue closing under `[LibsignalPlacement]`:
absorbs any residual heap garbage `R` into `anyHeap`, steps `epilogue_504_err_placed_w_wpE`,
and closes `(pksmTryFromSpecPlaced A).post` via `w8b_errPost_placed`. -/
theorem w8b_errTail_close_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost}
    {s0 s : State} {R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (pksmErrE A fn x.ret e ∗ R ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧
        (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf))
      (tryFromQp s0) := by
  refine SepWPp.mono_post
    (Wire.SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A fn x.ret e ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (by
        refine Entails.trans
          (Q := stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
            memRegion (s0.sp - 608#64) 296 ∗
            memRegion (s0.sp - 608#64 + 296#64) 152 ∗
            memRegion (s0.sp - 608#64 + 448#64) 64 ∗
            preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
            (pksmErrE A fn x.ret e ∗ R) ∗
            (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
          (by apply entails_of_eq; ac_rfl) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (entails_anyHeap R))))))))
      (epilogue_504_err_placed_w_wpE (x := x) fn e hst hpc hrun)) ?_
  intro sf Pf _ _ hq
  exact w8b_errPost_placed hparse hq

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
