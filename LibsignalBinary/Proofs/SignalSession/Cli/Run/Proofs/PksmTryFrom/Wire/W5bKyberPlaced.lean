/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyber
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKeyPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedB
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Kyber Exit States and Segment `+0x684 → +0x830`

Defines `[LibsignalPlacement]` `KyberExitA1cStatePlaced`, `KyberExitA24StatePlaced`,
`KyberExitA74StatePlaced`, and `KyberExitA80StatePlaced`, and re-exports
`post_seg2_1b4_to_360_placed_wp` (`+0x684 → +0x830`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- `[LibsignalPlacement]` Error-tail entry at `+0xa1c` (`2588`). -/
def KyberExitA1cStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueStatePlaced s0 sp' sf ∧
  0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64 ∧
  sf.readReg64 .x0 = kyberPtr ∧ sf.readReg64 .x1 = kyberCap ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- `[LibsignalPlacement]` Error-tail entry at `+0xa24` (`2596`). -/
def KyberExitA24StatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueStatePlaced s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- `[LibsignalPlacement]` Allocation-failure panic entry at `+0xa74` (`2676`). -/
def KyberExitA74StatePlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (sf : State) : Prop :=
  sf.sp = sp' ∧ sf.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
  allocFailedIn s0 sf ∧ s0.trace <+: sf.trace

/-- `[LibsignalPlacement]` Allocation-failure panic entry at `+0xa80` (`2688`). -/
def KyberExitA80StatePlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (sf : State) : Prop :=
  sf.sp = sp' ∧ sf.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
  allocFailedIn s0 sf ∧ s0.trace <+: sf.trace

abbrev post_seg2_1b4_to_360_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.post_seg2_1b4_to_360_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
