/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` `base_key` Deserialization Re-Exports

Re-exports `BaseKeyOkStatePlaced`, `DeserErrTailStatePlaced`, `DeserErrTailStateEPlaced`,
`deallocSlot` helpers, and `post_seg1b_0ac_to_1b4_placed_wp` (`+0x57c → +0x684`) on
`preKeyPlacedProg H`.
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

theorem deserErrTailStateEPlaced_nonvacuous [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (hst : PostEpilogueStatePlaced s0 sp' s0) :
    ∃ sf : State,
      DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb
        .noKeyTypeIdentifier sf := by
  rcases hst with ⟨hsp0, hal, hcl, _⟩
  refine ⟨(((((((((((s0.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 1#64).writeReg64 .x23 ikCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret).writeReg64 .x9 (speWord 7), ?_⟩
  refine ⟨⟨⟨by simp [hsp0, arm64_norm], by simpa [State.spAligned, arm64_norm] using hal,
      hcl, by simp [arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩, ?_⟩
  simp [speWordsOf, speWord, arm64_norm]

abbrev post_seg1b_0ac_to_1b4_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.post_seg1b_0ac_to_1b4_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
