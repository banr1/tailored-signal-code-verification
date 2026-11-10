/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.RegChain

/-!
# Relocatable S3 Commit Sub-Segment on Block `433`

Proves the relocatable `[LibsignalPlacement]` DH ratchet commit sub-segment (`+0x8ac → +0x3e4`,
`CliS3CommitSeamPlaced`) for `try_decrypt_with_state::<Coins>` (block `433`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt?
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding drop_chain_placed_ok
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet hiding chainKeyBytes_pointsTo
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt

/-- CLI relocatable S3 commit checkpoint state at `entry + 2220#64` (`+0x8ac`). -/
def CliDhCommitStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64; let draws := min 32 x.rest.length
  s.pc = entry + 2220#64 ∧ tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧ s.readReg64 .x20 = sp + 0x140#64 ∧ s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧ s.readReg64 .x23 = sp + 0x500#64 ∧ s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧ s.readReg64 .x28 = sp + 0x3d0#64 ∧
  ∃ (msgW : BitVec 32), msgW.setWidth 8 = msgTypeByte x.msgType ∧
    (s.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗ ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion (sp + 0x1d8#64) 0xd8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x110 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x80 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

/-- CLI relocatable S3 commit sub-segment seam (`entry + 2220#64 → entry + 996#64` or panic). -/
def CliS3CommitSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (receiverChainKey : ChainKey)
    (newSenderKey : KeyPair) (finalRootKey : RootKey) (senderChainKey : ChainKey) (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc → tr.ratchet.receiverChains.length < 2 ^ 32 →
    Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    CliDhCommitStatePlaced entry A ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s → prog.CodeLoaded s.mem →
    let newChain : ReceiverChain := { senderRatchetKey := x.msg.senderRatchetKey, chainKey := some receiverChainKey, messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩, rootKey := finalRootKey,
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1),
        receiverChains := RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧
      ((∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1
          receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

private theorem add_lscl_pre {α : Type} [LibsignalPlacement] {spec : Spec α} {arg : α}
    {s : State} {Rest : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hm : s.mem ⊨ spec.pre arg s ∗ Rest) :
    s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre arg s ∗ Rest := by
  dsimp only [withLsCodeLoaded]
  have h1 : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (spec.pre arg s ∗ Rest) := by
    rw [satisfies_pure_sepConj]; exact ⟨hcl, hm⟩
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1

private theorem dhCommit_step1_2_cl_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hShim : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hPanic : prog.externAt? (lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpySpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec A)))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State) (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace) (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (memRegion sp 12 ∗ ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x440#64) 16 ∗ memRegion (sp + 0x4e0#64) 32 ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool ∗ stackAt sp chainKeyToPbStack) ∗ (Frame ∗ R)) :
    let sckBs := chainKeyBytes senderChainKey
    let sck0 := DhCommit.pack64 (sckBs.take 8); let sck1 := DhCommit.pack64 ((sckBs.drop 8).take 8)
    let sck16 := DhCommit.pack32 ((sckBs.drop 16).take 4); let sck2 := DhCommit.pack64 ((sckBs.drop 20).take 8)
    let sck3 := DhCommit.pack64 (sckBs.drop 28)
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      ∃ boxPtr srkPtr ckPtr : BitVec 64, ∃ pad : List (BitVec 8),
        srkPtr ≠ 0 ∧ pad.length = 4 ∧ sf.pc = entry + 0xa84#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
           ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗ ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
           ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
           memRegion (sp + 0x1b0#64) 40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
           ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
           ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
           ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
           (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗ optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
           A.pool ∗ stackAt sp chainKeyToPbStack) ∗ (Frame ∗ R))) := by
  intro sckBs sck0 sck1 sck16 sck2 sck3
  let InitRest : SepProp := memRegion sp 12 ∗ ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
    ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗ (Frame ∗ R)
  have hm_440 : s.mem ⊨ memRegion (sp + 0x440#64) 16 ∗ (memRegion (sp + 0x4e0#64) 32 ∗ InitRest) := by
    dsimp only [InitRest]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨v440, v448, hm_440⟩ := elim_memRegion_16 hm_440
  have hm_4e0 : s.mem ⊨ memRegion (sp + 0x4e0#64) 32 ∗
      (((sp + 0x440#64) ↦₆₄ v440) ∗ ((sp + 0x440#64 + 8#64) ↦₆₄ v448) ∗ InitRest) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_440
  obtain ⟨v4e0, v4e8, v4f0, v4f8, hm_4e0⟩ := elim_memRegion_32 hm_4e0; dsimp only [InitRest] at hm_4e0
  have hrk0_len : (keyToBytes32 0).length = 32 := by simp [keyToBytes32]
  have hrk_len : (keyToBytes32 finalRootKey).length = 32 := by simp [keyToBytes32]
  have hb8_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk0_len
  have h194_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0x194#64) hrk_len
  have h1b4_cells := pointsToBytes_chainKey_eq_cells (sp + 0x1b4#64) senderChainKey
  set oldRk0 := DhCommit.pack32 ((keyToBytes32 0).take 4); set oldRk4 := DhCommit.pack64 (((keyToBytes32 0).drop 4).take 8)
  set oldRk12 := DhCommit.pack64 (((keyToBytes32 0).drop 12).take 8); set oldRk20 := DhCommit.pack64 (((keyToBytes32 0).drop 20).take 8)
  set oldRk28 := DhCommit.pack32 ((keyToBytes32 0).drop 28); set rk0 := DhCommit.pack32 ((keyToBytes32 finalRootKey).take 4)
  set rk4 := DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 4).take 8); set rk12 := DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 12).take 8)
  set rk20 := DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 20).take 8); set rk28 := DhCommit.pack32 ((keyToBytes32 finalRootKey).drop 28)
  have eb1 := add_assoc_const sp 0xb8#64 4#64 0xbc#64; have eb2 := add_assoc_const sp 0xb8#64 12#64 0xc4#64
  have eb3 := add_assoc_const sp 0xb8#64 20#64 0xcc#64; have eb4 := add_assoc_const sp 0xb8#64 28#64 0xd4#64
  rw [eb1, eb2, eb3, eb4] at hb8_cells
  rw [add_assoc_const sp 0x194#64 4#64 0x198#64, add_assoc_const sp 0x194#64 12#64 0x1a0#64,
      add_assoc_const sp 0x194#64 20#64 0x1a8#64, add_assoc_const sp 0x194#64 28#64 0x1b0#64] at h194_cells
  rw [add_assoc_const sp 0x1b4#64 8#64 0x1bc#64, add_assoc_const sp 0x1b4#64 16#64 0x1c4#64,
      add_assoc_const sp 0x1b4#64 20#64 0x1c8#64, add_assoc_const sp 0x1b4#64 28#64 0x1d0#64] at h1b4_cells
  rw [add_assoc_const sp 0x440#64 8#64 0x448#64, add_assoc_const sp 0x4e0#64 8#64 0x4e8#64,
      add_assoc_const sp 0x4e0#64 16#64 0x4f0#64, add_assoc_const sp 0x4e0#64 24#64 0x4f8#64,
      hb8_cells, h194_cells, h1b4_cells] at hm_4e0
  have hm_step1 : s.mem ⊨
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗ ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗ ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗ ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗ ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗ ((sp + 0x1a8#64) ↦₆₄ rk20) ∗ ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗ ((sp + 0x1bc#64) ↦₆₄ sck1) ∗ ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗ ((sp + 0x1d0#64) ↦₆₄ sck3) ∗ ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗ ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗ ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗ ((sp + 0x4f8#64) ↦₆₄ v4f8)) ∗
      ((memRegion sp 12 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗ Frame) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_4e0
  refine ReachesOrPanic.of_sepWP
    (hwp.step1 sp msgA scIdx oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0
      oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3 v440 v448 v4e0 v4e8 v4f0 v4f8
      s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28) hm_step1 hL ?_
  intro s1 P1 hpc1 hrun1 hkf1 _hsym1 hL1 hm1 hpost1
  have hcl1 := hcl.of_keepsFrozen hkf1
  rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hb8_final : ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) =
      ((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
      ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗ ((sp + 0xd4#64) ↦₃₂ rk28) := by
    rw [pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk_len, eb1, eb2, eb3, eb4]
  have h190_1b0_reg : (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗
      ((sp + 0x1a0#64) ↦₆₄ rk12) ∗ ((sp + 0x1a8#64) ↦₆₄ rk20)) ⊢ memRegion (sp + 0x190#64) 32 := by
    have hsplit32 := memRegion_split (sp + 0x190#64) 8 24 (by decide)
    have hsplit8 := memRegion_split (sp + 0x190#64) 4 4 (by decide)
    have hsplit24 := memRegion_split (sp + 0x198#64) 8 16 (by decide)
    rw [show (8 + 24 : Nat) = 32 from rfl] at hsplit32; rw [show (4 + 4 : Nat) = 8 from rfl] at hsplit8
    rw [show (8 + 16 : Nat) = 24 from rfl] at hsplit24
    rw [hsplit32, hsplit8, add_assoc_const sp 0x190#64 (BitVec.ofNat 64 4) 0x194#64,
        add_assoc_const sp 0x190#64 (BitVec.ofNat 64 8) 0x198#64, hsplit24,
        add_assoc_const sp 0x198#64 (BitVec.ofNat 64 8) 0x1a0#64]
    have ha0 := cells_2_to_memRegion_16 (sp + 0x1a0#64) rk12 rk20
    rw [add_assoc_const sp 0x1a0#64 8#64 0x1a8#64] at ha0
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono (sepConj_mono (cell32_to_memRegion_4 _ 0#32) (cell32_to_memRegion_4 _ rk0))
        (sepConj_mono (cell_to_memRegion_8 _ rk4) ha0))
  have h1b0_40_reg : (((sp + 0x1b0#64) ↦₃₂ rk28) ∗ ((sp + 0x1b4#64) ↦₆₄ sck0) ∗ ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
      ((sp + 0x1c4#64) ↦₃₂ sck16) ∗ ((sp + 0x1c8#64) ↦₆₄ sck2) ∗ ((sp + 0x1d0#64) ↦₆₄ sck3)) ⊢ memRegion (sp + 0x1b0#64) 40 := by
    have hsplit40 := memRegion_split (sp + 0x1b0#64) 4 36 (by decide)
    rw [show (4 + 36 : Nat) = 40 from rfl] at hsplit40; rw [hsplit40, add_assoc_const sp 0x1b0#64 (BitVec.ofNat 64 4) 0x1b4#64]
    have hsck_reg := pointsToBytes_entails_memRegion (sp + 0x1b4#64) sckBs
    rw [chainKeyBytes_length senderChainKey, h1b4_cells] at hsck_reg
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono (cell32_to_memRegion_4 _ rk28) hsck_reg)
  have hstk_ser := stackAt_split_from sp chainKeyToPbStack publicKeySerializeStack (by decide) (by decide)
  let SckRest0 : SepProp := ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗ memRegion (sp + 0x1b0#64) 40 ∗
    ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
    ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame
  let SckRest : SepProp := ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ SckRest0
  have hm_ser : s1.mem ⊨ (publicKeySerializeSpec A).pre ⟨msgA + 0x38#64, srk⟩ s1 ∗
      ((memRegion sp 12 ∗ memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - publicKeySerializeStack) ∗ SckRest0) ∗ R) := by
    dsimp only [publicKeySerializeSpec, SckRest0]; rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hx0_1, ?_⟩; rw [hb8_final]
    have hreg_s1 := Satisfies.mono (sepConj_mono h190_1b0_reg (sepConj_mono_left h1b0_40_reg))
      (show s1.mem ⊨ (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗
         ((sp + 0x1a0#64) ↦₆₄ rk12) ∗ ((sp + 0x1a8#64) ↦₆₄ rk20)) ∗
        (((sp + 0x1b0#64) ↦₃₂ rk28) ∗ ((sp + 0x1b4#64) ↦₆₄ sck0) ∗ ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
         ((sp + 0x1c4#64) ↦₃₂ sck16) ∗ ((sp + 0x1c8#64) ↦₆₄ sck2) ∗ ((sp + 0x1d0#64) ↦₆₄ sck3)) ∗
        (((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗ memRegion sp 12 ∗
         ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ (((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗ ((sp + 0xd4#64) ↦₃₂ rk28)) ∗
         ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
         ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame ∗ R) from
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1')
    rw [hstk_ser] at hreg_s1; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hreg_s1
  refine ReachesOrPanic.of_call_alloc_panic hPkSer hpc1 hrun1 hsp_align1 hx30_1
    (htr1.trans htrace) (add_lscl_pre hcl1 hm_ser) hL1 (by intro _; rfl) (by intros; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hkf2 _hsym2 hL2 hm2
  have hcl2 := hcl1.of_keepsFrozen hkf2
  dsimp only [withLsCodeLoaded, publicKeySerializeSpec] at hm2
  rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm2; rcases hm2 with ⟨⟨hx1_2, htr2⟩, hm2⟩
  set boxPtr := s2.readReg64 .x0
  have hser_len : srk.serialize.length = 33 := DhCommit.publicKey_serialize_length srk
  have hbox_buf : boxU8Buf A boxPtr srk.serialize =
      (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) := by
    unfold boxU8Buf; simp only [DhCommit.publicKey_serialize_ne_nil srk, ↓reduceIte, hser_len]
  rw [hbox_buf] at hm2
  have hm2_sp : s2.mem ⊨ memRegion sp 8 ∗ memRegion (sp + 8#64) 4 ∗
      ((⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       A.pool ∗ stackAt sp chainKeyToPbStack ∗ memRegion (sp + 0x190#64) 32 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest ∗ R) := by
    have hsplit12 := memRegion_split sp 8 4 (by decide); rw [show (8 + 4 : Nat) = 12 from rfl] at hsplit12
    dsimp only [SckRest, SckRest0] at hm2 ⊢; rw [← sepConj_assoc, ← hsplit12, hstk_ser]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2
  rw [sepConj_assoc] at hm2_sp; obtain ⟨vSp0, hm2_sp⟩ := elim_memRegion_8 hm2_sp
  obtain ⟨vSp8, hm2_sp8⟩ := elim_memRegion_4 (show s2.mem ⊨ memRegion (sp + 8#64) 4 ∗
      ((sp ↦₆₄ vSp0) ∗ (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       A.pool ∗ stackAt sp chainKeyToPbStack ∗ memRegion (sp + 0x190#64) 32 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest ∗ R) from
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2_sp)
  have hm_pre_shim : s2.mem ⊨ ((sp ↦₆₄ vSp0) ∗ ((sp + 8#64) ↦₃₂ vSp8)) ∗
      (((A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗
        memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) := by
    have hdrop_pure : (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ⊢
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) := Entails.pure_left (fun _ => Entails.refl _)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl))
      (Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop_pure))) hm2_sp8)
  refine ReachesOrPanic.of_sepWP
    (hwp.step2_pre_shim sp boxPtr vSp0 vSp8 sck16 s2 hpc2 hrun2 (by reg_chain) hsp_align2 rfl hx1_2 (by reg_chain))
    hm_pre_shim hL2 ?_
  intro s3 P3 hpc3 hrun3 hkf3 _hsym3 hL3 hm3 hpost3
  have hcl3 := hcl2.of_keepsFrozen hkf3
  rcases hpost3 with ⟨hsp3, hsp_align3, htr3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, _hx24_3, hx25_3, hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm3' := Satisfies.mono (sepConj_mono_left hP3) hm3
  have hm_shim : s3.mem ⊨ noAllocShimSpec.pre () s3 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        A.pool ∗ stackAt sp chainKeyToPbStack ∗ memRegion (sp + 0x190#64) 32 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) := by
    dsimp only [noAllocShimSpec]; rw [emp_sepConj]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm3'
  refine ReachesOrPanic.of_call_no_panic hShim hpc3 hrun3 hsp_align3 hx30_3 hm_shim hL3
    (by intro _; rfl) (by intros; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 hkf4 _hsym4 hL4 hm4
  have hcl4 := hcl3.of_keepsFrozen hkf4
  dsimp only [noAllocShimSpec] at hm4; rw [satisfies_pure_sepConj] at hm4; rcases hm4 with ⟨htr4, hm4⟩
  have hm_pre_alloc : s4.mem ⊨ emp ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        A.pool ∗ stackAt sp chainKeyToPbStack ∗ memRegion (sp + 0x190#64) 32 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) := by rw [emp_sepConj]; exact hm4
  refine ReachesOrPanic.of_sepWP
    (hwp.step2_pre_alloc sp s4 hpc4 hrun4 (by reg_chain) hsp_align4 (by reg_chain)) hm_pre_alloc hL4 ?_
  intro s5 P5 hpc5 hrun5 hkf5 _hsym5 hL5 hm5 hpost5
  have hcl5 := hcl4.of_keepsFrozen hkf5
  rcases hpost5 with ⟨hsp5, hsp_align5, htr5, hx0_5, hx1_5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, _hx24_5, hx25_5, hx26_5, _hx27_5, _hx28_5, hx29_5, hx30_5, hvregs_5, hP5⟩
  have hm5' := Satisfies.mono (sepConj_mono_left hP5) hm5; rw [emp_sepConj] at hm5'
  have hstk_alloc := stackAt_split_from sp chainKeyToPbStack allocHookStack (by decide) (by decide)
  have hm_alloc : s5.mem ⊨ (rustAllocSpec A).pre (33, 1) s5 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - allocHookStack) ∗
        memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) := by
    dsimp only [rustAllocSpec]; rw [hstk_alloc] at hm5'
    rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by rw [hx0_5]; rfl, by rw [hx1_5]; rfl, by decide, ⟨0, rfl⟩, by decide⟩,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm5'⟩
  refine ReachesOrPanic.of_call_no_panic hAlloc hpc5 hrun5 hsp_align5 hx30_5 hm_alloc hL5
    (by intro _; rfl) (by intros; rfl) ?_
  intro s6 hpc6 hrun6 hsp6 hsp_align6 hcs6 hkf6 _hsym6 hL6 hm6
  have hcl6 := hcl5.of_keepsFrozen hkf6
  dsimp only [rustAllocSpec] at hm6
  set srkPtr := s6.readReg64 .x0; have htr_s5 : s5.trace = s0.trace := by reg_chain
  by_cases hsrk0 : srkPtr = 0
  · simp only [hsrk0, ↓reduceIte] at hm6
    have hm6_pull : s6.mem ⊨ ⌜s6.trace = s5.trace ++ [allocFailedEvent]⌝ ∗
        (emp ∗ (((A.pool ∗ stackAt s5.sp allocHookStack) ∗ ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
          (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - allocHookStack) ∗
          memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest)) ∗ R)) := by
      rw [emp_sepConj]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm6
    rw [satisfies_pure_sepConj] at hm6_pull; rcases hm6_pull with ⟨htr6_fail, hm_oom⟩
    refine ReachesOrPanic.of_sepWP (hwp.step2_oom sp s6 hpc6 hrun6 (hsp6.trans hsp5) hsp_align6 hsrk0) hm_oom hL6 ?_
    intro s7 _ hpc7 hrun7 _ _ _ hm7 ⟨htr7, _⟩
    rcases allocFailedIn_of_eq (by rw [htr7, htr6_fail, htr_s5] : s7.trace = s0.trace ++ [allocFailedEvent]) with ⟨hfail7, hpfx7⟩
    rw [← sepConj_assoc] at hm7; exact ReachesOrPanic.of_panic_extern hrun7 (by rw [hpc7]; exact hPanic) hfail7 hpfx7 hm7
  · simp only [hsrk0, ↓reduceIte] at hm6; rw [hsp5] at hm6
    have hm6_pull : s6.mem ⊨ ⌜srkPtr.toNat % 1 = 0 ∧ s6.trace = s5.trace⌝ ∗
        ((sp ↦₆₄ boxPtr) ∗ ((memRegion srkPtr 33 ∗ A.live srkPtr 33 1 ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R)) := by
      rw [hstk_alloc]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm6
    rw [satisfies_pure_sepConj] at hm6_pull; rcases hm6_pull with ⟨⟨_, htr6⟩, hm_post_alloc⟩
    refine ReachesOrPanic.of_sepWP
      (hwp.step2_post_alloc sp srkPtr boxPtr s6 hpc6 hrun6 (by reg_chain) hsp_align6 rfl hsrk0 (by reg_chain)) hm_post_alloc hL6 ?_
    intro s7 P7 hpc7 hrun7 hkf7 _ hL7 hm7 hpost7; have hcl7 := hcl6.of_keepsFrozen hkf7
    rcases hpost7 with ⟨hsp7, hsp_align7, htr7, hx0_7, hx1_7, hx2_7,
      hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, _, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hx30_7, hvregs_7, hP7⟩
    have hm7' := Satisfies.mono (sepConj_mono_left hP7) hm7
    have hm_memcpy : s7.mem ⊨ framelessMemcpySpec.pre (srkPtr, boxPtr, srk.serialize) s7 ∗
        (((sp ↦₆₄ boxPtr) ∗ A.live srkPtr 33 1 ∗ A.live boxPtr 33 1 ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗ memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) := by
      dsimp only [framelessMemcpySpec]; rw [hser_len, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_7, hx1_7, by rw [hx2_7]; rfl⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm7'⟩
    refine ReachesOrPanic.of_call_no_panic hMemcpy hpc7 hrun7 hsp_align7 hx30_7 hm_memcpy hL7 (by intro _; rfl) (by intros; rfl) ?_
    intro s8 hpc8 hrun8 hsp8 hsp_align8 hcs8 hkf8 _ hL8 hm8; have hcl8 := hcl7.of_keepsFrozen hkf8
    dsimp only [framelessMemcpySpec] at hm8; rw [sepConj_assoc, satisfies_pure_sepConj] at hm8; rcases hm8 with ⟨⟨_, htr8⟩, hm8⟩
    refine ReachesOrPanic.of_sepWP (hwp.step2_to_pb sp s8 hpc8 hrun8 (by reg_chain) hsp_align8 (by reg_chain))
      (show s8.mem ⊨ emp ∗ (((srkPtr ↦ₛ srk.serialize) ∗ (boxPtr ↦ₛ srk.serialize) ∗ (sp ↦₆₄ boxPtr) ∗
        A.live srkPtr 33 1 ∗ A.live boxPtr 33 1 ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ SckRest) ∗ R) by
        rw [emp_sepConj]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm8) hL8 ?_
    intro s9 P9 hpc9 hrun9 hkf9 _ hL9 hm9 hpost9; have hcl9 := hcl8.of_keepsFrozen hkf9
    rcases hpost9 with ⟨hsp9, hsp_align9, htr9, hx0_9, hx8_9,
      hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, _, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hx30_9, hvregs_9, hP9⟩
    have hm9' := Satisfies.mono (sepConj_mono_left hP9) hm9; rw [emp_sepConj] at hm9'
    have hm_to_pb : s9.mem ⊨ (chainKeyToPbSpec A).pre ⟨sp + 0x3d0#64, receiverChainKey, sp + 0x190#64⟩ s9 ∗
        (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗ SckRest) ∗ R) := by
      dsimp only [chainKeyToPbSpec]; rw [hsp9, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_9, hx8_9⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm9'⟩
    refine ReachesOrPanic.of_call_alloc_panic hToPb hpc9 hrun9 hsp_align9 hx30_9
      (by reg_chain) (add_lscl_pre hcl9 hm_to_pb) hL9 (by intro _; rfl) (by intros; rfl) ?_
    intro s10 hpc10 hrun10 hsp10 hsp_align10 hcs10 _hkf10 _hsym10 hL10 hm10
    dsimp only [withLsCodeLoaded, chainKeyToPbSpec] at hm10
    rw [hsp9, sepConj_assoc, satisfies_pure_sepConj] at hm10; rcases hm10 with ⟨htr10, hm10⟩
    have hm10_pb : s10.mem ⊨
        (∃∗ p' : BitVec 64, optChainKeyAt A ⟨32#64, p'⟩ (some receiverChainKey) (sp + 0x190#64)) ∗
        (((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ A.pool ∗ stackAt sp chainKeyToPbStack ∗
         ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗ SckRest) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm10
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm10_pb; rcases hm10_pb with ⟨ckPtr, hm10_pb⟩
    rw [optChainKeyAt_eq_exists_bytes A ⟨32#64, ckPtr⟩ (some receiverChainKey) (sp + 0x190#64),
        sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm10_pb
    rcases hm10_pb with ⟨pad, hm10_pb⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm10_pb; rcases hm10_pb with ⟨hpad, hm10_pb⟩
    dsimp only [SckRest, SckRest0] at hm10_pb
    exact ReachesOrPanic.done ⟨boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc10, hrun10,
      by reg_chain, hsp_align10, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, hL10, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm10_pb⟩

private theorem dhCommit_step3a_cl_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace) (hcl : LibsignalCodeLoaded lsmpl s.mem) (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
      A.pool ∗ stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64, gcs.length < chainsCap1.toNat ∧
        sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗ vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 gcs ∗
          A.pool ∗ stackAt sp growOneStack) ∗ (Frame ∗ R))) := by
  have hexp0 : s.mem ⊨ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗ A.pool ∗ stackAt sp growOneStack ∗ (Frame ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  by_cases hgrow : BitVec.ofNat 64 gcs.length = chainsCap
  · have hexp := Satisfies.mono (sepConj_mono_left (vecBuf_chainAt_expose_bytes A chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp; rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by rw [hgrow]
    have hm_grow_wp : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
          chainHeaps A gcs ∗ A.pool ∗ stackAt sp growOneStack ∗ Frame) ∗ R) := by
      rw [h38_grow] at hexp; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hexp
    refine ReachesOrPanic.of_sepWP (hwp.step3a_grow sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align) hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 hkf1 _hsym1 hL1 hm1 hpost1
    have hcl1 := hcl.of_keepsFrozen hkf1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨ (CryptoVerification.LibsignalSession.growOneSpec A).pre (sp + 0x38#64, chainsCap, chainsPtr, bs) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗ chainHeaps A gcs ∗ Frame) ∗ R) := by
      dsimp only [CryptoVerification.LibsignalSession.growOneSpec]; rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by omega, hptr, hmax_lt⟩, ?_⟩
      rw [add_assoc_const sp 0x38#64 8#64 0x40#64]; rw [← h38_grow] at hm1'
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1'
    refine ReachesOrPanic.of_call_alloc_panic hGrow
      hpc1 hrun1 hsp_align1 hx30_1 (htr1.trans htrace) (add_lscl_pre hcl1 hm_call) hL1 (by intro _; rfl) (by intros; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 _hkf2 _hsym2 hL2 hm2
    dsimp only [withLsCodeLoaded, CryptoVerification.LibsignalSession.growOneSpec] at hm2
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm2; rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2; rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2; rcases hm2 with ⟨hp', hm2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < cap1.toNat := by omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    rw [add_assoc_const sp 0x38#64 8#64 0x40#64] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.live p' (cap1.toNat * 104) 8 := by rw [hcap1_toNat]
    have hmr_eq : memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
        memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
      rw [hlen_bs, hcap1_toNat, ← hlen_eq_cap]
    have hpull2 : s2.mem ⊨ (A.live p' (cap1.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) ∗ chainHeaps A gcs) ∗
        (((sp + 0x38#64) ↦₆₄ cap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         A.pool ∗ stackAt sp growOneStack ∗ (Frame ∗ R)) := by
      rw [hlive_eq, hmr_eq] at hm2; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2
    have hm2_vec := Satisfies.mono (sepConj_mono_left (vecBuf_chainAt_of_bytes A cap1 p' hcap1_ne hbs (by omega) (by omega) hp')) hpull2
    exact ReachesOrPanic.done ⟨cap1, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, hL2, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2_vec⟩
  · have hle_cap : gcs.length ≤ chainsCap.toNat := by
      unfold vecBuf at hexp0; rw [sepConj_assoc, satisfies_pure_sepConj] at hexp0; exact hexp0.1.1
    have hlt_cap : gcs.length < chainsCap.toNat := by
      rcases Nat.lt_or_eq_of_le hle_cap with hlt | heq
      · exact hlt
      · exfalso; apply hgrow; rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hm_nogrow : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          A.pool ∗ stackAt sp growOneStack ∗ Frame) ∗ R) := Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    refine ReachesOrPanic.of_sepWP (hwp.step3a_nogrow sp chainsCap (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hgrow) hm_nogrow hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    exact ReachesOrPanic.done ⟨chainsCap, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1'⟩

private theorem dhCommit_evict_one_cl_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveSpec dropChainStack))
    (hDrop : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gc₀ : ChainGhost × ReceiverChain) (gcs : List (ChainGhost × ReceiverChain)) (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = entry + 0xb04#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace) (hx23 : s.readReg64 .x23 = sp + 0x500#64) (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (gc₀ :: gcs).length)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActive A sp chainsCap chainsPtr (gc₀ :: gcs) ∗ (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      sf.pc = entry + 0xb8c#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
      (sf.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R))) := by
  unfold evictActive at hmem
  let EvRest : SepProp := ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
    memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x500#64) 96 ∗ A.pool ∗ stackAt sp dropChainStack ∗ (Frame ∗ R)
  have hexp_pull : s.mem ⊨
      (∃∗ pad₀ : List (BitVec 8), ∃∗ bs_rest : List (BitVec 8),
        ⌜pad₀.length = optChainKeyPadLen gc₀.2.chainKey ∧ ChainArrayBytes gcs bs_rest ∧
          bs_rest.length = gcs.length * 104 ∧ gcs.length + 1 ≤ chainsCap.toNat ∧
          chainsCap.toNat * 104 < 2 ^ 63 ∧ chainsPtr ≠ 0 ∧ chainsCap ≠ 0⌝ ∗
        A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
        memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeap A gc₀ ∗ chainHeaps A gcs) ∗ EvRest := by
    have hexp := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecBuf_chainAt_expose_for_remove0 A chainsCap chainsPtr gc₀ gcs))))) hmem
    dsimp only [EvRest]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hexp
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull; rcases hexp_pull with ⟨pad₀, hexp_pull⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull; rcases hexp_pull with ⟨bs_rest, hexp_pull⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hexp_pull
  rcases hexp_pull with ⟨⟨hpad₀, hrest, hbs_len, hcap_le, hcap_lt, hptr, _hcap_ne⟩, hm0⟩
  have hsrk_ne_mem := Satisfies.mono (sepConj_mono_left (chainHeap_srk_cap_ne_zero A gc₀))
    (show s.mem ⊨ chainHeap A gc₀ ∗ (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
      ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
      memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
      chainHeaps A gcs ∗ EvRest) from Satisfies.mono (Entails.of_eq (by ac_rfl)) hm0)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsrk_ne_mem; rcases hsrk_ne_mem with ⟨hc0_ne, hm1⟩
  dsimp only [EvRest] at hm1
  obtain ⟨s500, s508, s510, s518, s520, s528, s530, s538, s540, s548, s550, s558, hm2⟩ :=
    DhCommit.elim_memRegion_96 (show s.mem ⊨ memRegion (sp + 0x500#64) 96 ∗
      ((chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗ memRegion (sp + 0x190#64) 104 ∗
       A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
       memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
       chainHeap A gc₀ ∗ chainHeaps A gcs ∗ A.pool ∗ stackAt sp dropChainStack ∗ (Frame ∗ R)) from
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1)
  set tail₀ := optChainKeyTailBytes gc₀.1.ck gc₀.2.chainKey pad₀
  set c0 := gc₀.1.srk.cap; set c1 := gc₀.1.srk.ptr; set c2 := BitVec.ofNat 64 gc₀.1.srk.bytes.length
  set c3 := gc₀.1.priv.cap; set c4 := gc₀.1.priv.ptr; set c5 := BitVec.ofNat 64 gc₀.1.priv.bytes.length
  set c6 := gc₀.1.mkCap; set c7 := gc₀.1.mkPtr; set c8 := BitVec.ofNat 64 (gc₀.1.keys.zip gc₀.2.messageKeys).length
  set c9 := DhCommit.pack64 (tail₀.take 8); set c10 := DhCommit.pack64 ((tail₀.drop 8).take 8)
  set c11 := DhCommit.pack64 ((tail₀.drop 16).take 8); set c12 := DhCommit.pack64 (tail₀.drop 24)
  have hcells_ptr : (chainsPtr ↦ₛ chainBytes gc₀ pad₀) =
      (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
      ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
      ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
      ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
      ((chainsPtr + 96#64) ↦₆₄ c12) := pointsToBytes_chainBytes_eq_13_cells chainsPtr gc₀ hpad₀
  have hm_pre_wp : s.mem ⊨
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
       ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
       ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
       ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
       ((chainsPtr + 96#64) ↦₆₄ c12) ∗ ((sp + 0x500#64) ↦₆₄ s500) ∗ ((sp + 0x508#64) ↦₆₄ s508) ∗
       ((sp + 0x510#64) ↦₆₄ s510) ∗ ((sp + 0x518#64) ↦₆₄ s518) ∗ ((sp + 0x520#64) ↦₆₄ s520) ∗
       ((sp + 0x528#64) ↦₆₄ s528) ∗ ((sp + 0x530#64) ↦₆₄ s530) ∗ ((sp + 0x538#64) ↦₆₄ s538) ∗
       ((sp + 0x540#64) ↦₆₄ s540) ∗ ((sp + 0x548#64) ↦₆₄ s548) ∗ ((sp + 0x550#64) ↦₆₄ s550) ∗
       ((sp + 0x558#64) ↦₆₄ s558)) ∗
      ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗ memRegion (sp + 0x190#64) 104 ∗
        A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
        memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeap A gc₀ ∗ chainHeaps A gcs ∗ A.pool ∗ stackAt sp dropChainStack ∗ Frame) ∗ R) := by
    rw [hcells_ptr, add_assoc_const sp 0x500#64 8#64 0x508#64, add_assoc_const sp 0x500#64 16#64 0x510#64,
        add_assoc_const sp 0x500#64 24#64 0x518#64, add_assoc_const sp 0x500#64 32#64 0x520#64,
        add_assoc_const sp 0x500#64 40#64 0x528#64, add_assoc_const sp 0x500#64 48#64 0x530#64,
        add_assoc_const sp 0x500#64 56#64 0x538#64, add_assoc_const sp 0x500#64 64#64 0x540#64,
        add_assoc_const sp 0x500#64 72#64 0x548#64, add_assoc_const sp 0x500#64 80#64 0x550#64,
        add_assoc_const sp 0x500#64 88#64 0x558#64] at hm2
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2
  refine ReachesOrPanic.of_sepWP
    (hwp.step4b_pre_memmove sp chainsPtr (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558
      s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28) hm_pre_wp hL ?_
  intro s1 P1 hpc1 hrun1 hkf1 _hsym1 hL1 hm_s1 hpost1
  have hcl1 := hcl.of_keepsFrozen hkf1
  rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm_s1' := Satisfies.mono (sepConj_mono_left hP1) hm_s1
  set b₀ := chainBytes gc₀ pad₀
  have hb₀_len : b₀.length = 104 := chainBytes_length gc₀ hpad₀
  have hcomb_bytes : (chainsPtr ↦ₛ (b₀ ++ bs_rest)) = (chainsPtr ↦ₛ b₀) ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) := by
    rw [pointsToBytes_append, hb₀_len]
  have hx2_toNat : (s1.readReg64 .x2).toNat = gcs.length * 104 := by
    rw [hx2_1, List.length_cons]; exact memmove_len_toNat hlen_lt
  let Cells500_c : SepProp :=
    ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗ ((sp + 0x518#64) ↦₆₄ c4) ∗
    ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗ ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗
    ((sp + 0x540#64) ↦₆₄ c9) ∗ ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)
  have hm_memmove : s1.mem ⊨
      (sessionMemmoveSpec dropChainStack).pre (chainsPtr, b₀ ++ bs_rest, 0, 104, gcs.length * 104) s1 ∗
      ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
        memRegion (sp + 0x190#64) 104 ∗ Cells500_c ∗ A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
        memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeap A gc₀ ∗ chainHeaps A gcs ∗ A.pool ∗ Frame) ∗ R) := by
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec, Cells500_c]
    have ⟨hb1, hb2⟩ := DhCommitFacts.memmove_bounds (n := gcs.length)
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by rw [BitVec.add_zero, List.length_append, hb₀_len, hbs_len]; exact ⟨hx0_1, hx1_1, hx2_toNat, hb1, hb2⟩, ?_⟩
    rw [hcomb_bytes, show b₀ = chainBytes gc₀ pad₀ from rfl, hcells_ptr]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_s1'
  refine ReachesOrPanic.of_call_no_panic hMemmove
    hpc1 hrun1 hsp_align1 hx30_1 hm_memmove hL1 (by intro _; rfl) (by intros; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hkf2 _hsym2 hL2 hm_s2
  have hcl2 := hcl1.of_keepsFrozen hkf2
  dsimp only [sessionMemmoveSpec] at hm_s2
  rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm_s2; rcases hm_s2 with ⟨⟨_hx0_2, htr2⟩, hm_s2⟩
  have hvec_reasm : s2.mem ⊨ memRegion (sp + 0x190#64) 104 ∗
      (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗ Cells500_c ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       chainHeap A gc₀ ∗ A.pool ∗ stackAt sp dropChainStack ∗ (Frame ∗ R)) := by
    have hpull_rem : s2.mem ⊨
        (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ (chainsPtr ↦ₛ listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)) ∗
         memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104)) ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
         chainHeaps A gcs) ∗
        (memRegion (sp + 0x190#64) 104 ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         Cells500_c ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ chainHeap A gc₀ ∗ A.pool ∗ stackAt sp dropChainStack ∗ (Frame ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_s2
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) (Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_of_remove0 A chainsCap chainsPtr hb₀_len hrest hcap_le hcap_lt hptr)) hpull_rem)
  obtain ⟨s190, s198, s1a0, s1a8, s1b0, s1b8, s1c0, s1c8, s1d0, s1d8, s1e0, s1e8, s1f0, hm_s2_cells⟩ :=
    DhCommit.elim_memRegion_104 hvec_reasm
  have hm_post_mm_wp : s2.mem ⊨
      (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
       ((sp + 0x190#64) ↦₆₄ s190) ∗ ((sp + 0x198#64) ↦₆₄ s198) ∗ ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗
       ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗ ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗ ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗ ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗
       ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗ ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗ ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗ ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
       ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗ ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗ ((sp + 0x530#64) ↦₆₄ c7) ∗
       ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗ ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗
       ((sp + 0x558#64) ↦₆₄ c12)) ∗
      ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
        chainHeap A gc₀ ∗ A.pool ∗ stackAt sp dropChainStack ∗ Frame) ∗ R) := by
    dsimp only [Cells500_c] at hm_s2_cells
    rw [add_assoc_const sp 0x190#64 8#64 0x198#64, add_assoc_const sp 0x190#64 16#64 0x1a0#64,
        add_assoc_const sp 0x190#64 24#64 0x1a8#64, add_assoc_const sp 0x190#64 32#64 0x1b0#64,
        add_assoc_const sp 0x190#64 40#64 0x1b8#64, add_assoc_const sp 0x190#64 48#64 0x1c0#64,
        add_assoc_const sp 0x190#64 56#64 0x1c8#64, add_assoc_const sp 0x190#64 64#64 0x1d0#64,
        add_assoc_const sp 0x190#64 72#64 0x1d8#64, add_assoc_const sp 0x190#64 80#64 0x1e0#64,
        add_assoc_const sp 0x190#64 88#64 0x1e8#64, add_assoc_const sp 0x190#64 96#64 0x1f0#64] at hm_s2_cells
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_s2_cells
  refine ReachesOrPanic.of_sepWP
    (hwp.step4b_post_memmove sp (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0
      s2 hpc2 hrun2 (by reg_chain) hsp_align2
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hc0_ne)
    hm_post_mm_wp hL2 ?_
  intro s3 P3 hpc3 hrun3 hkf3 _hsym3 hL3 hm_s3 hpost3
  have hcl3 := hcl2.of_keepsFrozen hkf3
  rcases hpost3 with ⟨hsp3, hsp_align3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, _hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm_s3' := Satisfies.mono (sepConj_mono_left hP3) hm_s3
  have hcells_190 : ((sp + 0x190#64) ↦ₛ chainBytes gc₀ pad₀) =
      ((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗ ((sp + 0x1a8#64) ↦₆₄ c3) ∗
      ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗ ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗
      ((sp + 0x1d0#64) ↦₆₄ c8) ∗ ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
      ((sp + 0x1f0#64) ↦₆₄ c12) := by
    have h := pointsToBytes_chainBytes_eq_13_cells (sp + 0x190#64) gc₀ hpad₀
    rw [add_assoc_const sp 0x190#64 8#64 0x198#64, add_assoc_const sp 0x190#64 16#64 0x1a0#64,
        add_assoc_const sp 0x190#64 24#64 0x1a8#64, add_assoc_const sp 0x190#64 32#64 0x1b0#64,
        add_assoc_const sp 0x190#64 40#64 0x1b8#64, add_assoc_const sp 0x190#64 48#64 0x1c0#64,
        add_assoc_const sp 0x190#64 56#64 0x1c8#64, add_assoc_const sp 0x190#64 64#64 0x1d0#64,
        add_assoc_const sp 0x190#64 72#64 0x1d8#64, add_assoc_const sp 0x190#64 80#64 0x1e0#64,
        add_assoc_const sp 0x190#64 88#64 0x1e8#64, add_assoc_const sp 0x190#64 96#64 0x1f0#64] at h
    exact h
  have h500_reg : Cells500_c ⊢ memRegion (sp + 0x500#64) 96 := by
    dsimp only [Cells500_c]
    have h := DhCommit.cells_12_to_memRegion_96 (sp + 0x500#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    rw [add_assoc_const sp 0x500#64 8#64 0x508#64, add_assoc_const sp 0x500#64 16#64 0x510#64,
        add_assoc_const sp 0x500#64 24#64 0x518#64, add_assoc_const sp 0x500#64 32#64 0x520#64,
        add_assoc_const sp 0x500#64 40#64 0x528#64, add_assoc_const sp 0x500#64 48#64 0x530#64,
        add_assoc_const sp 0x500#64 56#64 0x538#64, add_assoc_const sp 0x500#64 64#64 0x540#64,
        add_assoc_const sp 0x500#64 72#64 0x548#64, add_assoc_const sp 0x500#64 80#64 0x550#64,
        add_assoc_const sp 0x500#64 88#64 0x558#64] at h; exact h
  have hsub1 : BitVec.ofNat 64 (gc₀ :: gcs).length - 1#64 = BitVec.ofNat 64 gcs.length :=
    DhCommit.sub_one_ofNat_succ gcs.length
  have hm_drop : s3.mem ⊨ (dropChainSpec A).pre ⟨sp + 0x190#64, gc₀⟩ s3 ∗
      ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
        vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗ memRegion (sp + 0x500#64) 96 ∗ Frame) ∗ R) := by
    dsimp only [dropChainSpec]; rw [hsp3, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hx0_3, ?_⟩
    have hpull_drop : s3.mem ⊨ (((sp + 0x190#64) ↦ₛ chainBytes gc₀ pad₀) ∗ chainHeap A gc₀) ∗ Cells500_c ∗
        (A.pool ∗ stackAt sp dropChainStack ∗
         ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗ Frame) ∗ R)) := by
      dsimp only [Cells500_c]; rw [hcells_190, ← hsub1]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_s3'
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) (Satisfies.mono
      (sepConj_mono (chainAt_of_bytes A gc₀ (sp + 0x190#64) hpad₀) (sepConj_mono_left h500_reg)) hpull_drop)
  refine ReachesOrPanic.of_call_no_panic hDrop
    hpc3 hrun3 hsp_align3 hx30_3 (add_lscl_pre hcl3 hm_drop) hL3 (by intro _; rfl) (by intros; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 _hkf4 _hsym4 hL4 hm_s4
  dsimp only [withLsCodeLoaded, dropChainSpec] at hm_s4
  rw [hsp3, sepConj_assoc, satisfies_pure_sepConj] at hm_s4; rcases hm_s4 with ⟨htr4, hm_s4⟩
  refine ReachesOrPanic.done ⟨hpc4, hrun4, by reg_chain, hsp_align4, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL4, ?_⟩
  unfold evictActive; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_s4

private theorem dhCommit_evict_loop_cl_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveSpec dropChainStack))
    (hDrop : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    ∀ (s : State), 6 ≤ gcs.length → gcs.length ≤ 2 ^ 32 →
      s.pc = entry + 0xb04#64 → s.status = .Running → s.sp = sp → s.spAligned = true → s.trace = s0.trace →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = 0xffffffffffffff98#64 →
      s.readReg64 .x28 = BitVec.ofNat 64 gcs.length →
      LibsignalCodeLoaded lsmpl s.mem → prog.CodeLoaded s.mem →
      (s.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) →
      ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
        sf.pc = entry + 0xb98#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨ evictActive A sp chainsCap chainsPtr (evictList gcs) ∗ (Frame ∗ R))) := by
  induction gcs with
  | nil => intro _ hge; simp at hge
  | cons gc₀ gcs ih =>
    intro s hge hle hpc hrun hsp hsp_align htrace hx23 hx24 hx25 hx27 hx28 hcl hL hmem
    rw [evictList_cons_of_ge_six gc₀ gcs hge]
    have hlen_lt : gcs.length < 2 ^ 32 := DhCommitFacts.len_lt_of_cons_le hle
    refine ReachesOrPanic.seq (dhCommit_evict_one_cl_placed hwp C A ctl S hMemmove hDrop
      x R Frame s0 s sp chainsCap chainsPtr gc₀ gcs hlen_lt hpc hrun hsp hsp_align htrace
      hx23 hx24 hx25 hx27 hx28 hcl hL hmem) ?_
    intro s1 hkf1 _hsym1 ⟨hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs_1, hL1, hm1⟩
    have hcl1 := hcl.of_keepsFrozen hkf1
    have hm1_48 : s1.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x500#64) 96 ∗ A.pool ∗ stackAt sp dropChainStack ∗ Frame) ∗ R) := by
      unfold evictActive at hm1; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
    by_cases hge' : 6 ≤ gcs.length
    · refine ReachesOrPanic.of_sepWP
        (hwp.step4c_hi sp (BitVec.ofNat 64 gcs.length) s1 hpc1 hrun1 hsp1 hsp_align1
          (DhCommitFacts.ult_five_of_ge_six hge' hlen_lt)) hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 hkf2 _hsym2 hL2 hm2 hpost2
      have hcl2 := hcl1.of_keepsFrozen hkf2
      rcases hpost2 with ⟨hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2, hP2⟩
      have hm2_act : s2.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        unfold evictActive; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2'
      refine ReachesOrPanic.seq
        (ih s2 hge' (Nat.le_of_lt hlen_lt) hpc2 hrun2 hsp2 hsp_align2 (by reg_chain)
          (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hx28_2 hcl2 hL2 hm2_act) ?_
      intro sf _ _ ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩
      exact ReachesOrPanic.done ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx23_f, hx25_f, by reg_chain, by reg_chain, hL_f, hm_f⟩
    · have hle5 : gcs.length ≤ 5 := DhCommitFacts.le_five_of_not_ge_six hge'
      refine ReachesOrPanic.of_sepWP
        (hwp.step4c_le sp (BitVec.ofNat 64 gcs.length) s1 hpc1 hrun1 hsp1 hsp_align1
          (DhCommitFacts.ult_five_eq_false_of_le_five hle5)) hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 _hkf2 _hsym2 hL2 hm2 hpost2
      rcases hpost2 with ⟨hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx25_2, _hx27_2, _hx28_2, hx29_2, hvregs_2, hP2⟩
      rw [evictList_of_le_five gcs hle5]
      have hm2_act : s2.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        unfold evictActive; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2'
      exact ReachesOrPanic.done ⟨hpc2, hrun2, hsp2, hsp_align2, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL2, hm2_act⟩

private theorem dhCommit_step4_cl_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveSpec dropChainStack))
    (hDrop : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hle : gcs.length ≤ 2 ^ 32)
    (hpc : s.pc = entry + 0xaf0#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace) (hx23 : s.readReg64 .x23 = sp + 0x500#64) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      sf.pc = entry + 0xb98#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
      (sf.mem ⊨ evictActive A sp chainsCap chainsPtr (evictList gcs) ∗ (Frame ∗ R))) := by
  have hm_48 : s.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
      ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
        memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x500#64) 96 ∗ A.pool ∗ stackAt sp dropChainStack ∗ Frame) ∗ R) := by
    unfold evictActive at hmem; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  by_cases hlt6 : gcs.length < 6
  · refine ReachesOrPanic.of_sepWP
      (hwp.step4a_lo sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align
        (DhCommitFacts.ult_six_of_lt_six hlt6)) hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hvregs_1, hP1⟩
    rw [evictList_of_le_five gcs (DhCommitFacts.le_five_of_lt_six hlt6)]
    have hm1_act : s1.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      unfold evictActive; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1'
    exact ReachesOrPanic.done ⟨hpc1, hrun1, hsp1, hsp_align1, htr1.trans htrace,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1.trans hx23, hx25_1.trans hx25, hx29_1, hvregs_1, hL1, hm1_act⟩
  · have hge6 : 6 ≤ gcs.length := DhCommitFacts.ge_six_of_not_lt_six hlt6
    refine ReachesOrPanic.of_sepWP
      (hwp.step4a_ge sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hx25
        (DhCommitFacts.ult_six_eq_false_of_not_lt_six hlt6 hle)) hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 hkf1 _hsym1 hL1 hm1 hpost1
    have hcl1 := hcl.of_keepsFrozen hkf1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1_act : s1.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      unfold evictActive; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1'
    refine ReachesOrPanic.seq
      (dhCommit_evict_loop_cl_placed hwp C A ctl S hMemmove hDrop x R Frame s0 sp chainsCap chainsPtr gcs
        s1 hge6 hle hpc1 hrun1 hsp1 hsp_align1 (htr1.trans htrace)
        (hx23_1.trans hx23) hx24_1 hx25_1 hx27_1 hx28_1 hcl1 hL1 hm1_act) ?_
    intro sf _ _ ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩
    exact ReachesOrPanic.done ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f.trans hx19_1, hx20_f.trans hx20_1, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
      hx23_f, hx25_f, hx29_f.trans hx29_1, hvregs_f.trans hvregs_1, hL_f, hm_f⟩

theorem s3_commit_placed_ok_cli [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec A)))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)))
    (hDropChain : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (hShim : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hDealloc : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpySpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveSpec dropChainStack))
    (hPanic : prog.externAt? (lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    CliS3CommitSeamPlaced prog entry C A ctl uuidTryParse S := by
  intro x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hS3 hL
  rcases hS3 with ⟨hpc_s, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  let newChain : ReceiverChain :=
    { senderRatchetKey := x.msg.senderRatchetKey, chainKey := some receiverChainKey, messageKeys := [] }
  let r1 : RatchetState :=
    { tr.ratchet with
      senderChain := some ⟨newSenderKey, senderChainKey⟩, rootKey := finalRootKey,
      previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1),
      receiverChains := RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
  let sp := s0.sp - 1504#64; let draws := min 32 x.rest.length
  dsimp only [trAt, ratchetAt, cliTryDecryptCommonHeapPlaced, signalMessageAt] at hm; rw [hsc] at hm
  have h_sc_50_eq : ∀ (pad : List (BitVec 8)), pad.length = 100 →
      ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) := by
    intro pad _
    rw [show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
        optSenderChainBytes_some_pointsTo (sp + 0x50#64) sc pad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _,
        chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey,
        show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _]
  let MsgCommon : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    memRegion (sp + 0xe4#64) 4 ∗ vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗
    cliTapeAfter ctl x.cur x.rest draws ∗ FromRecordCallees.lsLogOff ∗ tryDecryptSavedRegs s0.sp s0
  rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _] at hm
  have hm_pures : s.mem ⊨
      ⌜∀ sc', some sc = some sc' → Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.ciphertext.length < 2 ^ 40 ∧
        x.msg.pqRatchet.length < 2 ^ 40 ∧ x.msg.serialized.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
         (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
       ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) trG.ratchet.senderPad) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗ ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗ ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       memRegion (sp + 0x1d8#64) 0xd8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x110 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x80 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗ MsgCommon ∗
       stackAt sp tryDecryptSubStack ∗ A.pool ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm; dsimp only [sp, draws, MsgCommon]; ac_rfl
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨_hclamp_old, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨⟨hchains_len, hpad_len, hmfj⟩, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨hmsg_pure, hm_body⟩
  rw [h_sc_50_eq trG.ratchet.senderPad hpad_len] at hm_body
  have hsplit_1d8 := memRegion_split (sp + 0x1d8#64) 0x60 0x78 (by decide)
  rw [show (0x60 + 0x78 : Nat) = 0xd8 from rfl, show sp + 0x1d8#64 + 96#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hsplit_1d8
  have hsplit_2c0 := memRegion_split (sp + 0x2c0#64) 0x14 0xfc (by decide)
  rw [show (0x14 + 0xfc : Nat) = 0x110 from rfl, show sp + 0x2c0#64 + 20#64 = sp + 0x2d4#64 from add_assoc_const _ _ _ _] at hsplit_2c0
  have hsplit_440 := memRegion_split (sp + 0x440#64) 0x10 0x70 (by decide)
  rw [show (0x10 + 0x70 : Nat) = 0x80 from rfl, show sp + 0x440#64 + 16#64 = sp + 0x450#64 from add_assoc_const _ _ _ _] at hsplit_440
  have hsplit_450 := memRegion_split (sp + 0x450#64) 0x50 0x20 (by decide)
  rw [show (0x50 + 0x20 : Nat) = 0x70 from rfl, show sp + 0x450#64 + 80#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _] at hsplit_450
  have hsplit_4e0 := memRegion_split (sp + 0x4e0#64) 0x20 0x80 (by decide)
  rw [show (0x20 + 0x80 : Nat) = 0xa0 from rfl, show sp + 0x4e0#64 + 32#64 = sp + 0x500#64 from add_assoc_const _ _ _ _] at hsplit_4e0
  have hsplit_500 := memRegion_split (sp + 0x500#64) 0x60 0x20 (by decide)
  rw [show (0x60 + 0x20 : Nat) = 0x80 from rfl, show sp + 0x500#64 + 96#64 = sp + 0x560#64 from add_assoc_const _ _ _ _] at hsplit_500
  have hstk_pb := stackAt_split_from sp tryDecryptSubStack chainKeyToPbStack (by decide) (by decide)
  rw [hsplit_1d8, hsplit_2c0, hsplit_440, hsplit_450, hsplit_4e0, hsplit_500, hstk_pb] at hm_body
  let BaseFrame : SepProp :=
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗ ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x238#64) 0x78 ∗
    memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗
    memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x560#64) 0x20 ∗ MsgCommon
  let gcs0 := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hsplit_sp16 := memRegion_split sp 12 4 (by decide)
  rw [show (12 + 4 : Nat) = 0x10 from rfl, show sp + 12#64 = sp + 0xc#64 from rfl] at hsplit_sp16
  rw [hsplit_sp16] at hm_body
  let Frame12 : SepProp :=
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
    memRegion (sp + 0xc#64) 4 ∗ memRegion (sp + 0x1d8#64) 0x60 ∗ memRegion (sp + 0x500#64) 0x60 ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - chainKeyToPbStack) ∗ BaseFrame
  have hm_step12 : s.mem ⊨
      (memRegion sp 12 ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗ ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x440#64) 16 ∗
       memRegion (sp + 0x4e0#64) 32 ∗ ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       A.pool ∗ stackAt sp chainKeyToPbStack) ∗ (Frame12 ∗ R) := by
    dsimp only [Frame12, BaseFrame]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_body
  have hreach12 := dhCommit_step1_2_cl_placed hwp C A ctl S hPkSer hShim hAlloc hPanic hMemcpy hToPb
    x R Frame12 s0 s sp x.msgA sc.chainKey.index tr.ratchet.previousCounter
    finalRootKey senderChainKey receiverChainKey x.msg.senderRatchetKey
    hpc_s hrun hsp hsp_align htr hx22 hx25 hx27 hx28 hcro.1 hL hm_step12
  dsimp only at hreach12; refine ReachesOrPanic.seq_meta hreach12 ?_
  intro s1 hkf1 _hsym1 hs1
  rcases hs1 with ⟨boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc1, hrun1, hsp1, hsp_align1,
    htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1⟩
  have hcro1 := hcro.of_keepsFrozen hkf1
  have hstk_grow := stackAt_split_from sp tryDecryptSubStack growOneStack (by decide) (by decide)
  have hsplit_1d8_32 := memRegion_split (sp + 0x1d8#64) 32 0x40 (by decide)
  rw [show (32 + 0x40 : Nat) = 0x60 from rfl, show sp + 0x1d8#64 + 32#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _] at hsplit_1d8_32
  have hjoin_1b0_72 := (memRegion_split (sp + 0x1b0#64) 40 32 (by decide)).symm
  rw [show (40 + 32 : Nat) = 72 from rfl, show sp + 0x1b0#64 + 40#64 = sp + 0x1d8#64 from add_assoc_const _ _ _ _] at hjoin_1b0_72
  have hm1_sp8 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (cell_to_memRegion_8 sp boxPtr))) hm1
  have hm1_prep : s1.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - chainKeyToPbStack) ∗
       stackAt sp chainKeyToPbStack) ∗ (memRegion (sp + 0x1b0#64) 40 ∗ memRegion (sp + 0x1d8#64) 32) ∗
      vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
      memRegion sp 8 ∗ ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
      memRegion (sp + 0x1f8#64) 0x40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 0x60 ∗ ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗ A.pool ∗ BaseFrame ∗ R := by
    dsimp only [Frame12] at hm1_sp8; rw [hsplit_1d8_32] at hm1_sp8
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1_sp8
  rw [← hstk_pb, hstk_grow, hjoin_1b0_72, vecAt_chains_eq] at hm1_prep
  let Frame3 : SepProp :=
    memRegion sp 8 ∗ ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗ memRegion (sp + 0x1f8#64) 0x40 ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x500#64) 0x60 ∗ ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - growOneStack) ∗ BaseFrame
  let Step3Rest : SepProp :=
    ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗ memRegion (sp + 0x1b0#64) 72 ∗
    (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
    (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
    optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗ Frame3
  have hgcs0_len : gcs0.length < 2 ^ 32 := by
    dsimp only [gcs0]; rw [List.length_zip, hchains_len, Nat.min_self]; exact hrc_len
  have hreach3 : ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s1 (fun sf =>
      ∃ cap' ptr' : BitVec 64, sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
        sf.trace = s0.trace ∧ sf.readReg64 .x19 = s1.readReg64 .x19 ∧ sf.readReg64 .x20 = s1.readReg64 .x20 ∧
        sf.readReg64 .x21 = s1.readReg64 .x21 ∧ sf.readReg64 .x22 = s1.readReg64 .x22 ∧
        sf.readReg64 .x23 = s1.readReg64 .x23 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s1.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s1 ∧ prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨ (((sp + 0x38#64) ↦₆₄ cap') ∗ ((sp + 0x40#64) ↦₆₄ ptr') ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]).length) ∗
          vecBuf A 104 8 (chainAt A) cap' ptr' (gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]) ∗
          memRegion (sp + 0x190#64) 104 ∗ A.pool ∗ stackAt sp growOneStack) ∗ (Frame3 ∗ R))) := by
    refine ReachesOrPanic.seq (dhCommit_step3a_cl_placed hwp C A ctl S hGrowOne x R Step3Rest s0 s1 sp
      trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 hgcs0_len hpc1 hrun1 hsp1 hsp_align1 htr1 hcro1.1 hL1
      (by dsimp only [Step3Rest, Frame3]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1_prep)) ?_
    rintro s1b _ _ ⟨cap1, ptr1, hlt1, hpc1b, hrun1b, hsp1b, hspa1b, htr1b,
      hx19b, hx20b, hx21b, hx22b, hx23b, hx24b, hx25b, hx26b, hx27b, hx28b, hx29b, hvrb, hL1b, hm1b⟩
    exact dhCommit_step3b_of_wp tryDecryptPlacedImg C A ctl S hwp.step3b hDealloc
      x R Frame3 s0 s1 s1b sp cap1 ptr1 boxPtr srkPtr ckPtr gcs0 x.msg.senderRatchetKey receiverChainKey pad
      hlt1 hpad hsrk0 hpc1b hrun1b hsp1b hspa1b htr1b
      hx19b hx20b hx21b hx22b hx23b hx24b hx25b hx26b hx27b hx28b hx29b hvrb hx25_1 hx26_1 hx27_1 hx28_1 hL1b hm1b
  refine ReachesOrPanic.seq_meta hreach3 ?_
  intro s2 hkf2 _hsym2 hs2
  rcases hs2 with ⟨cap', ptr', hpc2, hrun2, hsp2, hsp_align2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx29_2, hvregs_2, hL2, hm2⟩
  have hcro2 := hcro1.of_keepsFrozen hkf2
  let gcs1 := gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]
  have hstk_drop := stackAt_split_from sp tryDecryptSubStack dropChainStack (by decide) (by decide)
  have hjoin_1f8 := (memRegion_split (sp + 0x1f8#64) 0x40 0x78 (by decide)).symm
  rw [show (0x40 + 0x78 : Nat) = 0xb8 from rfl, show sp + 0x1f8#64 + 64#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hjoin_1f8
  have hck_94 := (chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey).symm
  rw [show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _] at hck_94
  let TailFrame : SepProp :=
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗ MsgCommon
  let Step5Cells : SepProp :=
    memRegion sp 8 ∗ ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1f8#64) 0xb8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x450#64) 0x50 ∗ memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x560#64) 0x20
  let Frame4 : SepProp :=
    ((sp + 0x38#64) ↦₆₄ cap') ∗ Step5Cells ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - dropChainStack) ∗ TailFrame
  have hm_step4 : s2.mem ⊨ evictActive A sp cap' ptr' gcs1 ∗ (Frame4 ∗ R) := by
    have hm2_prep : s2.mem ⊨
        (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - growOneStack) ∗
         stackAt sp growOneStack) ∗ (memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x238#64) 0x78) ∗
        (((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) ∗
        ((sp + 0x38#64) ↦₆₄ cap') ∗ ((sp + 0x40#64) ↦₆₄ ptr') ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs1.length) ∗ vecBuf A 104 8 (chainAt A) cap' ptr' gcs1 ∗
        memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x500#64) 96 ∗ memRegion sp 8 ∗ A.pool ∗
        ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
        ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
        ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
        ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
        memRegion (sp + 0x450#64) 0x50 ∗ memRegion (sp + 0x4a0#64) 0x20 ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
        ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
        ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
        memRegion (sp + 0x560#64) 0x20 ∗ TailFrame ∗ R := by
      dsimp only [Frame3, BaseFrame, TailFrame] at hm2 ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2
    rw [← hstk_grow, hstk_drop, hjoin_1f8, hck_94] at hm2_prep
    dsimp only [evictActive, Frame4, Step5Cells]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm2_prep
  have hgcs1_len : gcs1.length = tr.ratchet.receiverChains.length + 1 := by
    dsimp only [gcs1, gcs0]; rw [List.length_append, List.length_zip, hchains_len, Nat.min_self]; rfl
  have hle4 : gcs1.length ≤ 2 ^ 32 := DhCommitFacts.le_of_eq_succ_lt hgcs1_len hrc_len
  have hreach4 := dhCommit_step4_cl_placed hwp C A ctl S hMemmove hDropChain
    x R Frame4 s0 s2 sp cap' ptr' gcs1 hle4 hpc2 hrun2 hsp2 hsp_align2 htr2
    (by reg_chain) hx25_2 hcro2.1 hL2 hm_step4
  refine ReachesOrPanic.seq_meta hreach4 ?_
  intro s3 hkf3 _hsym3 hs3
  rcases hs3 with ⟨hpc3, hrun3, hsp3, hsp_align3, htr3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx29_3, hvregs_3, hL3, hm3⟩
  have hcro3 := hcro2.of_keepsFrozen hkf3
  let Frame5 : SepProp :=
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
    A.pool ∗ stackAt sp tryDecryptSubStack ∗ TailFrame
  have hm_step5 : s3.mem ⊨
      memRegion sp 8 ∗ ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗ ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗ memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗ ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗ memRegion (sp + 0x560#64) 0x20 ∗ (Frame5 ∗ R) := by
    dsimp only [evictActive, Frame4, Step5Cells, Frame5] at hm3 ⊢
    rw [vecAt_chains_eq, hstk_drop]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm3
  refine ReachesOrPanic.seq_meta (dhCommit_step5_placed hwp C A ctl S x trG.ratchet.senderPad sc
    receiverChainKey newSenderKey senderChainKey msgW Frame5 R s0 s3 sp rfl hpad_len
    hpc3 hrun3 hsp3 hsp_align3 hx25_3 hL3 hm_step5) ?_
  rintro sf hkf_f _hsym_f ⟨hpcf, hrunf, hspf, hsp_alignf, htrf,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, _hx30f, hvregsf, _hLf, hmf⟩
  have hcro_f := hcro3.of_keepsFrozen hkf_f
  let trG' : TrGhost :=
    { trG with ratchet := { trG.ratchet with chainsCap := cap', chainsPtr := ptr', chains := (evictGcs gcs1).map Prod.fst } }
  refine ⟨sf, .refl sf, Or.inl ⟨trG', ?_⟩⟩
  dsimp only [ConsumeMsgKeyStatePlaced, segConsumeMsgKeyPC_at, tryDecryptMidMetaPlaced]
  dsimp only [sp] at hx23_3
  refine ⟨hpcf, ⟨hrunf, hspf, hsp0_align, hsp_alignf, by reg_chain, htrf.trans htr3, hcro_f, by reg_chain⟩,
    hx12f, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by rw [hx24f, setWidth8_zeroExtend64_shared_lb, hmsgW], hx25f, ?_⟩
  have h_evict_snd : (evictGcs gcs1).map Prod.snd = r1.receiverChains := by
    rw [map_snd_evictGcs, map_snd_zip_append trG.ratchet.chains tr.ratchet.receiverChains
      (newChainGhost srkPtr ckPtr x.msg.senderRatchetKey) newChain hchains_len]
  have h_zip_trG' : trG'.ratchet.chains.zip r1.receiverChains = evictGcs gcs1 := by
    dsimp only [trG']; rw [← h_evict_snd, zip_map_fst_snd]
  have h_len_trG' : trG'.ratchet.chains.length = r1.receiverChains.length := by
    dsimp only [trG']; rw [← h_evict_snd, List.length_map, List.length_map]
  have h_clamp_r1 : ∀ sc', r1.senderChain = some sc' →
      Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
    intro sc' hsc'; injection hsc' with hsc'_eq; subst hsc'_eq; exact hclamp
  dsimp only [trAt, ratchetAt, cliTryDecryptCommonHeapPlaced, signalMessageAt]
  rw [h_zip_trG', show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _]
  have hmf_pures : sf.mem ⊨
      ⌜∀ sc', r1.senderChain = some sc' → Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG'.ratchet.chains.length = r1.receiverChains.length ∧ trG'.ratchet.senderPad.length = 100 ∧ r1.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.ciphertext.length < 2 ^ 40 ∧
        x.msg.pqRatchet.length < 2 ^ 40 ∧ x.msg.serialized.length < 2 ^ 40 ∧ (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) trG.ratchet.senderPad) ∗
       memRegion sp 0x20 ∗ memRegion (sp + 0x140#64) 0x170 ∗ ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗ memRegion (sp + 0x2d4#64) 0x2ac ∗ (Frame5 ∗ R)) := by
    rw [satisfies_pure_sepConj]; refine ⟨h_clamp_r1, ?_⟩
    rw [satisfies_pure_sepConj]; refine ⟨⟨h_len_trG', hpad_len, hmfj⟩, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hmsg_pure, hmf⟩
  dsimp only [Frame5, TailFrame, MsgCommon] at hmf_pures
  refine Satisfies.mono (Entails.of_eq ?_) hmf_pures
  dsimp only [sp, draws, r1, newChain, trG']; ac_rfl

theorem s3_commit_433_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (withLsCodeLoaded lsmpl (chainKeyToPbSpec A)))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpySpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove")
      (sessionMemmoveSpec dropChainStack))
    (hPanic : ((blkPC_434).rebase (blkPl_434).base H).externAt?
      (lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    CliS3CommitSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A ctl uuidTryParse S :=
  s3_commit_placed_ok_cli (dhCommitBlockWp_549 H) C A ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove hPanic

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit
