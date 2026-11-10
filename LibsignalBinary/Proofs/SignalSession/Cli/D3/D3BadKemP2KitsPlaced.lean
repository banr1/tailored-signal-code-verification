/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3PollRejectAuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5Placed
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Blocks
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPost
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Stage P2 Bad-KEM Callee & Store-Kit Bridges

Cross-block `initialize_bob_session` Bad-KEM contracts, Stage-P2 Bad-KEM spatial frames
(`p2BadKemMsgFieldsAt`, `p2BadKemSub1To4Frame`, `p2BadKemErrFrameAtPlaced`,
`stageP2BadKemPreAtPlaced`, `stageP2OverBadKemPreAtPlaced`), and the Substage P2.5 tail
(`+0x1168 → +0x125c`) on Bad-KEM.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding Bytes PqxdhHookContracts PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession.Cli.RunProofs (pkVecTag?)

/-! ## 1. Stage P2 Bad-KEM Spatial Bundles & Helpers -/

/-- Coroutine Stage-P2 scratch regions at `+0x4f8..+0x7d8` preserved identically across all exits. -/
def p2CoroScratchTailAt (coroPtr : BitVec 64) : SepProp :=
  memRegion (coroPtr + 0x4f8#64) 344 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x658#64) 298 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  memRegion (coroPtr + 0x798#64) 64

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

theorem p2_pointsToBytes_entails_memRegion (p : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (h : bs.length = n) : (p ↦ₛ bs) ⊢ memRegion p n :=
  h ▸ ProofLib.pointsToBytes_entails_memRegion p bs

theorem p2_pointsToBytes_split_head (p : BitVec 64) (bs : List (BitVec 8)) (h : 0 < bs.length) :
    (p ↦ₛ bs) = (p ↦₈ bs.getD 0 0#8) ∗ ((p + 1#64) ↦ₛ bs.drop 1) := by
  cases bs with
  | nil => cases h
  | cons b tl =>
    change (p ↦ₛ ([b] ++ tl)) = (p ↦₈ b) ∗ ((p + 1#64) ↦ₛ tl)
    rw [pointsToBytes_append]
    simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton]

theorem p2_pqsk_split_rejoin (p : BitVec 64) (bs : List (BitVec 8)) (h : 0 < bs.length) :
    (p ↦₈ bs.getD 0 0#8) ∗ ((p + 1#64) ↦ₛ bs.drop 1) = (p ↦ₛ bs) :=
  (p2_pointsToBytes_split_head p bs h).symm

theorem p2_coro398_cells8_4_eq_96 (coroPtr : BitVec 64) :
    cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 =
      memRegion (coroPtr + 0x398#64) 96 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide),
      ← ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide),
      ← ProofLib.memRegion_split' (b := coroPtr + 0x398#64) (n := 64) (k := 32)
          (b' := coroPtr + 0x3d8#64) rfl (by bv_omega) (by decide)]

theorem p2_coro4f8_2cells_328_eq_344 (coroPtr : BitVec 64) :
    cells (coroPtr + 0x4f8#64) 2 ∗ memRegion (coroPtr + 0x508#64) 328 =
      memRegion (coroPtr + 0x4f8#64) 344 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x4f8#64) 2 (by decide),
      ← ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 16) (k := 328)
          (b' := coroPtr + 0x508#64) rfl (by bv_omega) (by decide)]

theorem p2_sp3b0_8_40_eq_48 (sp : BitVec 64) :
    memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 40 =
      memRegion (sp + 0x3b0#64) 48 :=
  (ProofLib.memRegion_split' (b := sp + 0x3b0#64) (n := 8) (k := 40)
    (b' := sp + 0x3b8#64) rfl (by bv_omega) (by decide)).symm

theorem p2_memRegion_a90_288_split_65_223 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 288 =
      memRegion (sp + 0xa90#64) 65 ∗ memRegion (sp + 0xad1#64) 223 :=
  ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 65) (k := 223)
    (b' := sp + 0xad1#64) rfl (by bv_omega) (by decide)

/-- Optional OPK secret-key bytes for `AcceptKeysInput` (`some (toU8 opkSkBytes)` when `opkId?`
is `some _`, `none` when `none`). -/
def opkOkSkBytes? : Option (BitVec 32) → List (BitVec 8) → Option SignalPqxdh.Bytes
  | some _, skB => some (toU8 skB)
  | none, _ => none

/-- Construct `AcceptKeysInput` from wire `HandshakeHdr`, Bob's 32-byte identity keypair bytes
`(ikBSk, ikBPk)`, and the store-resolved SPK, Kyber1024, and optional OPK key bytes. -/
def mkP2AcceptKeysInput (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    AcceptKeysInput where
  ikBSk := ikBSk
  ikBPk := ikBPk
  spkBSk := toU8 (clampBv8List spkPrivBytes)
  spkBPk := toU8 spkPubBytes
  opkBSk? := opkOkSkBytes? (hdrOpkIdBv? hdr) opkSkBytes
  pqspkBSk := toU8 kyberPrivBytes
  pqspkBPk := toU8 kyberPubBytes
  trustedPeer := true
  replayOk := true
  hdr := hdr

/-- Read-only `PreKeySignalMessage` fields accessed during Stage P2 with arbitrary Kyber ciphertext
slice `(ctBufPtr, ctBytes)`. -/
def p2BadKemMsgFieldsAt (msgPtr ctBufPtr : BitVec 64) (hdr : HandshakeHdr)
    (ctBytes : List (BitVec 8)) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) : SepProp :=
  ((msgPtr + 112#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗
  ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
  ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
  ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
  ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
  ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
  ((msgPtr + 200#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 232#64) ↦₃₂ remoteRegId) ∗
  ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗
  ((msgPtr + 240#64) ↦₈ 4#8) ∗
  (ctBufPtr ↦ₛ ctBytes)

/-- Frame held constant across `stageP2_sub1_to_4_kits` and `Over.stageP2_over_sub1_to_4_kits`
when the Kyber ciphertext slice is `(ctBufPtr, ctBytes)`. -/
def p2BadKemSub1To4Frame (A : RustAlloc) {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte : BitVec 8) (remoteRegId : BitVec 32)
    (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  memRegion (coroPtr + 1288#64) 328 ∗
  memRegion (coroPtr + 1616#64) 8 ∗
  memRegion (coroPtr + 1624#64) 298 ∗
  memRegion (coroPtr + 1928#64) 16 ∗
  memRegion (coroPtr + 1944#64) 64 ∗
  ((msgPtr + 112#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
  ((msgPtr + 200#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 232#64) ↦₃₂ remoteRegId) ∗
  (ctBufPtr ↦ₛ ctBytes) ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗
  ((sp + 136#64) ↦₆₄ u_88) ∗
  memRegion (sp + 928#64) 8 ∗
  memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 952#64) 40 ∗
  cells (sp + 1376#64) 4 ∗
  cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗
  memRegion (sp + 2769#64) 223 ∗
  memRegion (fp + -128#64) 9 ∗
  Frame

/-- Common coroutine, stack, message, address, and allocator spatial frame delivered uniformly at
`s0.readReg64 .x30` on all 5 Stage-P2 Bad-KEM error exits (Arms 1–5) under `[LibsignalPlacement]`. -/
def p2BadKemErrFrameAtPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 224#64) 368 ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ 1#8) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt ∗
  memRegion (coroPtr + 1160#64) 8 ∗
  memRegion (coroPtr + 1200#64) 65 ∗
  ((coroPtr + 1265#64) ↦₈ 0#8) ∗
  ((coroPtr + 1266#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  memRegion (sp + 128#64) 88 ∗
  memRegion (sp + 624#64) 9 ∗
  memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗
  memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗
  memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗
  cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗
  cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗
  memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

/-- Spatial precondition at `+2152` for `stageP2_pathA_badKem_kits_placed` (Path A). -/
def stageP2BadKemPreAtPlaced [LibsignalPlacement] (A : RustAlloc) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 224#64) ∗
  memRegion (coroPtr + 256#64) 336 ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ b_2c0) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  cells (coroPtr + 1016#64) 6 ∗
  cells (coroPtr + 1128#64) 4 ∗
  ((coroPtr + 1160#64) ↦₆₄ u_488) ∗
  ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 1201#64) 64 ∗
  ((coroPtr + 1265#64) ↦₈ b_4f1) ∗
  ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗ ((sp + 136#64) ↦₆₄ u_88) ∗ ((sp + 144#64) ↦₆₄ u_90) ∗
  ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
  ((sp + 168#64) ↦₆₄ u_a8) ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
  ((sp + 184#64) ↦₆₄ u_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗
  ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗ memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗ memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗ stackAt sp stk ∗ Frame

/-- Spatial precondition at `+2152` for `stageP2_over_badKem_kits_placed` (Over-Path C). -/
def stageP2OverBadKemPreAtPlaced [LibsignalPlacement] (A : RustAlloc) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateReprAt A (coroPtr + 248#64) recG sess ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ b_2c0) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  cells (coroPtr + 1016#64) 6 ∗
  cells (coroPtr + 1128#64) 4 ∗
  ((coroPtr + 1160#64) ↦₆₄ u_488) ∗
  ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 1201#64) 64 ∗
  ((coroPtr + 1265#64) ↦₈ b_4f1) ∗
  ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗ ((sp + 136#64) ↦₆₄ u_88) ∗ ((sp + 144#64) ↦₆₄ u_90) ∗
  ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
  ((sp + 168#64) ↦₆₄ u_a8) ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
  ((sp + 184#64) ↦₆₄ u_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗
  ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗ memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗ memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗ stackAt sp stk ∗ Frame

theorem bobParamsBadKemFieldsAt_intro (coroPtr msgPtr kyberKpSecPtr ctBufPtr : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : SignalPqxdh.Bytes) :
    ((coroPtr + 1624#64) ↦ₛ bytesToBv8 ikBPk) ∗ ((coroPtr + 1656#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
    ((coroPtr + 1720#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((coroPtr + 1752#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
    ((coroPtr + 1784#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((coroPtr + 1832#64) ↦₆₄ kyberKpSecPtr) ∗
    ((coroPtr + 1840#64) ↦₆₄ 3168#64) ∗ ((coroPtr + 1848#64) ↦₆₄ (msgPtr + 144#64)) ∗
    ((coroPtr + 1856#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
    opkOptFieldAt (coroPtr + 1889#64) inp.opkBSk? ∗
    (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
    ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
    ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
    ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
    (ctBufPtr ↦ₛ ctBytes) ∗ ((coroPtr + 1921#64) ↦₈ 0#8) ∗
    ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗
    ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      bobParamsBadKemFieldsAt (coroPtr + 1624#64) kyberKpSecPtr (msgPtr + 144#64) ctBufPtr
        (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 := by
  unfold bobParamsBadKemFieldsAt pqxdhAcceptBadKemFieldsAt opkPresentTag opkOptFieldAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cases inp.opkBSk? <;> ac_rfl

private theorem p2_entails_frame_v1_placed {P P₁ P₂ F Q : SepProp} (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : P₂ ∗ F ⊢ Q) : P ⊢ Q := by
  rw [hP]; exact Entails.trans (sepConj_mono_left hent) h

theorem p2_bobParamsBadKemFieldsAt_err_weaken (coroPtr msgPtr skBuf ctBufPtr : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8))
    (ikBPk spkBPk : SignalPqxdh.Bytes) (hwell : WellSizedAcceptKeysInput inp) :
    bobParamsBadKemFieldsAt (coroPtr + 1624#64) skBuf (msgPtr + 144#64) ctBufPtr
      (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ⊢
      ((coroPtr + 1832#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1840#64) ↦₆₄ 3168#64) ∗
      memRegion skBuf 3168 ∗
      ((coroPtr + 1624#64) ↦ₛ bytesToBv8 ikBPk) ∗
      ((coroPtr + 1656#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
      ((coroPtr + 1720#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 1752#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      ((coroPtr + 1784#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
      ((coroPtr + 1848#64) ↦₆₄ (msgPtr + 144#64)) ∗
      ((coroPtr + 1856#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      opkOptFieldAt (coroPtr + 1889#64) inp.opkBSk? ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
      ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
      (ctBufPtr ↦ₛ ctBytes) ∗
      ((coroPtr + 1921#64) ↦₈ 0#8) ∗
      ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗
      ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
  rw [← bobParamsBadKemFieldsAt_intro coroPtr msgPtr skBuf ctBufPtr inp ctBytes ikBPk spkBPk]
  have hlen : (bytesToBv8 inp.pqspkBSk).length = 3168 := by
    simp [bytesToBv8, hwell.2.2.2.2.2.1]
  have hm := p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hlen
  rw [← p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega)] at hm
  exact p2_entails_frame_v1_placed hm (by sep_focus) (Entails.of_eq (by ac_rfl))

theorem p2_initBobBadKemErrOwnedAt_unpack (A : RustAlloc) (sp : BitVec 64) :
    initBobBadKemErrOwnedAt A (sp + 992#64) ⊢
      ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ⌜errTag ≠ -2#64 ∧ errTag ≠ -3#64⌝ ∗
        ((sp + 992#64) ↦₆₄ -1#64) ∗
        speWordsAt (sp + 1000#64) errTag w2 w3 w4 w5 w6 ∗
        pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (sp + 1048#64) 288 := by
  dsimp only [initBobBadKemErrOwnedAt, pollReadyOkWord]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
    (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [sepConj_comm ((sp + 992#64) ↦₆₄ -1#64)]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun ⟨_, hne_pend, hne_ok⟩ => ?_
  refine Entails.pure_right ⟨hne_ok, hne_pend⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## 2. Cross-Block Bob Bad-KEM Transfers (`lsProg_75 H → callerProg` at `lsmpl.base 75`) -/

theorem initializeBobSession_badKem_errOwned_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedPlacedSpec A)) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedPlacedSpec A) := by
  have hcallee := initializeBobSession_badKem_errOwned_placed_ok_of_accept h_accept
  have hcallee_prog : IsLsBlockProg (lsProg_75 H) 75 H := inferInstance
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have hQL : (lsProg_75 H).CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcrl0.1 75 (by decide) (by decide) H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (lsProg_75 H).externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (lsProg_75 H).svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem initializeBobSession_badKem_errOwned_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A)) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept h_accept)

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting contract for `initialize_bob_session`
(Block `75`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 75`. -/
theorem initializeBobSession_badKem_errOwned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H CryptoVerification.lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (initializeBobSession_badKem_errOwned_full_placed_ok hWF hP hH h_memcpy)

theorem of_cro_badKem_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (h : subroutine_ok prog entry (initializeBobSessionBadKemErrOwnedPlacedSpec A)) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv (StoreKit.LibsignalCodeRoLoaded lsmpl)
          (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionBadKemErrOwnedPlacedSpec,
        initializeBobSessionBadKemErrOwnedInnerPlacedSpec, StoreKit.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionBadKemErrOwnedPlacedSpec,
        initializeBobSessionBadKemErrOwnedInnerPlacedSpec, StoreKit.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => hpost, fun sf hpan => hpan⟩
  dsimp only [initializeBobSessionBadKemErrOwnedPlacedSpec,
    initializeBobSessionBadKemErrOwnedInnerPlacedSpec, StoreKit.withLsCodeRoLoaded,
    withBobMemInv] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem of_frozen_badKem_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (h : subroutine_ok prog entry (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A)) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv (LibsignalFrozen lsmpl)
          (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
        initializeBobSessionBadKemErrOwnedInnerPlacedSpec, withLsFrozen] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
        initializeBobSessionBadKemErrOwnedInnerPlacedSpec, withLsFrozen] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => hpost, fun sf hpan => hpan⟩
  dsimp only [initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
    initializeBobSessionBadKemErrOwnedInnerPlacedSpec, StoreKit.withLsCodeRoLoaded,
    withBobMemInv, withLsFrozen] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-! ## 3. Placed Substage P2.5 Tail (`+0x1168 → +0x125c`) on Bad-KEM -/

section Sub5BadKemPlaced

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

set_option maxHeartbeats 1200000 in
/-- Substage P2.5 tail (`+0x1168 → +0x125c` Arm 5) on Bad-KEM: executes `is_same_account`
and `initialize_bob_session` under `pkVecTag? 8 1568 ctBytes = none`, exiting via Arm 5
(`hErrBob`). -/
theorem stageP2_sub5_tail_badKem_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {A : RustAlloc}
    (ext : String → Option (State → State))
    {sameStk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse sameStk)))
    (hInitBobBadKemErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (StoreKit.withLsCodeRoLoaded lsmpl
          (withBobMemInv Φ (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))))
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost)
    (s0 s6 : State) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
     kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
     u_950 u_958 u_960 u_968
     opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 : BitVec 64)
    (opkId : BitVec 32) (opk_b64 b_4f1 : BitVec 8)
    (stk : Nat) (F_rest : SepProp)
    (htrusted : inp.trustedPeer = true) (hreplay : inp.replayOk = true)
    (hopk_match : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hct_bd : ctBytes.length < 2 ^ 63)
    (hbadKem : pkVecTag? 8#8 1568 ctBytes = none)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hikB0 : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ikBPk) =
      ((a + 0#64) ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗
      ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hikB1 : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 inp.ikBSk) =
      ((a + 0#64) ↦₆₄ ik4) ∗ ((a + 8#64) ↦₆₄ ik5) ∗
      ((a + 16#64) ↦₆₄ ik6) ∗ ((a + 24#64) ↦₆₄ ik7))
    (hopk : ∀ a : BitVec 64,
      (a ↦₈ opkPresentTag inp.opkBSk?) ∗ ((a + 1#64) ↦ₛ opkPkBytes) ∗
        ((a + 33#64) ↦ₛ opkSkBytes) =
      ((a + 0#64) ↦₆₄ opk0) ∗ ((a + 8#64) ↦₆₄ opk1) ∗ ((a + 16#64) ↦₆₄ opk2) ∗
      ((a + 24#64) ↦₆₄ opk3) ∗ ((a + 32#64) ↦₆₄ opk4) ∗ ((a + 40#64) ↦₆₄ opk5) ∗
      ((a + 48#64) ↦₆₄ opk6) ∗ ((a + 56#64) ↦₆₄ opk7) ∗ ((a + 64#64) ↦₈ opk_b64))
    (hsame_le : sameStk ≤ stk)
    (herr_le : 768 + pqxdhEntryStack ≤ stk)
    (hstk_lt : stk ≤ sp.toNat)
    (hCode6 : Φ s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0x1168#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr6 : s0.trace <+: s6.trace)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx0_6 : s6.readReg64 .x0 = coroPtr + 1944#64)
    (hx1_6 : s6.readReg64 .x1 = localAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 200#64)
    (hx3_6 : s6.readReg64 .x3 = remoteAddrPtr)
    (hx8_6 : s6.readReg64 .x8 = opk_b64.zeroExtend 64)
    (hx9_6 : s6.readReg64 .x9 = msgPtr)
    (hx10_6 : s6.readReg64 .x10 = coroPtr + 1944#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = msgPtr + 144#64)
    (hx22_6 : s6.readReg64 .x22 = sp + 880#64)
    (hx23_6 : s6.readReg64 .x23 = sp + 2352#64)
    (hx24_6 : s6.readReg64 .x24 = coroPtr + 920#64)
    (hx28_6 : s6.readReg64 .x28 = sp + 2704#64)
    (hx29_6 : s6.readReg64 .x29 = fp)
    (hErrBob : ∀ (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State),
      errTag ≠ -2#64 → errTag ≠ -3#64 →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 144#64 →
      sf.readReg64 .x22 = sp + 880#64 → sf.readReg64 .x23 = sp + 2352#64 →
      sf.readReg64 .x24 = coroPtr + 920#64 → sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 → sf.readReg64 .x28 = sp + 2704#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 992#64) ↦₆₄ -1#64) ∗
         speWordsAt (sp + 1000#64) errTag w2 w3 w4 w5 w6 ∗
         pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
         memRegion (sp + 1048#64) 288 ∗
         bobParamsBadKemFieldsAt (coroPtr + 1624#64) kyberKpSecPtr (msgPtr + 144#64) ctBufPtr
           (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ∗
         ((coroPtr + 984#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
         ((coroPtr + 1000#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
         ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
         ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1688#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 1816#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 1824#64) ↦₆₄ 1568#64) ∗
         ((coroPtr + 1857#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 1889#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 1944#64) 64 ∗ ((msgPtr + 124#64) ↦₃₂ opkId) ∗
         ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
         cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (((coroPtr + 1944#64) ↦₆₄ ik0) ∗ ((coroPtr + 1952#64) ↦₆₄ ik1) ∗
       ((coroPtr + 1960#64) ↦₆₄ ik2) ∗ ((coroPtr + 1968#64) ↦₆₄ ik3) ∗
       ((coroPtr + 1976#64) ↦₆₄ ik4) ∗ ((coroPtr + 1984#64) ↦₆₄ ik5) ∗
       ((coroPtr + 1992#64) ↦₆₄ ik6) ∗ ((coroPtr + 2000#64) ↦₆₄ ik7) ∗
       ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 984#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
       ((coroPtr + 1000#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
       ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
       ((coroPtr + 1200#64) ↦₆₄ opk0) ∗ ((coroPtr + 1208#64) ↦₆₄ opk1) ∗
       ((coroPtr + 1216#64) ↦₆₄ opk2) ∗ ((coroPtr + 1224#64) ↦₆₄ opk3) ∗
       ((coroPtr + 1232#64) ↦₆₄ opk4) ∗ ((coroPtr + 1240#64) ↦₆₄ opk5) ∗
       ((coroPtr + 1248#64) ↦₆₄ opk6) ∗ ((coroPtr + 1256#64) ↦₆₄ opk7) ∗
       ((coroPtr + 1264#64) ↦₈ opk_b64) ∗ ((coroPtr + 1265#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 1624#64) 298 ∗ ((msgPtr + 124#64) ↦₃₂ opkId) ∗
       ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
       ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
       ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦ₛ ctBytes) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       memRegion (sp + 992#64) 65 ∗ memRegion (sp + 1057#64) 279 ∗
       ((sp + 2352#64) ↦₆₄ ik0) ∗ ((sp + 2360#64) ↦₆₄ ik1) ∗
       ((sp + 2368#64) ↦₆₄ ik2) ∗ ((sp + 2376#64) ↦₆₄ ik3) ∗
       ((sp + 2384#64) ↦₆₄ u_950) ∗ ((sp + 2392#64) ↦₆₄ u_958) ∗
       ((sp + 2400#64) ↦₆₄ u_960) ∗ ((sp + 2408#64) ↦₆₄ u_968) ∗
       cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
       cells (sp + 2704#64) 8 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by rw [bytesToBv8_length]; exact hikBPk_len
  have hspkBPk_bv : (bytesToBv8 spkBPk).length = 32 := by rw [bytesToBv8_length]; exact hspkBPk_len
  have hspkBSk_bv : (bytesToBv8 inp.spkBSk).length = 32 := by rw [bytesToBv8_length]; exact hwell.2.2.1
  have hikAPk_bv : (bytesToBv8 inp.hdr.ikAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.1
  have hekAPk_bv : (bytesToBv8 inp.hdr.ekAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.2.1
  obtain ⟨spk0, spk1, spk2, spk3, hspkPk⟩ := exists_words4_of_len32 hspkBPk_bv
  obtain ⟨spk4, spk5, spk6, spk7, hspkSk⟩ := exists_words4_of_len32 hspkBSk_bv
  obtain ⟨ikA0, ikA1, ikA2, ikA3, hikA⟩ := exists_words4_of_len32 hikAPk_bv
  obtain ⟨ekA0, ekA1, ekA2, ekA3, hekA⟩ := exists_words4_of_len32 hekAPk_bv
  have hspk_398 :
      ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗
        ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      ((coroPtr + 920#64) ↦₆₄ spk0) ∗ ((coroPtr + 928#64) ↦₆₄ spk1) ∗
      ((coroPtr + 936#64) ↦₆₄ spk2) ∗ ((coroPtr + 944#64) ↦₆₄ spk3) ∗
      ((coroPtr + 952#64) ↦₆₄ spk4) ∗ ((coroPtr + 960#64) ↦₆₄ spk5) ∗
      ((coroPtr + 968#64) ↦₆₄ spk6) ∗ ((coroPtr + 976#64) ↦₆₄ spk7) := by
    rw [hspkPk (coroPtr + 920#64), hspkSk (coroPtr + 952#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hekA_msg : ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) =
      ((msgPtr + 168#64) ↦₆₄ ekA0) ∗ ((msgPtr + 176#64) ↦₆₄ ekA1) ∗
      ((msgPtr + 184#64) ↦₆₄ ekA2) ∗ ((msgPtr + 192#64) ↦₆₄ ekA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hekA (msgPtr + 168#64)
  have hikA_msg : ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) =
      ((msgPtr + 200#64) ↦₆₄ ikA0) ∗ ((msgPtr + 208#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 216#64) ↦₆₄ ikA2) ∗ ((msgPtr + 224#64) ↦₆₄ ikA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hikA (msgPtr + 200#64)
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion65_eq_words8_byte (sp + 992#64)))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_420 => SepWPp.exists_elim fun u_3e0 =>
    SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 =>
    SepWPp.exists_elim fun u_3f8 => SepWPp.exists_elim fun u_400 =>
    SepWPp.exists_elim fun u_408 => SepWPp.exists_elim fun u_410 =>
    SepWPp.exists_elim fun u_418 => ?_
  have hca90 : cells (sp + 2704#64) 8 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ((sp + 2704#64) ↦₆₄ u0) ∗ ((sp + 2712#64) ↦₆₄ u1) ∗
        ((sp + 2720#64) ↦₆₄ u2) ∗ ((sp + 2728#64) ↦₆₄ u3) ∗
        ((sp + 2736#64) ↦₆₄ u4) ∗ ((sp + 2744#64) ↦₆₄ u5) ∗
        ((sp + 2752#64) ↦₆₄ u6) ∗ ((sp + 2760#64) ↦₆₄ u7)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hca90) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 =>
    SepWPp.exists_elim fun u_aa0 => SepWPp.exists_elim fun u_aa8 =>
    SepWPp.exists_elim fun u_ab0 => SepWPp.exists_elim fun u_ab8 =>
    SepWPp.exists_elim fun u_ac0 => SepWPp.exists_elim fun u_ac8 => ?_
  have hc560 : cells (sp + 1376#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 1376#64) ↦₆₄ u0) ∗ ((sp + 1384#64) ↦₆₄ u1) ∗
        ((sp + 1392#64) ↦₆₄ u2) ∗ ((sp + 1400#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc560) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_560 => SepWPp.exists_elim fun u_568 =>
    SepWPp.exists_elim fun u_570 => SepWPp.exists_elim fun u_578 => ?_
  have hc6a0 : cells (sp + 1696#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 1696#64) ↦₆₄ u0) ∗ ((sp + 1704#64) ↦₆₄ u1) ∗
        ((sp + 1712#64) ↦₆₄ u2) ∗ ((sp + 1720#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc6a0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_6a0 => SepWPp.exists_elim fun u_6a8 =>
    SepWPp.exists_elim fun u_6b0 => SepWPp.exists_elim fun u_6b8 => ?_
  have hc7e0 : cells (sp + 2016#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 2016#64) ↦₆₄ u0) ∗ ((sp + 2024#64) ↦₆₄ u1) ∗
        ((sp + 2032#64) ↦₆₄ u2) ∗ ((sp + 2040#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc7e0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_7e0 => SepWPp.exists_elim fun u_7e8 =>
    SepWPp.exists_elim fun u_7f0 => SepWPp.exists_elim fun u_7f8 => ?_
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  have hstep7 := p2_seg5c3_ext_placed_wp ext s6 coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyberKpPubPtr 1568#64 kyberKpSecPtr 3168#64
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578 u_6a0 u_6a8 u_6b0 u_6b8 u_7e0 u_7e8 u_7f0 u_7f8
    opk_b64 u_420 b_4f1
    hpc6 hrun6 hsp6_align hx0_6 hx1_6 hx2_6 hx3_6 hx8_6 hx9_6 hx10_6 hx19_6
    (by rw [hx22_6, hsp6]) (by rw [hx23_6, hsp6]) hx24_6 (by rw [hx28_6, hsp6])
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode6
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep7)
    (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx1_7, hx2_7, hx3_7, hx19_7, hx21_7, hx22_7, hx23_7,
    hx24_7, hx25_7, hx26_7, _, hx28_7, hx29_7, hx30_7, hvregs7_6⟩
  have hsp7 : s7.sp = sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  let localIk : IdentityKey := ⟨⟨⟨bytesToBv8 ikBPk, hikBPk_bv⟩⟩⟩
  let remoteIk : IdentityKey := ⟨⟨⟨bytesToBv8 inp.hdr.ikAPk, hikAPk_bv⟩⟩⟩
  have hneq' : localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes :=
    hneq.imp
      (fun h => identityKey_ne_of_bytes_ne hikBPk_bv hikAPk_bv
        (fun h_eq => h (congrArg bytesToBv8 h_eq))) id
  have hlocIk_eq : ((coroPtr + 1944#64) ↦₆₄ ik0) ∗ ((coroPtr + 1952#64) ↦₆₄ ik1) ∗
      ((coroPtr + 1960#64) ↦₆₄ ik2) ∗ ((coroPtr + 1968#64) ↦₆₄ ik3) =
      ((coroPtr + 1944#64) ↦ₛ localIk.publicKey.bytes.toList) := by
    change _ = ((coroPtr + 1944#64) ↦ₛ bytesToBv8 ikBPk)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 1944#64)).symm
  have hremIk_eq : ((msgPtr + 200#64) ↦₆₄ ikA0) ∗ ((msgPtr + 208#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 216#64) ↦₆₄ ikA2) ∗ ((msgPtr + 224#64) ↦₆₄ ikA3) =
      ((msgPtr + 200#64) ↦ₛ remoteIk.publicKey.bytes.toList) :=
    hikA_msg.symm
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hremIk_eq) (by sep_focus) ?_
  have hstk_same := p2_stackAt_split_of_le sp stk sameStk hsame_le hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same) (by sep_focus) ?_
  simp only [arm64_norm] at hpc7
  refine p2_call_nopanic_lscl_steps_frame_placed
    (x := (coroPtr + 1944#64, localIk, localAddrPtr, gMe,
           msgPtr + 200#64, remoteIk, remoteAddrPtr, gPeer))
    (R_pure := s7.readReg64 .x0 = coroPtr + 1944#64 ∧ s7.readReg64 .x1 = localAddrPtr ∧
          s7.readReg64 .x2 = msgPtr + 200#64 ∧ s7.readReg64 .x3 = remoteAddrPtr ∧
          (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes))
    (T := ((coroPtr + 1944#64) ↦ₛ localIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gMe localAddrPtr ∗
          ((msgPtr + 200#64) ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gPeer remoteAddrPtr ∗ stackAt sp sameStk)
    (hInv.toCodeRo hCode7) hSameAcct hpc7 hrun7 hsp7_al hx30_7
    (by dsimp only [isSameAccountDistinctAtSpec]; rw [hsp7])
    ⟨hx0_7, hx1_7, hx2_7, hx3_7, hneq'⟩ (by sep_focus)
    (hnext := fun s8 hst78 hpc8 hrun8 hsp8_7 _ hcs8 _ => ?_)
  dsimp only [isSameAccountDistinctAtSpec]; rw [hsp7]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_8_lo, htr8_7⟩ => ?_
  have hCode8 : Φ s8.mem := hInv.of_keepsFrozen hCode7 hst78.keepsFrozen
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, hx21_cs8, hx22_cs8, hx23_cs8, hx24_cs8, hx25_cs8, hx26_cs8, _,
    hx28_cs8, hx29_cs8, hvregscs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx21_8 : s8.readReg64 .x21 = msgPtr + 144#64 := by rw [hx21_cs8, hx21_7, hx21_6]
  have hx22_8 : s8.readReg64 .x22 = s8.sp + 880#64 := by rw [hx22_cs8, hx22_7, hsp8]
  have hx23_8 : s8.readReg64 .x23 = s8.sp + 2352#64 := by rw [hx23_cs8, hx23_7, hsp8]
  have hx24_8 : s8.readReg64 .x24 = coroPtr + 920#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s6.readReg64 .x25 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = s6.readReg64 .x26 := hx26_cs8.trans hx26_7
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 2704#64 := by rw [hx28_cs8, hx28_7, hsp8]
  have hx29_8 : s8.readReg64 .x29 = fp := by rw [hx29_cs8, hx29_7, hx29_6]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq.symm) (by sep_focus) ?_
  have hremIk_fold : ((msgPtr + 200#64) ↦ₛ remoteIk.publicKey.bytes.toList) =
      ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := rfl
  refine SepWPp.weaken_frame (Entails.of_eq hremIk_fold) (by sep_focus) ?_
  have h798_64 : ((coroPtr + 1944#64) ↦₆₄ ik0) ∗ ((coroPtr + 1952#64) ↦₆₄ ik1) ∗
      ((coroPtr + 1960#64) ↦₆₄ ik2) ∗ ((coroPtr + 1968#64) ↦₆₄ ik3) ∗
      ((coroPtr + 1976#64) ↦₆₄ ik4) ∗ ((coroPtr + 1984#64) ↦₆₄ ik5) ∗
      ((coroPtr + 1992#64) ↦₆₄ ik6) ∗ ((coroPtr + 2000#64) ↦₆₄ ik7) ⊢
      memRegion (coroPtr + 1944#64) 64 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words8_entails_memRegion64 (coroPtr + 1944#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
  refine SepWPp.weaken_frame h798_64 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398.symm) (by sep_focus) ?_
  have hopk_4b0_symm :
      ((coroPtr + 1200#64) ↦₆₄ opk0) ∗ ((coroPtr + 1208#64) ↦₆₄ opk1) ∗
      ((coroPtr + 1216#64) ↦₆₄ opk2) ∗ ((coroPtr + 1224#64) ↦₆₄ opk3) ∗
      ((coroPtr + 1232#64) ↦₆₄ opk4) ∗ ((coroPtr + 1240#64) ↦₆₄ opk5) ∗
      ((coroPtr + 1248#64) ↦₆₄ opk6) ∗ ((coroPtr + 1256#64) ↦₆₄ opk7) ∗
      ((coroPtr + 1264#64) ↦₈ opk_b64) =
      ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 1233#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 1200#64)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0_symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro658_298_eq coroPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_781 => SepWPp.exists_elim fun c_780 => ?_
  have hc658 : cells (coroPtr + 1624#64) 37 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
       ∃∗ c18 : BitVec 64, ∃∗ c19 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c22 : BitVec 64, ∃∗ c23 : BitVec 64,
       ∃∗ c24 : BitVec 64, ∃∗ c25 : BitVec 64, ∃∗ c26 : BitVec 64, ∃∗ c27 : BitVec 64, ∃∗ c28 : BitVec 64, ∃∗ c29 : BitVec 64,
       ∃∗ c30 : BitVec 64, ∃∗ c31 : BitVec 64, ∃∗ c32 : BitVec 64, ∃∗ c33 : BitVec 64, ∃∗ c34 : BitVec 64, ∃∗ c35 : BitVec 64, ∃∗ c36 : BitVec 64,
        ((coroPtr + 1624#64) ↦₆₄ c0) ∗ ((coroPtr + 1632#64) ↦₆₄ c1) ∗ ((coroPtr + 1640#64) ↦₆₄ c2) ∗
        ((coroPtr + 1648#64) ↦₆₄ c3) ∗ ((coroPtr + 1656#64) ↦₆₄ c4) ∗ ((coroPtr + 1664#64) ↦₆₄ c5) ∗
        ((coroPtr + 1672#64) ↦₆₄ c6) ∗ ((coroPtr + 1680#64) ↦₆₄ c7) ∗ ((coroPtr + 1688#64) ↦₆₄ c8) ∗
        ((coroPtr + 1696#64) ↦₆₄ c9) ∗ ((coroPtr + 1704#64) ↦₆₄ c10) ∗ ((coroPtr + 1712#64) ↦₆₄ c11) ∗
        ((coroPtr + 1720#64) ↦₆₄ c12) ∗ ((coroPtr + 1728#64) ↦₆₄ c13) ∗ ((coroPtr + 1736#64) ↦₆₄ c14) ∗
        ((coroPtr + 1744#64) ↦₆₄ c15) ∗ ((coroPtr + 1752#64) ↦₆₄ c16) ∗ ((coroPtr + 1760#64) ↦₆₄ c17) ∗
        ((coroPtr + 1768#64) ↦₆₄ c18) ∗ ((coroPtr + 1776#64) ↦₆₄ c19) ∗ ((coroPtr + 1784#64) ↦₆₄ c20) ∗
        ((coroPtr + 1792#64) ↦₆₄ c21) ∗ ((coroPtr + 1800#64) ↦₆₄ c22) ∗ ((coroPtr + 1808#64) ↦₆₄ c23) ∗
        ((coroPtr + 1816#64) ↦₆₄ c24) ∗ ((coroPtr + 1824#64) ↦₆₄ c25) ∗ ((coroPtr + 1832#64) ↦₆₄ c26) ∗
        ((coroPtr + 1840#64) ↦₆₄ c27) ∗ ((coroPtr + 1848#64) ↦₆₄ c28) ∗ ((coroPtr + 1856#64) ↦₆₄ c29) ∗
        ((coroPtr + 1864#64) ↦₆₄ c30) ∗ ((coroPtr + 1872#64) ↦₆₄ c31) ∗ ((coroPtr + 1880#64) ↦₆₄ c32) ∗
        ((coroPtr + 1888#64) ↦₆₄ c33) ∗ ((coroPtr + 1896#64) ↦₆₄ c34) ∗ ((coroPtr + 1904#64) ↦₆₄ c35) ∗
        ((coroPtr + 1912#64) ↦₆₄ c36)) := by
    simp (config := { maxSteps := 1000000 }) only
      [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
       sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc658) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_658 => SepWPp.exists_elim fun c_660 => SepWPp.exists_elim fun c_668 =>
    SepWPp.exists_elim fun c_670 => SepWPp.exists_elim fun c_678 => SepWPp.exists_elim fun c_680 =>
    SepWPp.exists_elim fun c_688 => SepWPp.exists_elim fun c_690 => SepWPp.exists_elim fun c_698 =>
    SepWPp.exists_elim fun c_6a0 => SepWPp.exists_elim fun c_6a8 => SepWPp.exists_elim fun c_6b0 =>
    SepWPp.exists_elim fun c_6b8 => SepWPp.exists_elim fun c_6c0 => SepWPp.exists_elim fun c_6c8 =>
    SepWPp.exists_elim fun c_6d0 => SepWPp.exists_elim fun c_6d8 => SepWPp.exists_elim fun c_6e0 =>
    SepWPp.exists_elim fun c_6e8 => SepWPp.exists_elim fun c_6f0 => SepWPp.exists_elim fun c_6f8 =>
    SepWPp.exists_elim fun c_700 => SepWPp.exists_elim fun c_708 => SepWPp.exists_elim fun c_710 =>
    SepWPp.exists_elim fun c_718 => SepWPp.exists_elim fun c_720 => SepWPp.exists_elim fun c_728 =>
    SepWPp.exists_elim fun c_730 => SepWPp.exists_elim fun c_738 => SepWPp.exists_elim fun c_740 =>
    SepWPp.exists_elim fun c_748 => SepWPp.exists_elim fun c_750 => SepWPp.exists_elim fun c_758 =>
    SepWPp.exists_elim fun c_760 => SepWPp.exists_elim fun c_768 => SepWPp.exists_elim fun c_770 =>
    SepWPp.exists_elim fun c_778 => ?_
  have hstep9 := p2_seg5d_ext_placed_wp ext s8 coroPtr (msgPtr + 144#64) (s8.readReg64 .x0)
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 kyberKpPubPtr 1568#64 kyberKpSecPtr 3168#64
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690 c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0 c_6f8 c_700 c_708 c_710 c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 opk_b64 c_780 c_781
    hpc8 hrun8 hsp8_align rfl hx19_8 hx21_8 hx22_8 hx23_8 hx24_8 hx28_8
  have hx0_8_b : (s8.readReg64 .x0).setWidth 8 = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h0 := congrArg (fun v => v.getLsbD i) hx0_8_lo
    have hi32 : i < 32 := by omega
    simpa [BitVec.getLsbD_setWidth, hi, hi32] using h0
  rw [hsp8, hx0_8_b] at hstep9
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode8
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep9)
    (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx1_9, hx8_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9,
    hx25_9, hx26_9, _, hx28_9, hx29_9, hx30_9, hvregs9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  refine SepWPp.weaken_frame
    (words8_byte_entails_memRegion65 (sp + 992#64) opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      opk_b64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_65_279 sp).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 2352#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 2704#64) spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 1376#64) kyberKpPubPtr 1568#64 kyberKpSecPtr 3168#64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 1696#64) ikA0 ikA1 ikA2 ikA3)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 2016#64) ekA0 ekA1 ekA2 ekA3)
    (by sep_focus) ?_
  have hikB0_658 : ((coroPtr + 1624#64) ↦₆₄ ik0) ∗ ((coroPtr + 1632#64) ↦₆₄ ik1) ∗
      ((coroPtr + 1640#64) ↦₆₄ ik2) ∗ ((coroPtr + 1648#64) ↦₆₄ ik3) =
      ((coroPtr + 1624#64) ↦ₛ bytesToBv8 ikBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 1624#64)).symm
  have hikB1_678 : ((coroPtr + 1656#64) ↦₆₄ ik4) ∗ ((coroPtr + 1664#64) ↦₆₄ ik5) ∗
      ((coroPtr + 1672#64) ↦₆₄ ik6) ∗ ((coroPtr + 1680#64) ↦₆₄ ik7) =
      ((coroPtr + 1656#64) ↦ₛ bytesToBv8 inp.ikBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB1 (coroPtr + 1656#64)).symm
  have hspkPk_698 : ((coroPtr + 1688#64) ↦₆₄ spk0) ∗ ((coroPtr + 1696#64) ↦₆₄ spk1) ∗
      ((coroPtr + 1704#64) ↦₆₄ spk2) ∗ ((coroPtr + 1712#64) ↦₆₄ spk3) =
      ((coroPtr + 1688#64) ↦ₛ bytesToBv8 spkBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkPk (coroPtr + 1688#64)).symm
  have hspkSk_6b8 : ((coroPtr + 1720#64) ↦₆₄ spk4) ∗ ((coroPtr + 1728#64) ↦₆₄ spk5) ∗
      ((coroPtr + 1736#64) ↦₆₄ spk6) ∗ ((coroPtr + 1744#64) ↦₆₄ spk7) =
      ((coroPtr + 1720#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkSk (coroPtr + 1720#64)).symm
  have hikA_6d8 : ((coroPtr + 1752#64) ↦₆₄ ikA0) ∗ ((coroPtr + 1760#64) ↦₆₄ ikA1) ∗
      ((coroPtr + 1768#64) ↦₆₄ ikA2) ∗ ((coroPtr + 1776#64) ↦₆₄ ikA3) =
      ((coroPtr + 1752#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikA (coroPtr + 1752#64)).symm
  have hekA_6f8 : ((coroPtr + 1784#64) ↦₆₄ ekA0) ∗ ((coroPtr + 1792#64) ↦₆₄ ekA1) ∗
      ((coroPtr + 1800#64) ↦₆₄ ekA2) ∗ ((coroPtr + 1808#64) ↦₆₄ ekA3) =
      ((coroPtr + 1784#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hekA (coroPtr + 1784#64)).symm
  have hopk_740 : ((coroPtr + 1856#64) ↦₆₄ opk0) ∗ ((coroPtr + 1864#64) ↦₆₄ opk1) ∗
      ((coroPtr + 1872#64) ↦₆₄ opk2) ∗ ((coroPtr + 1880#64) ↦₆₄ opk3) ∗
      ((coroPtr + 1888#64) ↦₆₄ opk4) ∗ ((coroPtr + 1896#64) ↦₆₄ opk5) ∗
      ((coroPtr + 1904#64) ↦₆₄ opk6) ∗ ((coroPtr + 1912#64) ↦₆₄ opk7) ∗
      ((coroPtr + 1920#64) ↦₈ opk_b64) =
      ((coroPtr + 1856#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 1857#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 1889#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 1856#64)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hikB0_658) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikB1_678) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkPk_698) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkSk_6b8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_6d8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_6f8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hopk_740) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (opkSlot65_eq_optField (coroPtr + 1889#64) inp.opkBSk? opkSkBytes hopkSk_eq))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq
      (bobParamsBadKemFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ctBytes ikBPk spkBPk))
    (by sep_focus) ?_
  have htr9_6 : s9.trace = s6.trace := by rw [htr9_8, htr8_7, htr7_6]
  have htr9_0 : s0.trace <+: s9.trace := htr9_6 ▸ htr6
  have hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s0 := by
    rw [hvregs9_8, hvregscs8, hvregs7_6, hvregs6]
  simp only [arm64_norm] at hpc9
  have hstk_err := p2_stackAt_split_of_le sp stk (768 + pqxdhEntryStack) herr_le hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_err) (by sep_focus) ?_
  refine p2_call_memInv_oom_steps_frame_sub5_qpan hInv
    (x := ({ inp := inp, ctBytes := ctBytes, ikBPk := ikBPk, spkBPk := spkBPk,
             sameAccountByte := 0#8, argPtr := coroPtr + 1624#64, pqskPtr := kyberKpSecPtr,
             ctSlicePtr := msgPtr + 144#64, ctBufPtr := ctBufPtr,
             ratchetKeyPairPtr := coroPtr + 920#64, outPtr := sp + 992#64 } : InitBobBadKemGhost))
    (φ := s9.readReg64 .x0 = coroPtr + 1624#64 ∧ s9.readReg64 .x1 = coroPtr + 920#64 ∧
          s9.readReg64 .x8 = sp + 992#64 ∧ inp.trustedPeer = true ∧ inp.replayOk = true ∧
          inp.hdr.opkId?.isSome = inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput inp ∧
          ikBPk.length = 32 ∧ spkBPk.length = 32 ∧ ctBytes.length < 2 ^ 63 ∧
          pkVecTag? 8#8 1568 ctBytes = none)
    (T := bobParamsBadKemFieldsAt (coroPtr + 1624#64) kyberKpSecPtr (msgPtr + 144#64) ctBufPtr
            (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ∗ memRegion (sp + 992#64) 344 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp (768 + pqxdhEntryStack) ∗ A.pool)
    hpan hCode9 htr9_0 hInitBobBadKemErrOwned
    hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [initializeBobSessionBadKemErrOwnedInnerPlacedSpec]; rw [hsp9])
    ⟨hx0_9, hx1_9, hx8_9, htrusted, hreplay, hopk_match, hwell, hikBPk_len, hspkBPk_len,
     hct_bd, hbadKem⟩
    (by sep_focus)
    (hnext := fun sf hst9f hpcf hrunf hspf_9 _ hcsf hCodef => ?_)
  dsimp only [initializeBobSessionBadKemErrOwnedInnerPlacedSpec]
  rw [hsp9]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htrf_9 => ?_
  rcases hcsf with ⟨hx19_csf, _, hx21_csf, hx22_csf, hx23_csf, hx24_csf, hx25_csf, hx26_csf, _,
    hx28_csf, hx29_csf, hvregscsf⟩
  refine SepWPp.weaken_frame (Entails.of_eq hstk_err.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_initBobBadKemErrOwnedAt_unpack A sp) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errTag => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
    SepWPp.exists_elim fun w5 => SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_elim fun ⟨herr_ne2, herr_ne3⟩ => ?_
  have hsteps_all := hst67.trans (hst78.trans (hst89.trans hst9f))
  have herr := hErrBob errTag w2 w3 w4 w5 w6 sf herr_ne2 herr_ne3
    hsteps_all hpcf hrunf (hspf_9.trans hsp9) (htrf_9.trans htr9_6)
    (hx19_csf.trans hx19_9) (hx21_csf.trans hx21_9) (hx22_csf.trans hx22_9)
    (hx23_csf.trans hx23_9) (hx24_csf.trans hx24_9)
    (by rw [hx25_csf, hx25_9, hx25_8]) (by rw [hx26_csf, hx26_9, hx26_8])
    (hx28_csf.trans hx28_9) (by rw [hx29_csf, hx29_9, hx29_8])
    (hvregscsf.trans hvregs9) (hInv.toCodeRo hCodef)
  exact p2_sepWPp_weaken_eq herr (by sep_focus)

end Sub5BadKemPlaced

end LibsignalBinary.Proofs.SignalSession.Cli.D3
