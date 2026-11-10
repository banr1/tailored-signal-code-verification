/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Msg
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Stage P2 Bad-KEM Composition & General `v4` Message Unpack/Reassembly

Unpacks and reassembles `preKeyMsgAt` for general version-4 `PreKeySignalMessage` values
with `pm.kyberPayload = some kp`, proves Error Arms 4–5 exit bridges, and composes full
Stage P2 Bad-KEM rejection on Path A and Over-Path C when `pkVecTag? 8#8 1568 ctBytes = none`.
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
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
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
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (signalMessageRestVerAt signalMessageAt_eq_ver_sep memRegion_4_eq_exists_pointsTo32)
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced

/-! ## 1. Canonical `HandshakeHdr` & Pure Header Bridges for General `v4` Messages -/

/-- Canonical `HandshakeHdr` extracted from a general `v4` `PreKeySignalMessage` with
`pm.kyberPayload = some kp` (pairing real curve/pre-key header fields with a dummy 1568-byte
`kemCt` placeholder for `WellSizedAcceptKeysInput`). -/
def mkBadKemHdr (pm : PreKeySignalMessage) (kp : KyberPayload) : HandshakeHdr where
  ikAPk := E2E.vecU8 pm.identityKey.publicKey.bytes
  ekAPk := E2E.vecU8 pm.baseKey.bytes
  spkId := u32 pm.signedPreKeyId
  opkId? := pm.preKeyId.map u32
  pqspkId := u32 kp.preKeyId
  kemCt := List.replicate 1568 0

theorem hdrOpkIdBv?_mkBadKemHdr (pm : PreKeySignalMessage) (kp : KyberPayload) :
    hdrOpkIdBv? (mkBadKemHdr pm kp) = pm.preKeyId := by
  unfold hdrOpkIdBv? mkBadKemHdr u32; cases pm.preKeyId <;> rfl

theorem mkBadKemHdr_ikAPk_len (pm : PreKeySignalMessage) (kp : KyberPayload) :
    (mkBadKemHdr pm kp).ikAPk.length = 32 :=
  vecU8_length pm.identityKey.publicKey.bytes

theorem mkBadKemHdr_ekAPk_len (pm : PreKeySignalMessage) (kp : KyberPayload) :
    (mkBadKemHdr pm kp).ekAPk.length = 32 :=
  vecU8_length pm.baseKey.bytes

theorem mkBadKemHdr_kemCt_len (pm : PreKeySignalMessage) (kp : KyberPayload) :
    (mkBadKemHdr pm kp).kemCt.length = 1568 := by
  simp [mkBadKemHdr]

theorem bytesToBv8_mkBadKemHdr_ekAPk (pm : PreKeySignalMessage) (kp : KyberPayload) :
    bytesToBv8 (mkBadKemHdr pm kp).ekAPk = pm.baseKey.bytes.toList :=
  bytesToBv8_vecU8 pm.baseKey.bytes

theorem bytesToBv8_mkBadKemHdr_ikAPk (pm : PreKeySignalMessage) (kp : KyberPayload) :
    bytesToBv8 (mkBadKemHdr pm kp).ikAPk = pm.identityKey.publicKey.bytes.toList :=
  bytesToBv8_vecU8 pm.identityKey.publicKey.bytes

theorem boxU8_payload_split_d3 (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) =
    (if bs = [] then emp else A.live ptr bs.length 1) ∗ (ptr ↦ₛ bs) := by
  by_cases h : bs = []
  · subst h
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
  · simp only [h, ↓reduceIte]

/-! ## 2. General `v4` Bad-KEM Message Unpack & Reassembly (`[LibsignalPlacement]`) -/

/-- Remainder of `preKeyMsgAt` outside `p2BadKemMsgFieldsAt` + `signalMessageRestVerAt` for any
`v4` `PreKeySignalMessage` with `pm.kyberPayload = some kp` (empty or non-empty `kp.ciphertext`). -/
def badKemMsgRemInnerAt (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) (kp : KyberPayload) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
  (if kp.ciphertext = [] then emp else E2E.HooksE.A0.live g.kyberPtr kp.ciphertext.length 1) ∗
  memRegion (msgA + 164#64) 4 ∗
  boxU8At E2E.HooksE.A0 (msgA + 128#64) g.serPtr pm.serialized ∗
  memRegion (msgA + 241#64) 7

theorem badKemMsgRemInnerAt_dup_kyber (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) (kp : KyberPayload) :
    badKemMsgRemInnerAt g msgA pm kp ⊢
      ⌜g.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗ badKemMsgRemInnerAt g msgA pm kp := by
  unfold badKemMsgRemInnerAt
  refine Entails.pure_left fun hp => ?_
  have hp' : g.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63 := hp
  rw [pure_sepConj_of_true hp', pure_sepConj_of_true hp]
  exact Entails.refl _

/-- Unpack `preKeyMsgAt` for any `pm` with `pm.messageVersion = 4` and `pm.kyberPayload = some kp`
into `p2BadKemMsgFieldsAt` + `signalMessageRestVerAt` + `badKemMsgRemInnerAt`. -/
theorem preKeyMsgAt_unpack_badKem (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) (kp : KyberPayload)
    (hv4 : pm.messageVersion = 4#8) (hkp : pm.kyberPayload = some kp) :
    preKeyMsgAt E2E.HooksE.A0 g msgA pm ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id⌝ ∗
        p2BadKemMsgFieldsAt msgA g.kyberPtr (mkBadKemHdr pm kp) kp.ciphertext
          pm.message.messageVersion opkWord kp.preKeyId pm.registrationId pm.signedPreKeyId ∗
        signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA pm.message ∗
        badKemMsgRemInnerAt g msgA pm kp := by
  unfold preKeyMsgAt p2BadKemMsgFieldsAt badKemMsgRemInnerAt
  rw [hv4, hkp, signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkBadKemHdr,
      bytesToBv8_mkBadKemHdr_ekAPk, bytesToBv8_mkBadKemHdr_ikAPk]
  dsimp only [optKyberAt, boxU8At]
  rw [boxU8_payload_split_d3 E2E.HooksE.A0 g.kyberPtr kp.ciphertext]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  cases hopk_eq : pm.preKeyId with
  | none =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_4_eq_exists_pointsTo32 (msgA + 124#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun opkWord => ?_
    refine Entails.sepExists_right opkWord (Entails.pure_right (by nofun) ?_)
    exact Entails.of_eq (by ac_rfl)
  | some id =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right id (Entails.pure_right (fun _ h => Option.some.inj h) ?_)
    exact Entails.of_eq (by ac_rfl)

/-- Reassemble `p2BadKemMsgFieldsAt` + `signalMessageRestVerAt` + `badKemMsgRemInnerAt` back into
`preKeyMsgAt E2E.HooksE.A0 g msgA pm`. -/
theorem p2BadKemMsgFields_reassemble (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) (kp : KyberPayload) (opkWord : BitVec 32)
    (hv4 : pm.messageVersion = 4#8) (hkp : pm.kyberPayload = some kp)
    (hopkWord : ∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id) :
    p2BadKemMsgFieldsAt msgA g.kyberPtr (mkBadKemHdr pm kp) kp.ciphertext
      pm.message.messageVersion opkWord kp.preKeyId pm.registrationId pm.signedPreKeyId ∗
    signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA pm.message ∗
    badKemMsgRemInnerAt g msgA pm kp ⊢
      preKeyMsgAt E2E.HooksE.A0 g msgA pm := by
  unfold p2BadKemMsgFieldsAt badKemMsgRemInnerAt preKeyMsgAt
  rw [hv4, hkp, signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkBadKemHdr,
      bytesToBv8_mkBadKemHdr_ekAPk, bytesToBv8_mkBadKemHdr_ikAPk]
  have hoptU32 :
      ((msgA + 120#64) ↦₃₂ opkOptTag32 pm.preKeyId) ∗ ((msgA + 124#64) ↦₃₂ opkWord) ⊢
      optU32At (msgA + 120#64) pm.preKeyId := by
    cases hopk_eq : pm.preKeyId with
    | none =>
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
    | some id =>
      have hw := hopkWord id hopk_eq
      subst hw
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (((msgA + 120#64) ↦₃₂ opkOptTag32 pm.preKeyId) ∗ ((msgA + 124#64) ↦₃₂ opkWord)) ∗
    (((msgA + 112#64) ↦₈ pm.message.messageVersion) ∗
      signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA pm.message ∗
      boxU8At E2E.HooksE.A0 (msgA + 128#64) g.serPtr pm.serialized ∗
      (((msgA + 144#64) ↦₆₄ g.kyberPtr) ∗
        ((msgA + 152#64) ↦₆₄ BitVec.ofNat 64 kp.ciphertext.length) ∗
        ⌜g.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        ((if kp.ciphertext = [] then emp else E2E.HooksE.A0.live g.kyberPtr kp.ciphertext.length 1) ∗
          (g.kyberPtr ↦ₛ kp.ciphertext)) ∗
        ((msgA + 160#64) ↦₃₂ kp.preKeyId) ∗
        memRegion (msgA + 164#64) 4) ∗
      ((msgA + 168#64) ↦ₛ pm.baseKey.bytes.toList) ∗
      ((msgA + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList) ∗
      ((msgA + 232#64) ↦₃₂ pm.registrationId) ∗
      ((msgA + 236#64) ↦₃₂ pm.signedPreKeyId) ∗
      ((msgA + 240#64) ↦₈ 4#8) ∗
      memRegion (msgA + 241#64) 7) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hoptU32) ?_
  dsimp only [optKyberAt, boxU8At]
  rw [boxU8_payload_split_d3 E2E.HooksE.A0 g.kyberPtr kp.ciphertext]
  exact Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)

/-! ## 3. Error Arms 4–5 (`SepWPp` Exit Bridges) on `stageP1ProgPlaced ext` -/

set_option maxHeartbeats 800000 in
/-- Placed Path-A Arm 4 (`+0x07bc -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2BadKemErrFrameAtPlaced`. -/
theorem p2_badKem_arm4_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc} (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64) (pkKit : PreKeyStoreSpec A 0#64)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (s0 s2 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (spkBPk : SignalPqxdh.Bytes) (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.KpErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp) (hspkBPk_len : spkBPk.length = 32) (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32) (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem) (hpc : s2.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s2.status = .Running) (hsp : s2.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s2.readReg64 .x19 = coroPtr) (hx21 : s2.readReg64 .x21 = coroPtr + 912#64) (hx23 : s2.readReg64 .x23 = coroPtr + 1266#64)
    (hx24 : s2.readReg64 .x24 = sp + 880#64) (hx25 : s2.readReg64 .x25 = sp + 528#64) (hx26 : s2.readReg64 .x26 = coroPtr + 920#64)
    (hx27 : s2.readReg64 .x27 = ctxPtr) (hx28 : s2.readReg64 .x28 = sp + 2704#64) (hx29 : s2.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp), Steps (stageP1ProgPlaced ext) s2 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.trace = s2.trace → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt skit.kpErr outPtr e ∗ spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
      (kpPollOutAt skit (sp + 992#64) (.error e) ∗ memRegion (sp + 1064#64) 272 ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗ ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 1272#64) ↦₆₄ idKpFutPtr) ∗ ((coroPtr + 1280#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗ ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗ ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗ ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗ ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
       ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗ ((coroPtr + 1265#64) ↦₈ 1#8) ∗
       memRegion (coroPtr + 1624#64) 298 ∗ memRegion (coroPtr + 1944#64) 64 ∗
       ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
       ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦ₛ ctBytes) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8) ∗
       ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 968#64) 7 ∗ cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
       cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗ ((fp + -128#64) ↦₆₄ u_b90) ∗ ((fp + -120#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗
       p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId stSpk' stKpk' stPk' Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hpqsk_len : (bytesToBv8 inp.pqspkBSk).length = 3168 := by simp [bytesToBv8, hwell.2.2.2.2.2.1]
  dsimp only [p2Sub5FramePlaced]; simp only [BitVec.reduceNeg]
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega))) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hpqsk_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr)) (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
      memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm4 := p2_arm4_err_hooks_placed_ok (Qp := fun _ _ => False) hH hskitOk s0 s2
    sp coroPtr msgPtr ctxPtr outPtr 0#64 8#64 idStorePtr idKpFutPtr pkBuf skBuf fp
    (coroPtr + 912#64) (coroPtr + 920#64) (coroPtr + 1266#64) v_a8 (coroPtr + 912#64) v_b8 ctxPtr v_d0 u_b90
    opkIdWord b_2c0 b_390 b_4f2 b_b98 e (by decide) hCode hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
  rw [hif0] at harm4
  refine p2_finish_err_arm_drop
    (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
      ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗ ((0#64 + skit.kpFutVtOff + 16#64) ↦₆₄ᵣ 8#64))
    harm4 (by sep_focus) ?_ (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  dsimp only [p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]; simp only [BitVec.reduceNeg]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3e0_arm4_to_368 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 920#64)
    (coroPtr + 1266#64) (skit.kpErr.w4 e) (coroPtr + 912#64) (skit.kpErr.w2 e) ctxPtr outPtr (skit.kpErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
    pkBuf 1568#64 skBuf 3168#64 (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1])) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) (msgPtr + 144#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4f8_words2_328_entails_344 coroPtr idKpFutPtr (0#64 + skit.kpFutVtOff)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
/-- Placed Over-Path Arm 4 (`+0x07bc -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2BadKemErrFrameAtPlaced`. -/
theorem p2_over_badKem_arm4_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc} (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64) (pkKit : PreKeyStoreSpec A 0#64)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit) (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext) (s0 s2 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (spkBPk : SignalPqxdh.Bytes) (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.KpErr) (gMe gPeer : AddrGhost) (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp) (hspkBPk_len : spkBPk.length = 32) (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32) (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem) (hpc : s2.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s2.status = .Running) (hsp : s2.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s2.readReg64 .x19 = coroPtr) (hx21 : s2.readReg64 .x21 = coroPtr + 912#64) (hx23 : s2.readReg64 .x23 = coroPtr + 1266#64)
    (hx24 : s2.readReg64 .x24 = sp + 880#64) (hx25 : s2.readReg64 .x25 = sp + 528#64) (hx26 : s2.readReg64 .x26 = coroPtr + 920#64)
    (hx27 : s2.readReg64 .x27 = ctxPtr) (hx28 : s2.readReg64 .x28 = sp + 2704#64) (hx29 : s2.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp), Steps (stageP1ProgPlaced ext) s2 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.trace = s2.trace → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt skit.kpErr outPtr e ∗ spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
      (kpPollOutAt skit (sp + 992#64) (.error e) ∗ memRegion (sp + 1064#64) 272 ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗ ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 1272#64) ↦₆₄ idKpFutPtr) ∗ ((coroPtr + 1280#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗ ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗ ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗ ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗ ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
       ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗ ((coroPtr + 1265#64) ↦₈ 1#8) ∗
       memRegion (coroPtr + 1624#64) 298 ∗ memRegion (coroPtr + 1944#64) 64 ∗
       ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
       ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦ₛ ctBytes) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8) ∗
       ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 968#64) 7 ∗ cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
       cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗ ((fp + -128#64) ↦₆₄ u_b90) ∗ ((fp + -120#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗
       p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId stSpk' stKpk' stPk' g recG sess Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat := Nat.le_trans hstk_drop hstk_lt
  have hpqsk_len : (bytesToBv8 inp.pqspkBSk).length = 3168 := by simp [bytesToBv8, hwell.2.2.2.2.2.1]
  dsimp only [p2OverSub5FramePlaced]; simp only [BitVec.reduceNeg]
  refine SepWPp.weaken_frame (sessionAt_entails_sessionStateAt A (coroPtr + 248#64) recG sess) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega))) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hpqsk_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64)) (by sep_focus) ?_
  have harm4 := p2_over_arm4_err_hooks_placed_ok (Qp := fun _ _ => False) hH hDropSs3 hskitOk s0 s2
    sp coroPtr msgPtr ctxPtr outPtr idStorePtr idKpFutPtr pkBuf skBuf fp
    (coroPtr + 912#64) (coroPtr + 920#64) (coroPtr + 1266#64) v_a8 (coroPtr + 912#64) v_b8 ctxPtr v_d0 u_b90
    opkIdWord b_2c0 b_390 b_4f2 b_b98 e g recG sess.state hCode hsp hsp_lt hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
  refine p2_finish_err_arm_drop
    (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
      ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗ ((0#64 + skit.kpFutVtOff + 16#64) ↦₆₄ᵣ 8#64))
    harm4 (by sep_focus) ?_ (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hCodef hent)
  dsimp only [p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]; simp only [BitVec.reduceNeg]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3e0_arm4_to_368 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 920#64)
    (coroPtr + 1266#64) (skit.kpErr.w4 e) (coroPtr + 912#64) (skit.kpErr.w2 e) ctxPtr outPtr (skit.kpErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
    pkBuf 1568#64 skBuf 3168#64 (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1])) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) (msgPtr + 144#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4f8_words2_328_entails_344 coroPtr idKpFutPtr (0#64 + skit.kpFutVtOff)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
/-- Placed Path-A Arm 5 (`+0x125c -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2BadKemErrFrameAtPlaced`. -/
theorem p2_badKem_arm5_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc} (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64) (pkKit : PreKeyStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (hH : StageP2ClosureHooksPlaced A ext) (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : SignalPqxdh.Bytes) (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp) (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568) (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ -2#64) (herr_ne_pend : errTag ≠ -3#64) (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl sf5.mem) (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr) (hx25 : sf5.readReg64 .x25 = sp + 528#64) (hx28 : sf5.readReg64 .x28 = sp + 2704#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp), Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.trace = sf5.trace → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗ spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
      (((sp + 992#64) ↦₆₄ -1#64) ∗ speWordsAt (sp + 1000#64) errTag w2 w3 w4 w5 w6 ∗ memRegion (sp + 1048#64) 288 ∗
       bobParamsBadKemFieldsAt (coroPtr + 1624#64) skBuf (msgPtr + 144#64) ctBufPtr (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗ ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
       ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗ ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
       cells (coroPtr + 1272#64) 2 ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗
       ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗ ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1688#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 1816#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 1824#64) ↦₆₄ 1568#64) ∗ ((coroPtr + 1857#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 1889#64) inp.opkBSk? opkSkBytes ∗ memRegion (coroPtr + 1944#64) 64 ∗
       ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8') ∗
       ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8') ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 968#64) 7 ∗ cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
       cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗ ((fp + -128#64) ↦₆₄ u_b90') ∗ ((fp + -120#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗
       p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId stSpk' stKpk' stPk' Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2Sub5FramePlaced]; simp only [BitVec.reduceNeg]
  refine SepWPp.weaken_frame (p2_bobParamsBadKemFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ctBytes ikBPk spkBPk hwell) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr)) (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
      memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm5 := p2_arm5_err_hooks_placed_ok (Qp := fun _ _ => False) hH s0 sf5
    sp coroPtr outPtr 0#64 8#64 pkBuf skBuf errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0' b_2c0 b_390 b_4f2 (by decide)
    (by simpa only [BitVec.reduceNeg] using herr_ne_pend) (by simpa only [BitVec.reduceNeg] using herr_ne_ok)
    hCode hsp hpc hrun (hsp ▸ hsp_align) hx19 hx25 hx28 hvregs
  rw [hif0] at harm5
  refine p2_finish_err_arm_drop (Drop := emp) harm5 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ => hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  rw [emp_sepConj]; dsimp only [p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]; simp only [BitVec.reduceNeg]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 920#64)
    (coroPtr + 1266#64) w5 (coroPtr + 912#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
    hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
    pkBuf 1568#64 skBuf 3168#64 (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1])) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) (msgPtr + 144#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
/-- Placed Over-Path Arm 5 (`+0x125c -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2BadKemErrFrameAtPlaced`. -/
theorem p2_over_badKem_arm5_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc} (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64) (pkKit : PreKeyStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : SignalPqxdh.Bytes) (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp) (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568) (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ -2#64) (herr_ne_pend : errTag ≠ -3#64) (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl sf5.mem) (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr) (hx25 : sf5.readReg64 .x25 = sp + 528#64) (hx28 : sf5.readReg64 .x28 = sp + 2704#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp), Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.trace = sf5.trace → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗ spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
      (((sp + 992#64) ↦₆₄ -1#64) ∗ speWordsAt (sp + 1000#64) errTag w2 w3 w4 w5 w6 ∗ memRegion (sp + 1048#64) 288 ∗
       bobParamsBadKemFieldsAt (coroPtr + 1624#64) skBuf (msgPtr + 144#64) ctBufPtr (coroPtr + 920#64) inp ctBytes ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗ ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
       ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗ ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
       cells (coroPtr + 1272#64) 2 ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗
       ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗ ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1688#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 1816#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 1824#64) ↦₆₄ 1568#64) ∗ ((coroPtr + 1857#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 1889#64) inp.opkBSk? opkSkBytes ∗ memRegion (coroPtr + 1944#64) 64 ∗
       ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8') ∗
       ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8') ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 968#64) 7 ∗ cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
       cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗ ((fp + -128#64) ↦₆₄ u_b90') ∗ ((fp + -120#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗
       p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId stSpk' stKpk' stPk' g recG sess Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat := Nat.le_trans hstk_drop hstk_lt
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2OverSub5FramePlaced]; simp only [BitVec.reduceNeg]
  refine SepWPp.weaken_frame (sessionAt_entails_sessionStateAt A (coroPtr + 248#64) recG sess) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_bobParamsBadKemFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ctBytes ikBPk spkBPk hwell) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64)) (by sep_focus) ?_
  have harm5 := p2_over_arm5_err_hooks_placed_ok (Qp := fun _ _ => False) hH hDropSs3 s0 sf5
    sp coroPtr outPtr pkBuf skBuf errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0' b_2c0 b_390 b_4f2 g recG sess.state
    (by simpa only [BitVec.reduceNeg] using herr_ne_pend) (by simpa only [BitVec.reduceNeg] using herr_ne_ok)
    hCode hsp hsp_lt hpc hrun (hsp ▸ hsp_align) hx19 hx25 hx28 hvregs
  refine p2_finish_err_arm_drop (Drop := emp) harm5 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ => hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hCodef hent)
  rw [emp_sepConj]; dsimp only [p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]; simp only [BitVec.reduceNeg]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 920#64)
    (coroPtr + 1266#64) w5 (coroPtr + 912#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
    hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
    pkBuf 1568#64 skBuf 3168#64 (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1])) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) (msgPtr + 144#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## 4. Full Stage P2 Bad-KEM Compositions on `stageP1ProgPlaced ext` (Path A & Over-Path C) -/

theorem p2_badKem_entry_le_stageP2bStack : 768 + pqxdhEntryStack ≤ stageP2bStack := by
  decide

set_option maxHeartbeats 1200000 in
/-- Full Path-A Stage P2 (`+0x0868 -> s0.readReg64 .x30`) on Bad-KEM
(`pkVecTag? 8#8 1568 ctBytes = none`). -/
theorem stageP2_pathA_badKem_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ) {A : RustAlloc} (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext) {sameStk : Nat}
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse sameStk)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk)
    (hsame_le : sameStk ≤ stk) (herr_le : 768 + pqxdhEntryStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (hctBuf_nz : ctBufPtr ≠ 0#64) (hstk_lt : stk ≤ sp.toNat)
    (hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (hekAPk_len : hdr.ekAPk.length = 32) (hkemCt_len : hdr.kemCt.length = 1568)
    (hct_bd : ctBytes.length < 2 ^ 63) (hbadKem : pkVecTag? 8#8 1568 ctBytes = none) (hCode : Φ s.mem)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8), spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8), kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧ r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8), opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64) (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr) (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr) (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr) (hx16 : s.readReg64 .x16 = ikit.id_vt)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 224#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) (hx29 : s.readReg64 .x29 = fp)
    (hErrSpk : ∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) → sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt spkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗ pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt kpkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt pkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (wOpk : OpkOkWitness (hdrOpkIdBv? hdr))
        (e : skit.KpErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → skit.kpRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt skit.kpErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes → spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec → kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes → kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes → skit.kpRel stId (.ok kp) → errTag ≠ -2#64 → errTag ≠ -3#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.ok kp) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (stageP2BadKemPreAtPlaced A spkKit kpkKit pkKit ikit s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer stk Frame) Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hstk_sub56 : stageP2Sub56Stack skit ≤ stk := Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc : allocHookStack ≤ stk := Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  refine p2_mono_pre (p2_badKem_entry_to_sub1To4_placed spkKit kpkKit pkKit ikit s0
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId stSpk stKpk stPk stId gMe gPeer stk Frame) ?_
  refine stageP2_sub1_to_4_kits_ext_placed ext hH hPure
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk hstk_p2 hstk_le64 s0 s
    (p2BadKemSub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame)
    Q hpan sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 912#64) u_90 u_a8 u_b8 u_d0 u_488 baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2
    hctBuf_nz (hInv.toCodeRo hCode) hfs hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    (fun e spkFutPtr sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrSpk e sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm1_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          hdr ctBytes stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrKpk spkRec e sf P_f hspk_rel hspk_ok hkpk_rel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm2_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          hdr ctBytes spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrPk spkRec kpkRec opkId e sf P_f hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm3_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90 b_4b0 msgVerByte opkId opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId hdr ctBytes spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
          stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs4 _hCode4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk := fun _ h => opkOkSkBytes?_eq_of_some h
  have htr0_4 : s0.trace <+: s4.trace := htr.trans (by rw [htr4, List.append_assoc, List.append_assoc]; exact List.prefix_append _ _)
  refine p2_mono_pre (p2_badKem_sub4_to_sub5_placed spkKit kpkKit pkKit skit s0
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
    inp hdr ctBytes spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId msgVerByte b_2c0 b_390 b_4f2
    (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
    (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId gMe gPeer stk Frame rfl (bytesToBv8_toU8 spkPubBytes)
    (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
    (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
    (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm hkyberPriv_len) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  exact stageP2_sub5_badKem_kits_memInv_at_placed hInv ext skit hH hskitOk hskitVt hSameAcct hInitBobBadKemErrOwned
    inp ctBytes spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q hpan
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) Frame)
    rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hct_bd hbadKem hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp) (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hsame_le herr_le hstk_sub56 hstk_lt (hInv.of_keepsFrozen hCode hst_s4.keepsFrozen)
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1) hpc4 hrun4 hsp4 hsp_align htr0_4 hvregs4
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    (fun kp errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5 hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hCode5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
        rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      have harm5 := p2_mono_panic hpan
        (p2_badKem_arm5_hooks_placed_ok ext spkKit kpkKit pkKit ikit hH s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90 errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ctBytes ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId gMe gPeer stk (pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗ Frame)
          hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq herr_ne_ok herr_ne_pend hstk_alloc hstk_lt
          hCode5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes wOpk opkPkBytes opkSkBytes kp
              errTag w2 w3 w4 w5 w6 sf P_f hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq hopk_rel hopkPk_len hopkSk_len hopk_kb
              hkp_rel herr_ne_ok herr_ne_pend hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hinvf
              (Entails.trans hent (p2_badKem_arm5_err_payload_pull_placed s0 sp fp coroPtr outPtr msgPtr ctBufPtr
                remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
                v_330 v_388 errTag w2 w3 w4 w5 w6 inp.hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                (ikit.identityAt idStorePtr stId) gMe gPeer stk Frame))))
      dsimp only [p2Sub5FramePlaced] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    (fun e s2 hkp_err _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2 =>
      p2_mono_panic hpan
        (p2_badKem_arm4_hooks_placed_ok ext spkKit kpkKit pkKit skit hH hskitOk s0 s2 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' u_b90 inp ctBytes spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId msgVerByte b_2c0 b_390 b_4f2 b_b98
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId e gMe gPeer stk Frame
          hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_alloc hstk_lt hCode2 hpc2 hrun2 hsp2 hsp_align
          hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrKp spkRec kpkRec wOpk e sf P_f hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err
              hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hinvf hent)))

abbrev stageP2_pathA_badKem_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2PureCalleesPlaced P A F ext)
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv (StoreKit.LibsignalCodeRoLoaded lsmpl)
        (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit) (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit) (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk : stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_pathA_badKem_kits_memInv_at_placed StageP2MemInv.codeRoLoaded ext
    hH hPure.to_4K.toStageP2BaseCalleesPlaced4K (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    hInitBobBadKemErrOwned ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk
    (Nat.le_trans (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans p2_isSameAccount_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans p2_stageP2bStack_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))

set_option maxHeartbeats 1200000 in
/-- Full Over-Path Stage P2 (`+0x0868 -> s0.readReg64 .x30`) on Bad-KEM
(`pkVecTag? 8#8 1568 ctBytes = none`). -/
theorem stageP2_over_badKem_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ) {A : RustAlloc} (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext) {sameStk : Nat}
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse sameStk)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit) (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit) (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk_overP2 : stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤ stk)
    (hstk_sub56 : stageP2Sub56Stack skit ≤ stk) (hstk_drop : dropSessionStructureLocal2Stack ≤ stk)
    (hsame_le : sameStk ≤ stk) (herr_le : 768 + pqxdhEntryStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8) (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (hPromMiss : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 4#8 (5#8 :: bytesToBv8 hdr.ekAPk))
    (hctBuf_nz : ctBufPtr ≠ 0#64) (hstk_lt : stk ≤ sp.toNat) (hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (hekAPk_len : hdr.ekAPk.length = 32) (hkemCt_len : hdr.kemCt.length = 1568)
    (hct_bd : ctBytes.length < 2 ^ 63) (hbadKem : pkVecTag? 8#8 1568 ctBytes = none) (hCode : Φ s.mem)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8), spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8), kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧ r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id → pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8), opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64) (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr) (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr) (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr) (hx16 : s.readReg64 .x16 = ikit.id_vt)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 224#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) (hx29 : s.readReg64 .x29 = fp)
    (hErrSpk : ∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) → sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt spkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗ pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt kpkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt pkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (wOpk : OpkOkWitness (hdrOpkIdBv? hdr))
        (e : skit.KpErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → skit.kpRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt skit.kpErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes → spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec → kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes → kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes → skit.kpRel stId (.ok kp) → errTag ≠ -2#64 → errTag ≠ -3#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.ok kp) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        p2BadKemErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (stageP2OverBadKemPreAtPlaced A spkKit kpkKit pkKit ikit s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame) Q Qp := by
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  have hPromMiss_bk : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 4#8 baseKey.serialize := hPromMiss
  refine p2_mono_pre (p2_over_badKem_entry_to_sub1To4_placed spkKit kpkKit pkKit ikit s0
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame) ?_
  refine stageP2_over_sub1_to_4_kits_ext_placed ext hH hPure
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk hstk_overP2 s0 s
    (p2BadKemSub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame)
    Q hpan sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 912#64) u_90 u_a8 u_b8 u_d0 u_488 hstk_lt g recG sess baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2 hPromMiss_bk hctBuf_nz (hInv.toCodeRo hCode) hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    (fun e spkFutPtr sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrSpk e sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm1_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          hdr ctBytes stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrKpk spkRec e sf P_f hspk_rel hspk_ok hkpk_rel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm2_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          hdr ctBytes spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrPk spkRec kpkRec opkId e sf P_f hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent (p2_badKem_arm3_entails_placed spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          (coroPtr + 912#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90 b_4b0 msgVerByte opkId opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId hdr ctBytes spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
          stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs4 _hCode4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk := fun _ h => opkOkSkBytes?_eq_of_some h
  have htr0_4 : s0.trace <+: s4.trace := htr.trans (by rw [htr4, List.append_assoc, List.append_assoc]; exact List.prefix_append _ _)
  refine p2_mono_pre (p2_over_badKem_sub4_to_sub5_placed spkKit kpkKit pkKit skit s0
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
    inp hdr ctBytes spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId msgVerByte b_2c0 b_390 b_4f2
    (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
    (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId gMe gPeer g recG sess stk Frame rfl (bytesToBv8_toU8 spkPubBytes)
    (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
    (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
    (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm hkyberPriv_len) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  exact stageP2_sub5_badKem_kits_memInv_at_placed hInv ext skit hH hskitOk hskitVt hSameAcct hInitBobBadKemErrOwned
    inp ctBytes spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q hpan
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) g recG sess Frame)
    rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hct_bd hbadKem hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp) (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hsame_le herr_le hstk_sub56 hstk_lt (hInv.of_keepsFrozen hCode hst_s4.keepsFrozen)
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1) hpc4 hrun4 hsp4 hsp_align htr0_4 hvregs4
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    (fun kp errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5 hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hCode5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      have harm5 := p2_mono_panic hpan
        (p2_over_badKem_arm5_hooks_placed_ok ext spkKit kpkKit pkKit ikit hH hPure.dropSessionStructure3 s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90 errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ctBytes ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId gMe gPeer g recG sess stk (pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗ Frame)
          hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq herr_ne_ok herr_ne_pend hstk_drop hstk_lt
          hCode5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes wOpk opkPkBytes opkSkBytes kp
              errTag w2 w3 w4 w5 w6 sf P_f hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq hopk_rel hopkPk_len hopkSk_len hopk_kb
              hkp_rel herr_ne_ok herr_ne_pend hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hinvf
              (Entails.trans hent (p2_badKem_arm5_err_payload_pull_placed s0 sp fp coroPtr outPtr msgPtr ctBufPtr
                remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
                v_330 v_388 errTag w2 w3 w4 w5 w6 inp.hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                (ikit.identityAt idStorePtr stId) gMe gPeer stk Frame))))
      dsimp only [p2OverSub5FramePlaced] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    (fun e s2 hkp_err _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2 =>
      p2_mono_panic hpan
        (p2_over_badKem_arm4_hooks_placed_ok ext spkKit kpkKit pkKit skit hH hPure.dropSessionStructure3 hskitOk s0 s2 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' u_b90 inp ctBytes spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId msgVerByte b_2c0 b_390 b_4f2 b_b98
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId e gMe gPeer g recG sess stk Frame
          hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_drop hstk_lt hCode2 hpc2 hrun2 hsp2 hsp_align
          hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrKp spkRec kpkRec wOpk e sf P_f hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err
              hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hinvf hent)))

abbrev stageP2_over_badKem_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2PureCalleesPlaced P A F ext)
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv (StoreKit.LibsignalCodeRoLoaded lsmpl)
        (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A))))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit) (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit) (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_over_badKem_kits_memInv_at_placed StageP2MemInv.codeRoLoaded ext
    hH hPure.to_4K.toStageP2BaseCalleesPlaced4K (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    hInitBobBadKemErrOwned ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk
    ((stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      Nat.le_trans (p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans (p2_sub56Stack_le_v1CallStack spkKit kpkKit pkKit skit)
      (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_over_dropSS3_le_overPure (Nat.le_trans (p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_isSameAccount_le_bobV1
      (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
        (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))
    (Nat.le_trans p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans p2_stageP2bStack_le_bobV1
        (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
          (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk))))

abbrev stageP2_pathA_badKem_kits_frozen_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse isSameAccountDistinctStack)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit) (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit) (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk : stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_pathA_badKem_kits_memInv_at_placed StageP2MemInv.frozen ext hH hPure hSameAcct
    (of_frozen_badKem_errOwned_placed hInitBobBadKemErrOwned)
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk
    (Nat.le_trans (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans p2_isSameAccount_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans p2_stageP2bStack_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))

abbrev stageP2_over_badKem_kits_frozen_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse isSameAccountDistinctStack)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A))
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64) (hspkVt : SignedPreKeyVtablesPlacedOk spkKit) (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit) (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkVt : PreKeyVtablesPlacedOk pkKit) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_over_badKem_kits_memInv_at_placed StageP2MemInv.frozen ext hH hPure hSameAcct
    (of_frozen_badKem_errOwned_placed hInitBobBadKemErrOwned)
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk stk
    ((stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      Nat.le_trans (p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans (p2_sub56Stack_le_v1CallStack spkKit kpkKit pkKit skit)
      (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_over_dropSS3_le_overPure (Nat.le_trans (p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans p2_isSameAccount_le_bobV1
      (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
        (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))
    (Nat.le_trans p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans p2_stageP2bStack_le_bobV1
        (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
          (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit) hstk))))

end LibsignalBinary.Proofs.SignalSession.Cli.D3
