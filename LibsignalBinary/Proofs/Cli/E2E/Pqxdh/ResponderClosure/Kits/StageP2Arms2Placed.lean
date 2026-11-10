/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext

/-!
# Relocatable Stage P2 Arm 6 and Normal-Exit Bridges

Defines `p2Sub6FramePlaced` and `p2OkPostAtPlaced`, and proves placed Arm 6 error unwind
`p2_v1_arm6_ok_hooks_placed` and normal-exit entailment `p2_v1_ok_entails_placed` on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (mkBobSenderChainGhost)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

private theorem lsLogOff_eq_pl2 [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

/-- Frame held constant across `stageP2_sub6_v1_kits_placed` (`+0x125c -> +0x1778` and Arm 6). -/
def p2Sub6FramePlaced (A : RustAlloc) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (s0 : State)
    (sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey)
    (pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (b_2c0 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk' ∗
  kpkKit.storeAt kyberStorePtr stKpk' ∗
  pkKit.storeAt preKeyStorePtr stPk' ∗
  p2BobSessHeapAt A inp ikBPk spkBPk drKey pqBytes
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
  ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
  ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
  ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
  ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
  ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
  ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
  opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
  memRegion (coroPtr + 0x798#64) 64 ∗
  ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
  ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
  ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x538#64) 24 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  Frame

set_option maxHeartbeats 800000 in
/-- Placed Arm 6 (`+0x09f4 -> s0.readReg64 .x30`) full `SepWPp` exit bridge into
`p2ErrFrameAtPlaced`, folding the unpromoted Bob `SessionState` at `coroPtr + 0x4f8` via
`p2BobSessRegIdsV1_entails_bobInitSessionV1` and dropping it via `p2_arm6_err_hooks_placed_ok`. -/
theorem p2_v1_arm6_ok_hooks_placed {P : Primitives} {A : RustAlloc} [LibsignalPlacement]
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (s0 s4 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     regIdFutPtr pkBuf skBuf v_330 v_388
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
     c0 c1 c2 c3 c4 d0 d1 d2
     u_298 u_2a0 u_80 u_88 u_90 u_a8 u_b8 u_d0
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey)
    (spkPrivBytes pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (pad_f4 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId u_2a8 : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_3ac : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.RegIdErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hacc : Model.acceptKeys P inp = some drKey)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hspk_priv_len : spkPrivBytes.length = 32)
    (hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠ 0#64)
    (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64)
    (hrat_pub : ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64)
    (hck_ptr : chainKeyBoxPtr ≠ 0#64)
    (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem)
    (hpc : s4.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s4.status = .Running) (hsp : s4.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s4.readReg64 .x19 = coroPtr)
    (hx21 : s4.readReg64 .x21 = coroPtr + 0x390#64)
    (hx23 : s4.readReg64 .x23 = coroPtr + 0x4f2#64)
    (hx25 : s4.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s4.readReg64 .x26 = coroPtr + 0x398#64)
    (hx28 : s4.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (stageP1ProgPlaced ext) s4 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s4.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s4
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x410#64) 296 ∗
       memRegion (sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
         (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
            (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
            pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64 0#64))) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗ ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? inp.hdr)) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗ ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗
       p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
         localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
         ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
         inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
         stSpk' stKpk' stPk' gMe gPeer Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2Sub6FramePlaced, p2BobSessHeapAt]
  rw [p2_head56_mid280V1_zero_eq_regIds]
  have hsess_fold := p2BobSessRegIdsV1_entails_bobInitSessionV1 (A := A)
    hWF hacc hwell hikBPk_len hspkBPk_len hspk_priv_len hspk_clamp
    (coroPtr + 0x4f8#64) localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 0#32 0#32
    c0 c1 c2 c3 c4 d0 d1 d2 pqBytes
    hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
  dsimp only at hsess_fold
  refine SepWPp.weaken_frame hsess_fold (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_bobParamsFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_memRegion_a90_288_to_cells6_240 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm6 := p2_arm6_err_hooks_placed_ok (Qp := fun _ _ => False) hH hDropSs3 hskitOk
    (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (bytesToBv8 (Model.encodeEC ikBPk)) (bytesToBv8 (Model.encodeEC inp.hdr.ikAPk))
      (bytesToBv8 (Model.encodeEC inp.hdr.ekAPk))
      (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        (bytesToBv8 (Model.encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
      0#32 0#32)
    (p2BobInitSessionV1 ikBPk spkBPk inp drKey pqBytes hikBPk_len hwell.2.2.2.2.2.2.2.1
      hspkBPk_len (by rw [← hspk_clamp]; exact clampBv8List_length hspk_priv_len))
    s0 s4 sp coroPtr outPtr 0#64 8#64
    idStorePtr regIdFutPtr pkBuf skBuf
    (coroPtr + 0x390#64) u_88 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64)
    u_a8 (coroPtr + 0x390#64) u_b8 u_d0
    b_2c0 b_390 b_4f2 e
    (by decide) hCode hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx25 hx26 hx28 hvregs
  rw [hif0] at harm6
  refine p2_finish_err_arm_drop
    (Drop := ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
             ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
             ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    harm6 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  dsimp only [p2ErrFrameAtPlaced, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [lsLogOff_eq_pl2]
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp3e0_arm6_to_368 sp (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
      (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp3b0_words6_entails_48 sp u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (sp + 0x3a0#64) u_3a0)
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo8_entails_memRegion (sp + 0x3ac#64) b_3ac)
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_memRegion_a90_288_to_cells6_240 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 (skit.regIdErr.w0 e) u_90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (skit.regIdErr.w4 e) (coroPtr + 0x390#64) (skit.regIdErr.w2 e)
      ctxPtr outPtr (skit.regIdErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro298_words_entails_20 coroPtr u_298 u_2a0 u_2a8) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x650#64) (coroPtr + 0x4f8#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro788_words2_entails_16 coroPtr regIdFutPtr (0#64 + skit.regIdFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
      hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_v1_arm6_ok_ext_placed := @p2_v1_arm6_ok_hooks_placed
abbrev p2_v1_arm6_ok_4k_placed := @p2_v1_arm6_ok_hooks_placed
abbrev p2_v1_arm6_ok_placed := @p2_v1_arm6_ok_hooks_placed

/-- Placed spatial postcondition at `+0x1778` (Normal exit into Stage P3 `StageP3GenVRegs`). -/
def p2OkPostAtPlaced (A : RustAlloc) [LibsignalPlacement]
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    (ikit : IdentityStoreSpec A 0#64)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk' ∗
  kpkKit.storeAt kyberStorePtr stKpk' ∗
  pkKit.storeAt preKeyStorePtr stPk' ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  sessionStateAt A (coroPtr + 0xf8#64) G_bob st_bob ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ ((opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32))) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
  memRegion (coroPtr + 0x488#64) 8 ∗
  memRegion (coroPtr + 0x4b0#64) 65 ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((sp + 0x90#64) ↦₆₄ v_388) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ v_330) ∗
  ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
  ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
  ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
  ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
  ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  FromRecordCallees.lsLogOff ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

set_option maxHeartbeats 800000 in
/-- Placed normal-exit (`+0x1778`) spatial bridge folding `sessionStateAt A (coroPtr + 0xf8#64)` and
rejoining all Stage-P2 scratch slots into `p2OkPostAtPlaced`. -/
theorem p2_v1_ok_entails_placed {P : Primitives} {A : RustAlloc} [LibsignalPlacement]
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hWF : StructuralPrims P)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     regIdFutPtr pkBuf skBuf v_330 v_388
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
     c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey)
    (spkPrivBytes pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hacc : Model.acceptKeys P inp = some drKey)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hspk_priv_len : spkPrivBytes.length = 32)
    (hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠ 0#64)
    (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64)
    (hrat_pub : ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64)
    (hck_ptr : chainKeyBoxPtr ≠ 0#64) :
    (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
     ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
     ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
     ((coroPtr + 0xf8#64) ↦ₛ (p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
       (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
     ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
       (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
     ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
       (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
     ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
     ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
     ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
     ikit.identityAt idStorePtr stId ∗
     ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
     ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
     ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
     ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
     ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
     ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
     ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗
     ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
     ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
     ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
     opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
     ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
     ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
     ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
     ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
     ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
     ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
     ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
     ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
     ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
     ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
     ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
     ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
     ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
     cells (coroPtr + 0x250#64) 6 ∗
     ((coroPtr + 0x298#64) ↦₆₄ ((opkOptTag32 (hdrOpkIdBv? inp.hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32))) ∗
     ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
     ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
     ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
     ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
     ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
     ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
     ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? inp.hdr)) ∗
     ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
     ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
     ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
     ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
     ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
     ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
     (ctBufPtr ↦₈ 8#8) ∗
     ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
     ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
     ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
     ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
     ((sp + 0x90#64) ↦₆₄ v_388) ∗
     ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
     ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
     ((sp + 0xa8#64) ↦₆₄ v_330) ∗
     ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
     ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
     memRegion (sp + 0xbc#64) 4 ∗
     ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
     ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
     ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
     ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
     ((sp + 0x3ac#64) ↦₈ 3#8) ∗
     ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
     ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
     ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
     ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
     ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
     ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
     memRegion (sp + 0xa90#64) 288 ∗
     (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗
     p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
       remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
       localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
       ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
       inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
       stSpk' stKpk' stPk' gMe gPeer Frame) ⊢
    p2OkPostAtPlaced A spkKit kpkKit pkKit ikit s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        (bytesToBv8 (Model.encodeEC ikBPk)) (bytesToBv8 (Model.encodeEC inp.hdr.ikAPk))
        (bytesToBv8 (Model.encodeEC inp.hdr.ekAPk))
        (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          (bytesToBv8 (Model.encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
        remoteRegId localRegId)
      (p2BobInitSessionV1 ikBPk spkBPk inp drKey pqBytes hikBPk_len hwell.2.2.2.2.2.2.2.1
        hspkBPk_len (by rw [← hspk_clamp]; exact clampBv8List_length hspk_priv_len))
      inp.hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame := by
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2Sub6FramePlaced, p2BobSessHeapAt, p2OkPostAtPlaced, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [lsLogOff_eq_pl2]
  rw [← p2BobSessRegIdsV1_eq localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
        spqrCap spqrBufPtr (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr
        chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId]
  have hsess_fold := p2BobSessRegIdsV1_entails_bobInitSessionV1 (A := A)
    hWF hacc hwell hikBPk_len hspkBPk_len hspk_priv_len hspk_clamp
    (coroPtr + 0xf8#64) localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 remoteRegId localRegId
    c0 c1 c2 c3 c4 d0 d1 d2 pqBytes
    hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
  dsimp only at hsess_fold
  refine p2_entails_frame_v1 hsess_fold (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_bobSessRegIdsV1_entails_memRegion344 (coroPtr + 0x4f8#64)
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_bobSessRegIdsV1_entails_memRegion344 (sp + 0x3e0#64)
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_memRegion_3e0_split_344_24 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x650#64) (coroPtr + 0x4f8#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro788_words2_entails_16 coroPtr regIdFutPtr (0#64 + skit.regIdFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
      hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
