/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsA
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Placed Stage P2 Over-Path Exit Bridges for Error Arms 4 and 5

Defines `[LibsignalPlacement]` Substage P2.5 frame `p2OverSub5FramePlaced` and proves the placed
`SepWPp` exit bridges into `p2ErrFrameAtPlaced` for Error Arms 4 (`+0x07bc → x30`) and 5
(`+0x125c → x30`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

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
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

private theorem lsLogOff_eq_pl [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

/-- Spatial frame preserved across placed Substage P2.5 (`+0x36ac → +0x125c` and error Arms 4–5)
with a populated `SessionRecord`. -/
def p2OverSub5FramePlaced (A : RustAlloc) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 : BitVec 64)
    (kyberPubBytes : List (BitVec 8))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk' ∗
  kpkKit.storeAt kyberStorePtr stKpk' ∗
  pkKit.storeAt preKeyStorePtr stPk' ∗
  (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
  A.live skBuf 3168 1 ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  memRegion (coroPtr + 0x508#64) 328 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗
  ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
  ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
  ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
  ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 8 ∗
  memRegion (sp + 0x3c0#64) 8 ∗ memRegion (sp + 0x3cf#64) 1 ∗
  memRegion (sp + 0x3d0#64) 8 ∗ memRegion (sp + 0x3d8#64) 8 ∗
  memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0xad0#64) 1 ∗
  memRegion (sp + 0xad1#64) 223 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗ Frame

set_option maxHeartbeats 800000 in
/-- Placed Error Arm 4 (`+0x07bc → s0.readReg64 .x30`) exit bridge into `p2ErrFrameAtPlaced`. -/
theorem p2_over_v1_arm4_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (s0 s2 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (inp : AcceptKeysInput) (spkBPk : SignalPqxdh.Bytes)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.KpErr) (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
    (hpc : s2.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s2.status = .Running) (hsp : s2.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s2.readReg64 .x19 = coroPtr)
    (hx21 : s2.readReg64 .x21 = coroPtr + 0x390#64)
    (hx23 : s2.readReg64 .x23 = coroPtr + 0x4f2#64)
    (hx24 : s2.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s2.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s2.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s2.readReg64 .x27 = ctxPtr)
    (hx28 : s2.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s2.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (stageP1ProgPlaced ext) s2 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s2.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x428#64) 272 ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
       ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗
       p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' g recG sess Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat := Nat.le_trans hstk_drop hstk_lt
  have hpqsk_len : (bytesToBv8 inp.pqspkBSk).length = 3168 := by
    simp [bytesToBv8, hwell.2.2.2.2.2.1]
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2OverSub5FramePlaced]
  refine SepWPp.weaken_frame
    (sessionAt_entails_sessionStateAt A (coroPtr + 0xf8#64) recG sess) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega)))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hpqsk_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64))
    (by sep_focus) ?_
  have harm4 := p2_over_arm4_err_hooks_placed_ok (Qp := fun _ _ => False) hH hDropSs3 hskitOk s0 s2
    sp coroPtr msgPtr ctxPtr outPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    (coroPtr + 0x390#64) (coroPtr + 0x398#64) (coroPtr + 0x4f2#64)
    v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
    opkIdWord b_2c0 b_390 b_4f2 b_b98 e g recG sess.state
    hCode hsp hsp_lt hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
  refine p2_finish_err_arm_drop
    (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
             ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
             ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    harm4 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hCodef hent)
  dsimp only [p2ErrFrameAtPlaced, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [lsLogOff_eq_pl]
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3e0_arm4_to_368 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (skit.kpErr.w4 e) (coroPtr + 0x390#64) (skit.kpErr.w2 e)
      ctxPtr outPtr (skit.kpErr.w3 e)) (by sep_focus) ?_
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
    (p2_coro4f8_words2_328_entails_344 coroPtr idKpFutPtr (0#64 + skit.kpFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_over_v1_arm4_ext_placed_ok [LibsignalPlacement] := @p2_over_v1_arm4_hooks_placed_ok
abbrev p2_over_v1_arm4_placed_ok [LibsignalPlacement] := @p2_over_v1_arm4_hooks_placed_ok

set_option maxHeartbeats 800000 in
/-- Placed Error Arm 5 (`+0x125c → s0.readReg64 .x30`) exit bridge into `p2ErrFrameAtPlaced`. -/
theorem p2_over_v1_arm5_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    (ikit : IdentityStoreSpec A 0#64)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90
     errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_pend : errTag ≠ 0xfffffffffffffffd#64)
    (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl sf5.mem)
    (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr)
    (hx25 : sf5.readReg64 .x25 = sp + 0x210#64)
    (hx28 : sf5.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
       memRegion (sp + 0x418#64) 288 ∗
       bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
       cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
       cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗
       p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' g recG sess Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat := Nat.le_trans hstk_drop hstk_lt
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2OverSub5FramePlaced]
  refine SepWPp.weaken_frame
    (sessionAt_entails_sessionStateAt A (coroPtr + 0xf8#64) recG sess) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_bobParamsFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64))
    (by sep_focus) ?_
  have harm5 := p2_over_arm5_err_hooks_placed_ok (Qp := fun _ _ => False) hH hDropSs3 s0 sf5
    sp coroPtr outPtr pkBuf skBuf
    errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0'
    b_2c0 b_390 b_4f2 g recG sess.state herr_ne_pend herr_ne_ok
    hCode hsp hsp_lt hpc hrun (hsp ▸ hsp_align)
    hx19 hx25 hx28 hvregs
  refine p2_finish_err_arm_drop (Drop := emp) harm5 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hCodef hent)
  rw [emp_sepConj]
  dsimp only [p2ErrFrameAtPlaced, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [lsLogOff_eq_pl]
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) w5 (coroPtr + 0x390#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
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
    (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_over_v1_arm5_ext_placed_ok [LibsignalPlacement] := @p2_over_v1_arm5_hooks_placed_ok
abbrev p2_over_v1_arm5_placed_ok [LibsignalPlacement] := @p2_over_v1_arm5_hooks_placed_ok

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
