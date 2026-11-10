/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Stage P2 Arm 6 and Normal-Exit Bridges

Proves `RustCliAllocBudget M` placed Arm 6 error unwind `p2_v1_arm6_ok_hooks_placed` (`+0x09f4 →
s0.readReg64 .x30` under `P2Arm6FreeEnv`) and normal-exit entailment `p2_v1_ok_entails_placed` at
`+0x1778`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  dropSessionStructureLocal2Stack lsLogOff
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec LibsignalCodeRoLoaded
  PreKeyStoreSpec SignedPreKeyStoreSpec speErrAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (regIdPollOutAt)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput DRKey HandshakeHdr Primitives StructuralPrims WellSizedAcceptKeysInput bytesToBv8
  encodeEC
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderStore (
  clampBv8List clampBv8List_length
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bobParamsFieldsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved eq_of_sep_emp opkOptFieldAt opkPresentTag sessionRecordEmptyHeaderAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (mkBobSenderChainGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? mkBobGhostV1 opkOptTag32 p2BobInitSessionV1 p2BobSessHead56Bv8 p2BobSessHeapAt
  p2BobSessMid280V1 p2BobSessRegIdsV1_entails_bobInitSessionV1
  p2CoroScratchTailAt p2MsgFieldsAt
  p2_bobParamsFieldsAt_err_weaken p2_coro298_words_entails_20
  p2_coro398_bytes_words4_entails_96 p2_coro4b0_byte_bytes_entails_65
  p2_coro658_298_rejoin p2_coro788_words2_entails_16 p2_ctBuf_split
  p2_drop_frame_mid p2_entails_frame_v1 p2_head56_mid280V1_zero_eq_regIds
  p2_memRegion_a90_288_to_cells6_240 p2_processPrekeyActive10At_eq
  p2_sessionRecordEmptyHeaderAt_eq p2_sp80_11words_entails_88
  p2_sp3b0_words6_entails_48 p2_sp3e0_arm6_to_368 p2_stack_split_dropSs3
  stageP1EntryPlaced stageP1ProgPlaced
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv retagIdentitySelfStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentitySelfStoreKitPlacedOkI)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget (
  p2ErrFrameAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget (
  p2Arm6ErrEvents p2_arm6_err_events_hooks_placed_ok
)

private theorem lsLogOff_eq_pl2 [LibsignalPlacement] :
    lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem protocolAddressAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : AddrGhost) (p : BitVec 64) :
    protocolAddressAt (A.atState lim st s) g p = protocolAddressAt A.repAlloc g p := rfl

private theorem p2_finish_err_arm6_drop {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp}
    {ArmOut Keep : List AllocEvent → State → SepProp}
    {Ψ : List AllocEvent → Prop} {Φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (∃ evs_ss : List AllocEvent,
          FreeOnlyEvs evs_ss ∧ (P_f ⊢ ArmOut evs_ss sf) ∧ Ψ evs_ss) ∧
        Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ evs_ss sf, ArmOut evs_ss sf ∗ Rest ⊢ Drop ∗ Keep evs_ss sf)
    (hQ : ∀ sf P_f evs_ss,
      FreeOnlyEvs evs_ss →
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep evs_ss sf) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps,
      ⟨hpcm, hrunm, P_m, hmm, htrf, ⟨evs_ss, hfree, hent, _⟩, hΦ⟩ |
      ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hArm (Rest ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (ArmOut evs_ss sm ∗ Rest) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    have hmm'' : sm.mem ⊨ (Drop ∗ Keep evs_ss sm) ∗ R :=
      Arm64.Satisfies.mono (sepConj_mono_left (hSplit evs_ss sm)) hmm'
    obtain ⟨sf, hsteps_mf, hpost⟩ :=
      (p2_drop_frame_mid (Drop := Drop) rfl
        (SepWPp.done (Qp := Qp) hpcm hrunm
          (hQ sm (Keep evs_ss sm) evs_ss hfree hsteps hpcm hrunm htrf (Entails.refl _) hΦ)))
        R hmm'' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps_mf, hpost⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Frame held constant across `stageP2_sub6_v1_kits_placed` (`+0x125c -> +0x1778` and Arm 6),
parameterized by `A : RustCliAllocBudget M`. -/
def p2Sub6FramePlaced {M : AllocCostModel} (A : RustCliAllocBudget M) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (s0 : State)
    (sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8) (drKey : DRKey)
    (pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (b_2c0 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub6FramePlaced
    A.repAlloc spkKit kpkKit pkKit s0
    sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
    inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
    stSpk' stKpk' stPk' gMe gPeer Frame

theorem p2Sub6FramePlaced_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (s0 : State)
    (sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8) (drKey : DRKey)
    (pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (b_2c0 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (gMe gPeer : AddrGhost) (Frame : SepProp) :
    p2Sub6FramePlaced A spkKit kpkKit pkKit s0
      sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
      stSpk' stKpk' stPk' gMe gPeer Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub6FramePlaced
      (A.atState lim st s)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      s0 sp fp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
      stSpk' stKpk' stPk' gMe gPeer Frame := rfl

/-- Placed Arm 6 (`+0x09f4 -> s0.readReg64 .x30`) budget-threaded full `SepWPp` exit bridge into
`p2ErrFrameAtPlaced`, folding the unpromoted Bob `SessionState` at `coroPtr + 0x4f8` and dropping
it via `p2_arm6_err_events_hooks_placed_ok`. -/
theorem p2_v1_arm6_ok_hooks_placed {P : Primitives} [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    {senv : IdentitySelfStoreBudgetEnv skit}
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (s0 s4 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     regIdFutPtr pkBuf skBuf v_330 v_388
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
     c0 c1 c2 c3 c4 d0 d1 d2
     u_298 u_2a0 u_80 u_88 u_90 u_a8 u_b8 u_d0
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8) (drKey : DRKey)
    (spkPrivBytes pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (pad_f4 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId u_2a8 : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_3ac : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.RegIdErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hacc : acceptKeys P inp = some drKey)
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
    (hCode : LibsignalCodeRoLoaded lsmpl s4.mem)
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
    (hCont : ∀ (sf : State) (P_f : SepProp) (evs_ss : List AllocEvent),
      FreeOnlyEvs evs_ss →
      Steps (stageP1ProgPlaced ext) s4 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s4.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim
          (M.stepEvents (p2Arm6ErrEvents skit.regIdBoxSize evs_ss 0#64) st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
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
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? inp.hdr)) ∗
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
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s4 ∗ stackAt sp stk ∗
       p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
         localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
         ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
         inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
         stSpk' stKpk' stPk' gMe gPeer Frame)
      Q Qp := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2Sub6FramePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub6FramePlaced,
    p2BobSessHeapAt, RustCliAllocBudget.repAlloc_live]
  rw [p2_head56_mid280V1_zero_eq_regIds]
  have hsess_fold := p2BobSessRegIdsV1_entails_bobInitSessionV1 (A := A.repAlloc)
    hWF hacc hwell hikBPk_len hspkBPk_len hspk_priv_len hspk_clamp
    (coroPtr + 0x4f8#64) localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 0#32 0#32
    c0 c1 c2 c3 c4 d0 d1 d2 pqBytes
    hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
  dsimp only [RustCliAllocBudget.repAlloc_live] at hsess_fold
  refine weaken_frame hsess_fold (by sep_focus) ?_
  refine weaken_frame
    (p2_bobParamsFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (p2_memRegion_a90_288_to_cells6_240 sp)) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm6 := p2_arm6_err_events_hooks_placed_ok (st0 := st) (Qp := fun _ _ => False)
    hH hDropSs3 hskitOk
    (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (bytesToBv8 (encodeEC ikBPk)) (bytesToBv8 (encodeEC inp.hdr.ikAPk))
      (bytesToBv8 (encodeEC inp.hdr.ekAPk))
      (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        (bytesToBv8 (encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
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
  refine p2_finish_err_arm6_drop
    (Drop := ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
             ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
             ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    harm6 (by sep_focus) ?_
    (fun sf P_f evs_ss hfree hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
      hCont sf P_f evs_ss hfree hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  intro evs_ss sf
  dsimp only [p2ErrFrameAtPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced,
    p2CoroScratchTailAt, p2MsgFieldsAt, RustCliAllocBudget.atState_pool]
  rw [lsLogOff_eq_pl2]
  simp only [protocolAddressAt_atState_eq_repAlloc]
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

/-- Budget-threaded placed spatial postcondition at `+0x1778` (Normal exit into Stage P3
`StageP3GenVRegs`), matching `Poll.p2OkPostAtPlaced (A.atState lim st sf)` by `rfl`. -/
def p2OkPostAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2OkPostAtPlaced
    (A.atState lim st sf)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
    G_bob st_bob hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    stSpk' stKpk' stPk' stId gMe gPeer stk Frame

theorem p2OkPostAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2OkPostAtPlaced A lim st s0 sf spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      G_bob st_bob hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2OkPostAtPlaced
      (A.atState lim st sf)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      G_bob st_bob hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame := rfl

/-- Budget-threaded placed normal-exit (`+0x1778`) spatial bridge folding `sessionStateAt` at
`coroPtr + 0xf8#64` and rejoining all Stage-P2 scratch slots into `p2OkPostAtPlaced`. -/
theorem p2_v1_ok_entails_placed {P : Primitives} [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hWF : StructuralPrims P)
    (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     regIdFutPtr pkBuf skBuf v_330 v_388
     localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
     c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8) (drKey : DRKey)
    (spkPrivBytes pqBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hacc : acceptKeys P inp = some drKey)
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
     (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
     p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
       remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
       localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
       ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
       inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
       stSpk' stKpk' stPk' gMe gPeer Frame) ⊢
    p2OkPostAtPlaced A lim st s0 sf spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        (bytesToBv8 (encodeEC ikBPk)) (bytesToBv8 (encodeEC inp.hdr.ikAPk))
        (bytesToBv8 (encodeEC inp.hdr.ekAPk))
        (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          (bytesToBv8 (encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
        remoteRegId localRegId)
      (p2BobInitSessionV1 ikBPk spkBPk inp drKey pqBytes hikBPk_len hwell.2.2.2.2.2.2.2.1
        hspkBPk_len (by rw [← hspk_clamp]; exact clampBv8List_length hspk_priv_len))
      inp.hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_v1_ok_entails_placed
    (P := P) (A := A.atState lim st sf)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentitySelfStore (A' := A.atState lim st sf) skit)
    hWF s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    regIdFutPtr pkBuf skBuf v_330 v_388
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
    c0 c1 c2 c3 c4 d0 d1 d2
    inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
    pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId
    msgVerByte b_2c0 stSpk' stKpk' stPk' stId gMe gPeer stk Frame
    hacc hwell hikBPk_len hspkBPk_len hspk_priv_len hspk_clamp
    hopkPk_len hopkSk_len hopkSk_eq
    hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget
