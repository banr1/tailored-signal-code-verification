/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTail
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Stage 5 Accept Path (`[LibsignalPlacement]`): `save_identity`, `memcpy`, and `promote_state`

Relocatable `[LibsignalPlacement]` proof of the Stage 5 accept path (`+0x163c → +0x1768 → lr`) on
`initProgPlaced W`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding LibsignalCodeRoLoaded withLsCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced

set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs_placed (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

private theorem stage5_memcpy_and_promote_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem} {x : InitGhost} {be : PreKeyBundleFields}
    {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey}
    {hdr : SignalPqxdh.HandshakeHdr} {pqspkPtr dataPtr : BitVec 64}
    {opkId reg padVal w1_kyb : BitVec 32} {sg : SessionGhost}
    {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {w5c0 w5c8 w5d0 : BitVec 64} {BRest Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk) (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle : ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
      ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hpc : s.pc = initEntryPlaced + offSaveDeallocDone)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++ unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₂ : SessionGhost := { sg with pending := some pg, kyber := some kg', regIds := unpack32 x.bundle.regId ++ unpack32 reg }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A x.stores StoresGhost.opened.identity.own ∗
        dirAt A (x.stores + 0x28#64) (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers ∗
        dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗ dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗ dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗ dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗ ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗ memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗ stage5ScratchAt fsp w5c0 w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp := by
  intro fsp opkFlag pg kg' sg₂
  have hMemcpy := s5_memcpy_ok_at_placed hh
  have hPromote := hLocal.promoteState
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  conv => arg 4; unfold stage5ScratchAt; simp only [sepConj_assoc]
  s5_have_eq hpPreMem :
      (memRegion (fsp + 0x1600#64) 48 ∗ memRegion (fsp + 0x1630#64) 296) ∗ ?remPreMem := by
    s5_ac_rfl
  refine sepWPp_conseq
    (Entails.trans (Entails.of_eq hpPreMem) (sepConj_mono_left (Entails.of_eq (scratch_sret344_eq fsp)))) ?_
  have hssDecomp : sessionStateAt A (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage = _ :=
    RawByteMove.sessionStateAt_eq_inline_sep_heap A (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage
  s5_rw_pre hssDecomp
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro ssBytes
  refine SepWPp.pure_elim fun ⟨hssLen, hssInl⟩ => ?_
  s5_have_eq hpSvStep5 : ((fsp + 0x5b9#64) ↦₈ 1#8) ∗ ?remSvStep5 := by s5_ac_rfl
  refine sepWPp_conseq (Entails.of_eq hpSvStep5) ?_
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_mem hinv (mid := lsρ memcpyName)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSaveDeallocDone, lsρ] at hpc ⊢
    wp_steps
    simp (config := { failIfUnchanged := false }) only [hx26]
    try wp_steps
    s5_step_done
  intro _ hinv5
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_memcpy_placed (ret_pc := initEntryPlaced + offAfterMemcpy)
    hh hMemcpy fsp (fsp + 0x1600#64) (fsp + 0x460#64) ssBytes ?svF5
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterMemcpy]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv5
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hssLen])
    hpan ?svPre5 ?_
  case svPre5 => rw [hssLen]; s5_close_frame
  intro sm5 hpc5 hrun5 hsp5 hal5 hcs5 hinv5 htr5 hfs5
  have hfs5' : sm5.fs.files = x.F := hfs5.trans hfss
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hvregs] at hcs5
  rcases hcs5 with ⟨hx19_5, _, _, _, _, _, _, _, _, _, _, hvregs_5⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; unfold initFreshRecAt; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc5
  apply sepWPp_step_to_lscro_mem hinv5 (mid := lsmpl.base 47)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterMemcpy] at hpc5 ⊢
    wp_steps
    s5_step_done
  intro _ hinv6
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (prom_le_stkSub hstk) (stkSub_hi hstk64),
        stackAt_96_eq_promoteState_cells fsp]
    simp only [sepConj_assoc]
  have haRec18 : (fsp + 0x128#64) + 0x18#64 = fsp + 0x140#64 := by bv_omega
  have haRec20 : (fsp + 0x128#64) + 0x20#64 = fsp + 0x148#64 := by bv_omega
  refine s5_call_promoteState_placed (ret_pc := initEntryPlaced + offStore)
    hh hPromote fsp (fsp + 0x128#64) (fsp + 0x1600#64) ssBytes ?svF6
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal5)
    (by dsimp only [initEntryPlaced, offStore]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr5]) hinv6
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5]) hssLen
    hpan ?svPre6 ?_
  case svPre6 => rw [haRec18, haRec20]; s5_close_frame
  intro sm6 hpc6 hrun6 hsp6 hal6 hcs6 hinv6 htr6 hfs6
  have hfs6' : sm6.fs.files = x.F := hfs6.trans hfs5'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_5, hsp5, hvregs_5] at hcs6
  rcases hcs6 with ⟨hx19_6, _, hx21_6, _, _, _, _, _, _, _, _, hvregs_6⟩
  conv => arg 4; rw [haRec18]
  s5_rw_pre (stackAt_96_eq_promoteState_cells fsp).symm
  s5_rw_pre (s5_stackAt_sub_split fsp (prom_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hmove2 := RawByteMove.sessionStateAt_move_bytes_twice A
    (fsp + 0x460#64) (fsp + 0x1600#64) (fsp + 0x140#64)
    sg₂ ss.setUnacknowledgedPreKeyMessage hssInl
  obtain ⟨hrecFold, hencLt, hinitEq⟩ := sessionRecord_promote_accept
    (A := A) (W := W) (X := X) (x := x) (be := be) (kp := kp) (dk := dk) (hdr := hdr)
    (opkId := opkId) (reg := reg) (sg := sg) (ss := ss)
    (dataPtr := dataPtr) (padVal := padVal) (w1 := w1_kyb) (kg := kg)
    fsp hbe htrusted hkp hreg hopkId hkeys hinitSess hpqLen halice hkgBytes hkemLen hkyberKey
  have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins =
      some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
        (Record.encodeRecord ⟨some (RecordX.sessionOfX
          (fun _ => initiatorRecordExtras ⟨kp.privateKey.bytes, reg⟩ be ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt))
          ⟨initParty x.peer.val, ss.setUnacknowledgedPreKeyMessage, 0, [0]⟩)⟩), ())) := by
    rw [hS]; exact hinitEq
  refine sepWPp_conseq ?_
    (stage5_store_and_cleanup_placed_ok (kp := kp) (pqspkPtr := pqspkPtr) (opkId := opkId) (sg₂ := sg₂) (w5c0 := w5c0) (w5c8 := w5c8)
      (w5d0 := w5d0) (b5b8 := 0#8) (Extra := Extra)
      hh hStore hLocal hinitOk hstk hstk64 hekLen hkpkLen hencLt hans
      hpc6 hrun6 hsp6 hsp_align hvregs_6 hinv6 htr6 hfs0 hfs6'
      hx19_6 hx21_6 hpost hpan)
  s5_have_eq hpM1 :
      (((fsp + 0x140#64) ↦ₛ ssBytes) ∗ ((fsp + 0x1600#64) ↦ₛ ssBytes) ∗
        ((fsp + 0x460#64) ↦ₛ ssBytes) ∗
        RawByteMove.sessionHeap A sg₂ ss.setUnacknowledgedPreKeyMessage) ∗ ?remM1 := by
    conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpM1) (Entails.trans (sepConj_mono_left hmove2) ?_)
  rw [← scratch_sret344_eq fsp]
  s5_have_eq hpM2 :
      ((((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
        ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage) ∗
      (((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗
        ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest)) ∗ ?remM2 := by
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpM2)
    (Entails.trans (sepConj_mono_left (sepConj_mono hrecFold hfoldBundle)) ?_)
  dsimp only [stage5ScratchAt, sg₂]
  exact Entails.of_eq (by s5_ac_rfl)

/-- Accepted path from `offSave` (`+0x163c`): writes `local_registration_id = reg` and
`remote_registration_id = x.bundle.regId`, runs `save_identity` shim + poll + future drop + box
dealloc, and hands off to `stage5_memcpy_and_promote_placed_ok`. -/
theorem stage5_accept_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr : BitVec 64} {opkId reg padVal w1_kyb : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {w5c8 w5d0 : BitVec 64} {BRest Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk) (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle :
      ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hpc : s.pc = initEntryPlaced + offSave)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx27 : (s.readReg64 (.gpr 27#5)).setWidth 32 = reg)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let basePk : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, basePk.serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++ unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A x.stores StoresGhost.opened.identity.own ∗
        dirAt A (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗ dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗ dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗ dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗ ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗ memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗ stage5ScratchAt fsp (fsp + 0x460#64) w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp := by
  intro fsp opkFlag basePk pg kg' sg₁
  have hDealloc := s5_dealloc_ok_at_placed hh
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  s5_have_eq hpRegEq :
      sessionStateAt A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗ ?regRem := by
    s5_ac_rfl
  refine s5_apply_lens hpRegEq fun R m hm => ?_
  obtain ⟨oldRem, oldLoc, SSRest, hmReg, hfoldRegIds⟩ :=
    sessionState_regIds_lens A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage R m hm
  simp only [← sepConj_assoc] at hmReg
  refine ⟨_, hmReg, ?_⟩
  conv =>
    arg 4
    rw [show (fsp + 0x460#64) + 0x150#64 = fsp + 0x5b0#64 by bv_omega,
        show (fsp + 0x460#64) + 0x154#64 = fsp + 0x5b4#64 by bv_omega]
  apply s5_with_rodata (idVt_saveShim_rodata_placed hStore hinv)
  conv => arg 4; unfold initArgsAtPlaced stage5ScratchAt; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_mem hinv (mid := lsmpl.base 600)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSave] at hpc ⊢
    wp_steps
    s5_step_done
  intro _ hinv1
  let sg₂ : SessionGhost :=
    { sg with pending := some pg, kyber := some kg',
              regIds := unpack32 x.bundle.regId ++ unpack32 reg }
  have hregFold :
      (((fsp + 0x460#64) + 0x150#64) ↦₃₂ x.bundle.regId) ∗
        (((fsp + 0x460#64) + 0x154#64) ↦₃₂ reg) ∗ SSRest ⊢
        sessionStateAt A (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage :=
    hfoldRegIds x.bundle.regId reg
  let cSaveShim : IdentityShimCall :=
    { self := x.stores, addrA := x.peerA, keyA := x.bundleA + 0x78#64 }
  let cSave : IdentityCall :=
    { addrA := x.peerA, addr := x.peer, keyA := x.bundleA + 0x78#64, key := x.bundle.idKey }
  refine s5_call_idSaveShim_placed (ret_pc := initEntryPlaced + offAfterSaveShim)
    hh hStore fsp cSaveShim ?svF1
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterSaveShim]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv1
    (by dsimp only [cSaveShim]; wp_norm_goal) (by dsimp only [cSaveShim]; wp_norm_goal)
    (by dsimp only [cSaveShim]; wp_norm_goal) hpan ?svPre1 ?_
  case svPre1 =>
    s5_have_eq hpull :
        ((((fsp + 0x460#64) + 0x150#64) ↦₃₂ x.bundle.regId) ∗
          (((fsp + 0x460#64) + 0x154#64) ↦₃₂ reg) ∗ SSRest) ∗ ?restSv1 := by
      conv =>
        lhs
        simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hx27]
        rw [show fsp + 0x5b0#64 = (fsp + 0x460#64) + 0x150#64 by bv_omega,
            show fsp + 0x5b4#64 = (fsp + 0x460#64) + 0x154#64 by bv_omega]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull) (Entails.trans (sepConj_mono_left hregFold) ?_)
    s5_close_frame
  intro sm1 hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1 hx1_1 hnz1 hal8_1
  have hx1_1_gpr : sm1.readReg64 (.gpr 1#5) = lsρ idSaveFutVtSym := hx1_1
  conv => arg 4; dsimp only [cSaveShim]
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hfss
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hx20, hvregs] at hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  apply s5_with_rodata (idSaveFut_poll_rodata_placed hinv1)
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_mem hinv1 (mid := lsmpl.base 565)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSaveShim] at hpc1 ⊢
    wp_steps
    s5_step_done_pc simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1]
  intro _ hinv2
  let gSave : IdPollGhost :=
    { call := { call := cSave, fut := sm1.readReg64 .x0, out := fsp + 0x1600#64 },
      self := x.stores, peers := StoresGhost.opened.identity.peers }
  have hwfPeers :
      ∀ bs, gSave.peers.get cliIo.rd sm1.fs.files x.peer.val.name = .ok bs → IdFileWf bs := by
    dsimp only [gSave, cSave]; rw [hfs1']
    obtain ⟨bs₀, hbs₀, hwf₀⟩ := hinitOk.idGet
    intro bs hbs; rw [hbs₀] at hbs; injection hbs with hEq; exact hEq ▸ hwf₀
  refine s5_call_idSavePoll_placed (ret_pc := initEntryPlaced + offAfterSavePoll)
    hh hStore fsp gSave ?svF2
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1]) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offAfterSavePoll]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]) hinv2
    (by dsimp only [gSave, cSave]; wp_norm_goal)
    (by dsimp only [gSave, cSave]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    hinitOk.nameLt opened_peers_bounds.1 opened_peers_bounds.2
    ⟨by dsimp only [gSave, cSave]; exact hinitOk.idPathOk,
     by dsimp only [gSave, cSave]; exact hinitOk.idPathLt⟩ hwfPeers
    hpan ?svPre2 ?_
  case svPre2 => dsimp only [gSave, cSave]; s5_close_frame
  intro sm2 gr pAns hpc2 hrun2 hsp2 hal2 hcs2 hinv2 htr2 hfs2 hgr hpAns
  conv => arg 4; dsimp only [gSave, cSave]
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx20_1, hx1_1, hsp1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, hx22_2, hx23_2, _, _, hx26_2, _, _, _, hvregs_2⟩
  have hgr' : gr = StoresGhost.opened.identity.peers.get cliIo.rd x.F x.peer.val.name := by
    dsimp only [gSave, cSave] at hgr
    simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hfs1'] using hgr
  obtain ⟨cg, hsaveOk, hpeersEq⟩ := idSave_ok_of_trusted htrusted hgr' hpAns
  have houtUnpack :
      idSaveOutAt A (fsp + 0x1600#64) (idSaveOf pAns x.bundle.idKey) ⊢
        ∃∗ sw1 : BitVec 64, ∃∗ sw2 : BitVec 64, ∃∗ sw3 : BitVec 64,
        ∃∗ sw4 : BitVec 64, ∃∗ sw5 : BitVec 64,
          ⌜sw1.setWidth 32 = (if cg == .replacedExisting then 1#32 else 0#32)⌝ ∗
          ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ sw1) ∗ (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ sw2) ∗
          (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ sw3) ∗ (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ sw4) ∗
          (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ sw5) := by
    rw [hsaveOk]; dsimp only [idSaveOutAt]
    refine Entails.trans
      (sepConj_mono_right (u32_tail36_words5 (fsp + 0x1600#64)
        (if cg == .replacedExisting then 1#32 else 0#32))) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun sw1 => Entails.sepExists_elim fun sw2 =>
      Entails.sepExists_elim fun sw3 => Entails.sepExists_elim fun sw4 =>
      Entails.sepExists_elim fun sw5 => ?_
    exact Entails.sepExists_right sw1 (Entails.sepExists_right sw2
      (Entails.sepExists_right sw3 (Entails.sepExists_right sw4
        (Entails.sepExists_right sw5 (Entails.of_eq (by ac_rfl))))))
  s5_have_eq hpOutEq :
      idSaveOutAt A (fsp + 0x1600#64) (idSaveOf pAns x.bundle.idKey) ∗ ?outRem := by
    s5_ac_rfl
  refine sepWPp_conseq (Entails.trans (Entails.of_eq hpOutEq) (sepConj_mono_left houtUnpack)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro sw1; apply SepWPp.exists_elim; intro sw2
  apply SepWPp.exists_elim; intro sw3; apply SepWPp.exists_elim; intro sw4
  apply SepWPp.exists_elim; intro sw5; refine SepWPp.pure_elim fun _ => ?_
  have hsretOffs := sret_word_offs fsp
  conv => arg 4; rw [hsretOffs.1, hsretOffs.2.1, hsretOffs.2.2.1, hsretOffs.2.2.2.1, hsretOffs.2.2.2.2]
  apply s5_with_rodata (idSaveFut_drop_rodata_placed hinv2)
  generalize hdrop : lsmpl.base 547 = dropAddr
  s5_have_eq hpSvStep3 :
      (((lsρ idSaveFutVtSym) ↦₆₄ᵣ dropAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ sw1) ∗ ((fsp + 5648#64) ↦₆₄ sw2) ∗ ((fsp + 5656#64) ↦₆₄ sw3) ∗
        ((fsp + 5664#64) ↦₆₄ sw4) ∗ ((fsp + 5672#64) ↦₆₄ sw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ sm1.readReg64 (.gpr 0#5))) ∗ ?remSvStep3 := by
    conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hsp1, hx1_1_gpr]
    s5_ac_rfl
  suffices hAfterDrop : ∀ (sm3 : State) (dAddr : BitVec 64) {P3 : SepProp},
      P3 = (((lsρ idSaveFutVtSym) ↦₆₄ᵣ dAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ sw1) ∗ ((fsp + 5648#64) ↦₆₄ sw2) ∗ ((fsp + 5656#64) ↦₆₄ sw3) ∗
        ((fsp + 5664#64) ↦₆₄ sw4) ∗ ((fsp + 5672#64) ↦₆₄ sw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ sm1.readReg64 (.gpr 0#5))) ∗ ?remSvStep3 →
      sm3.pc = initEntryPlaced + offSaveDealloc →
      sm3.status = .Running →
      sm3.sp = fsp →
      sm3.spAligned = true →
      sm3.readReg64 (.gpr 19#5) = x.ret →
      sm3.readReg64 (.gpr 20#5) = fsp + 0x460#64 →
      sm3.readReg64 (.gpr 22#5) = lsρ idSaveFutVtSym →
      sm3.readReg64 (.gpr 23#5) = sm1.readReg64 (.gpr 0#5) →
      sm3.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      calleeSavedVRegs sm3 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sm3.mem →
      sm3.trace = s0.trace →
      sm3.fs.files = x.F →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm3 P3 Q Qp by
    rw [initEntryPlaced_eq_blkPl] at hpc2
    by_cases hdropNe : dropAddr = 0#64
    · apply sepWPp_step_to_lscro_mem_framed hinv2 hpSvStep3 (mid := initEntryPlaced + offSaveDealloc)
      · s5_clear_callees
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSavePoll, offSaveDealloc] at hpc2 ⊢
        rw [initEntryPlaced_eq_blkPl]
        wp_steps
        simp (config := { failIfUnchanged := false }) only [
          hdropNe, beq_self_eq_true, ↓reduceIte]
        try wp_steps
        s5_step_done
      intro _ hinv3; clear hpSvStep3
      exact hAfterDrop _ 0#64 rfl
        (by dsimp only [initEntryPlaced, offSaveDealloc]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp2])
        (by simpa [State.spAligned, wp_norm, arm64_norm, hsp2] using hal2)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_2])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_2])
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [calleeSavedVRegs, wp_norm, arm64_norm, hvregs_2])
        hinv3
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr2])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs2'])
    · apply sepWPp_step_to_lscro_mem_framed hinv2 hpSvStep3 (mid := dropAddr)
      · s5_clear_callees
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSavePoll] at hpc2 ⊢
        wp_steps
        simp (config := { failIfUnchanged := false }) only [
          beq_eq_false_iff_ne.mpr hdropNe, Bool.false_eq_true, ↓reduceIte]
        try wp_steps
        s5_step_done
      intro _ hinv3; clear hpSvStep3; subst hdrop
      refine s5_call_futDrop_placed (ret_pc := initEntryPlaced + offSaveDealloc)
        hh hStore fsp _
        (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp2])
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hal2)
        (by dsimp only [initEntryPlaced, offSaveDealloc]; wp_norm_goal; try rfl)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr2]) hinv3
        hpan (Entails.refl _) ?_
      intro sm3 hpc3 hrun3 hsp3 hal3 hcs3 hinv3 htr3 hfs3
      have hfs3' : sm3.fs.files = x.F := hfs3.trans hfs2'
      simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_2, hx20_2, hx22_2, hx23_2, hx26_2, hvregs_2] at hcs3
      rcases hcs3 with ⟨hx19_3, hx20_3, _, hx22_3, hx23_3, _, _, hx26_3, _, _, _, hvregs_3⟩
      exact hAfterDrop sm3 (lsmpl.base 547) rfl hpc3 hrun3 hsp3 hal3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hvregs_3 hinv3 htr3 hfs3'
  clear hpSvStep3
  intro sm3 dAddr P3 hP3Eq hpc3 hrun3 hsp3 hal3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hvregs_3 hinv3 htr3 hfs3'
  subst hP3Eq
  apply s5_with_rodata (idSaveFut_size_rodata_placed hinv3)
  apply s5_with_rodata (idSaveFut_align_rodata_placed hinv3)
  rw [initEntryPlaced_eq_blkPl] at hpc3
  apply sepWPp_step_to_lscro_mem hinv3 (mid := lsρ lsRustDeallocSymCli)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSaveDealloc, lsρ] at hpc3 hx22_3 ⊢
    wp_steps
    s5_step_done
  intro _ hinv4
  have hboxMem := idSaveBoxAt_entails_memRegion32 (sm1.readReg64 .x0) x.stores
    x.peerA (x.bundleA + 0x78#64) 1#8
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (ret_pc := initEntryPlaced + offSaveDeallocDone)
    hh hDealloc fsp (sm1.readReg64 .x0) 32 8 ?svF4
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal3)
    (by dsimp only [initEntryPlaced, offSaveDeallocDone]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]) hinv4
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_3])
    (by wp_norm_goal) (by wp_norm_goal) layoutOk_32_8
    hpan ?svPre4 ?_
  case svPre4 =>
    s5_have_eq hpull :
        idSaveBoxAt (sm1.readReg64 .x0) x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗ ?restSvBox := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp3]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hboxMem) ?_)
    s5_close_frame
  intro sm4 hpc4 hrun4 hsp4 hal4 hcs4 hinv4 htr4 hfs4
  have hfs4' : sm4.fs.files = x.F := hfs4.trans hfs3'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_3, hx20_3, hx26_3, hvregs_3] at hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, _, _, _, hx26_4, _, _, _, hvregs_4⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hw48 := words6_entails_memRegion48 (fsp + 0x1600#64) 0xFFFFFFFFFFFFFFFE#64 sw1 sw2 sw3 sw4 sw5
  have hsretSymm := sret_word_offs_symm fsp
  refine sepWPp_conseq ?_
    (stage5_memcpy_and_promote_placed_ok (pqspkPtr := pqspkPtr) (dataPtr := dataPtr) (opkId := opkId) (padVal := padVal) (w1_kyb := w1_kyb)
      (sg := sg) (kg := kg) (w5c0 := sm1.readReg64 .x0)
      (w5c8 := lsρ idSaveFutVtSym) (w5d0 := w5d0)
      (Extra := ?extraSv)
      hh hStore hLocal hS hinitOk hstk hstk64
      hbe htrusted hkp hreg hopkId hkeys hinitSess hpqLen halice hkgBytes hkemLen hkyberKey
      hekLen hkpkLen hfoldBundle
      hpc4 hrun4 hsp4 hsp_align hvregs_4 hinv4 htr4 hfs0 hfs4'
      hx19_4 hx20_4 hx26_4 hpost hpan)
  s5_have_eq hpW48 :
      (((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ sw1) ∗ (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ sw2) ∗
        (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ sw3) ∗ (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ sw4) ∗
        (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ sw5)) ∗ ?remSw48 := by
    conv =>
      lhs
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
      rw [hsretSymm.1, hsretSymm.2.1, hsretSymm.2.2.1, hsretSymm.2.2.2.1, hsretSymm.2.2.2.2]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpW48) (Entails.trans (sepConj_mono_left hw48) ?_)
  have hpeersDirEq :
      idSavePeers StoresGhost.opened.identity.peers x.peer.val.name x.bundle.idKey pAns =
        (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers :=
    congrArg IdGhost.peers hpeersEq
  conv => lhs; rw [hpeersDirEq]
  dsimp only [initArgsAtPlaced, stage5ScratchAt, sg₂]
  exact Entails.of_eq (by dsimp only [Reg.x0, fsp]; s5_ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
