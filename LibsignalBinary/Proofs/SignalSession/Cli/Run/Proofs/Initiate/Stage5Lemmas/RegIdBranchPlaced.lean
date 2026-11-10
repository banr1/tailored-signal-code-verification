/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranch
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Stage 5 `get_local_registration_id` Shim and Poll (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` proof of `stage5_reg_and_branch_placed_ok` (`+0x14b8 → lr`).
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
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
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

/-- Continuation from `offAfterUnackKyb` (`+0x14b8`) on `initProgPlaced W`: calls
`get_local_registration_id` shim + poll + future drop + box dealloc, then branches on `ans` to
`stage5_err_cleanup_placed_ok` or `stage5_accept_placed_ok`. -/
theorem stage5_reg_and_branch_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr w5c0 w5c8 w5d0 : BitVec 64} {opkId padVal w1_kyb : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {BRest : SepProp} {stk : Nat} {s0 s5 s : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk) (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
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
    (hpc : s.pc = initEntryPlaced + offAfterUnackKyb)
    (_hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp w5c0 w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame)) Q Qp := by
  intro fsp opkFlag pg kg' sg₁
  have halign_s : s.spAligned = true := spAligned_fsp hs5.ctrl.spAligned hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  apply s5_with_rodata (idVt_regIdShim_rodata_placed hStore hinv)
  conv => arg 4; unfold storesAt initArgsAtPlaced stage5ScratchAt; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_mem hinv (mid := lsmpl.base 603)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterUnackKyb] at hpc ⊢
    wp_steps
    s5_step_done
  intro _ hinv3
  refine s5_call_idRegIdShim_placed (ret_pc := initEntryPlaced + offAfterRegShim)
    hh hStore fsp x.stores ?eF3
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterRegShim]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv3
    (by wp_norm_goal)
    hpan ?ePre3 ?_
  case ePre3 =>
    inImageKitClearInvHyps
    s5_close_frame
  intro sm3 hpc3 _hrun3 hsp3 hal3 hcs3 hinv3 htr3 hfs3 hx1_3 _hnz3 _hal8_3
  have hfs3' : sm3.fs.files = x.F := hfs3.trans hfss
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hx20, hvregs] at hcs3
  rcases hcs3 with ⟨hx19_3, hx20_3, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  apply s5_with_rodata (idRegIdFut_poll_rodata_placed hinv3)
  rw [initEntryPlaced_eq_blkPl] at hpc3
  apply sepWPp_step_to_lscro_mem hinv3 (mid := lsmpl.base 568)
  · s5_clear_callees
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterRegShim] at hpc3 ⊢
    wp_steps
    s5_step_done_pc simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_3]
  intro _ hinv4
  let gReg : IdOwnPollGhost :=
    { fut := sm3.readReg64 .x0, out := fsp + 0x1600#64,
      self := x.stores, own := StoresGhost.opened.identity.own }
  refine s5_call_idRegIdPoll_placed (ret_pc := initEntryPlaced + offAfterRegPoll)
    hh hStore fsp gReg ?eF4
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_3]) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal3)
    (by dsimp only [initEntryPlaced, offAfterRegPoll]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]) hinv4
    (by dsimp only [gReg]; wp_norm_goal)
    (by dsimp only [gReg]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    opened_own_regId_pre.1 opened_own_regId_pre.2
    hpan ?ePre4 ?_
  case ePre4 => dsimp only [gReg]; s5_close_frame
  intro sm4 ans hpc4 hrun4 hsp4 hal4 hcs4 hinv4 htr4 hfs4 hansReg
  conv => arg 4; dsimp only [gReg]
  have hfs4' : sm4.fs.files = x.F := hfs4.trans hfs3'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_3, hx20_3, hvregs_3] at hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, _, _, _, _, _, _, _, hvregs_4⟩
  have hansReg' : ans = StoresGhost.opened.identity.regId cliIo.rd x.F := by
    dsimp only [gReg, IdGhost.regId] at hansReg ⊢
    simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hfs3'] using hansReg
  s5_have_eq hpRegOut : idRegIdOutAt A (fsp + 0x1600#64) ans ∗ ?regOutRem := by s5_ac_rfl
  refine s5_apply_lens hpRegOut fun R3 m3 hm3 => ?_
  obtain ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hrw0_ne3, hmAns, hansBranch⟩ :=
    unpack_idRegIdOutAt A fsp x.ret ans R3 m3 hm3
  simp only [← sepConj_assoc] at hmAns
  refine ⟨_, hmAns, ?_⟩
  refine sepWPp_conseq ?pre1
    (stage5_reg_drop_dealloc_placed_ok (fsp := fsp) (storesPtr := x.stores) (futPtr := sm3.readReg64 .x0)
      (rw0 := rw0) (rw1 := rw1) (rw2 := rw2) (rw3 := rw3) (rw4 := rw4) (rw5 := rw5)
      (Frame56 := ?frame56) hh hStore hstk hstk64 hrw0_ne3
      hpc4 hrun4 hsp4 hal4 hvregs_4 hinv4 htr4 hpan
      fun RoExtra sm6 hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs6
          hx19_6 hx20_6 hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 =>
        sepWPp_conseq ?pre2
          (stage5_branch_after_reg_placed_ok (dataPtr := dataPtr) (futPtr := sm3.readReg64 .x0)
            (rw0 := rw0) (rw1 := rw1) (rw2 := rw2) (rw3 := rw3) (rw4 := rw4) (rw5 := rw5)
            (padVal := padVal) (w1_kyb := w1_kyb) (ans := ans) (kg := kg) (SpeH := SpeH)
            (Extra := ?extraBranch)
            hh hStore hLocal hS hinitOk hstk hstk64 hs5
            halice hkgBytes hkemLen hkyberKey hekLen hkpkLen hfoldBundle
            hansReg' hrw0_ne3 hansBranch hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs0
            (hfs6.trans hfs4') (hx19_6.trans hx19_4) (hx20_6.trans hx20_4)
            hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hpost hpan))
  case pre1 =>
    inImageKitClearInvHyps
    conv =>
      lhs
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [
        BitVec.add_zero, hx1_3,
        show fsp + 1480#64 = fsp + 0x5c8#64 by bv_omega,
        show fsp + 1488#64 = fsp + 0x5d0#64 by bv_omega]
    exact Entails.of_eq (by s5_ac_rfl)
  case pre2 =>
    inImageKitClearInvHyps
    dsimp only [storesAt, initArgsAtPlaced, stage5ScratchAt]
    conv =>
      lhs
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [
        BitVec.add_zero,
        show fsp + 1472#64 = fsp + 0x5c0#64 by bv_omega]
    exact Entails.of_eq (by s5_ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
