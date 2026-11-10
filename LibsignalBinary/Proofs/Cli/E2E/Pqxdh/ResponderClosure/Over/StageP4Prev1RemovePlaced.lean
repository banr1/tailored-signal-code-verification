/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Remove
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveIdPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKey

/-!
# Placed Stage P4.3 (`remove_pre_key`) on 1-Element `previous_sessions`

Proves `[LibsignalPlacement]` Substage P4.3 (`remove_pre_key`) over a 1-element `previous_sessions`
vector `prevVecAt [enc]` on `lsProg_518 ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Spatial resources preserved across placed Substage P4.3 over `prevVecAt [enc]`. -/
def stageP4RemovePreKeyPrev1SharedPlaced {A : RustAlloc}
    (pkKit : PreKeyStoreSpec A 0#64) (s0 s : State) : SepProp :=
  memRegion (s.sp + 0x310#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt s.sp (removePreKeyCallStack pkKit)

/-- Precondition of placed Substage P4.3 at `0#64 + pkKit.removeShimOff` over `prevVecAt [enc]`. -/
def stageP4RemovePreKeyPrev1PrePlaced {A : RustAlloc}
    (pkKit : PreKeyStoreSpec A 0#64) (s0 s : State)
    (coroPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (pst0 : pkKit.PkState) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4RemovePreKeyPrev1SharedPlaced pkKit s0 s ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  pkKit.storeAt preKeyStorePtr pst0

/-- Postcondition of placed Substage P4.3 after `Ok(())` and future deallocation (`+0x3cc`). -/
def stageP4RemovePreKeyPrev1OkPostPlaced {A : RustAlloc}
    (pkKit : PreKeyStoreSpec A 0#64) (s0 s : State)
    (coroPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (opkId : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (pst0 : pkKit.PkState) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4RemovePreKeyPrev1SharedPlaced pkKit s0 s ∗
  removePreKeyVtablesAt pkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  pkKit.storeAt preKeyStorePtr (pkKit.removeUpdate pst0 opkId (.ok ()))

/-- Postcondition of placed Substage P4.3 on `Err(e)` at `s0.readReg64 .x30`. -/
def stageP4RemovePreKeyPrev1ErrPostPlaced {A : RustAlloc}
    (pkKit : PreKeyStoreSpec A 0#64) (s0 s : State)
    (coroPtr outPtr preKeyStorePtr : BitVec 64)
    (opkId : BitVec 32) (pst0 : pkKit.PkState) (e : pkKit.RemoveErr) : SepProp :=
  stageP4RemovePreKeyPrev1SharedPlaced pkKit s0 s ∗
  removePreKeyVtablesAt pkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  speErrAt pkKit.removeErr outPtr e ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  pkKit.storeAt preKeyStorePtr (pkKit.removeUpdate pst0 opkId (.error e))

set_option maxHeartbeats 1200000 in
/-- Placed Substage P4.3 (`opkId? = some opkId`, `removeShim → +0x3cc` or `s0.readReg64 .x30`) over
`prevVecAt [enc]`. -/
theorem stageP4_removePreKey_some_prev1_vregs_remove_p4_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (pkKit : PreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpkKit : PreKeyRemoveKitPlacedOk pkKit ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    {Qfs : Prop} (s0 s : State)
    (coroPtr ctxPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (opkId : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (pst0 : pkKit.PkState) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hremOk : pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : removePreKeyCallStack pkKit ≤ 2 ^ 64)
    (hfs : FsAt pkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + pkKit.removeShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = preKeyStorePtr)
    (hx1 : s.readReg64 .x1 = opkId.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x3c0#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      pkKit.removeRel pst0 opkId (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running → s1.sp = s.sp →
      s1.trace = s.trace ++ pkKit.removeEvs opkId (.ok ()) →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 → s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ stageP4RemovePreKeyPrev1OkPostPlaced pkKit s0 s coroPtr outPtr preKeyStorePtr
        prevCap prevPtr ptCap ptPtr opkId b_2c0 pt enc pst0 G st ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : pkKit.RemoveErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      pkKit.removeRel pst0 opkId (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running → sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ pkKit.removeEvs opkId (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4RemovePreKeyPrev1ErrPostPlaced pkKit s0 s coroPtr outPtr preKeyStorePtr
        opkId pst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RemovePreKeyPrev1PrePlaced pkKit s0 s coroPtr outPtr preKeyStorePtr prevCap prevPtr
        ptCap ptPtr b_2c0 pt enc pst0 G st ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : pkKit.removeBoxSize = (BitVec.ofNat 64 pkKit.removeBoxSize).toNat :=
    (Nat.mod_eq_of_lt pkKit.removeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  have hx1_w : s.readReg32 .x1 = opkId := by simp only [State.readReg32, hx1]; bv_omega
  refine SepWPp.intro_ro (R_ro := removePreKeyVtablesAt pkKit)
    (fun hm => removePreKeyVtablesAt_placed_intro hpVt hcro.2 hm) ?_
  unfold stageP4RemovePreKeyPrev1PrePlaced stageP4RemovePreKeyPrev1SharedPlaced removePreKeyVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_shim pkKit s.sp hsp_ub)) (by sep_focus) ?_
  refine call_rocl_frame
    (spec := kitPreKeyRemoveShimSpec pkKit)
    (x := { self := preKeyStorePtr, id := opkId })
    (φ := (0#64 &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = preKeyStorePtr ∧ s.readReg32 .x1 = opkId)
    (T := A.pool ∗ stackAt s.sp pkKit.removeShimStack)
    hcro htr_pfx (hpkKit.removeShim (by decide)) hpc hrun hsp_al hlr
    (by dsimp only [kitPreKeyRemoveShimSpec]; exact Entails.of_eq (by ac_rfl))
    ⟨rfl, hx0, hx1_w⟩ (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1 hsp1_al hcs1 hcro1 hst1 => ?_)
  dsimp only [kitPreKeyRemoveShimSpec]
  simp only [sepConj_assoc]
  let boxPtr := s1.readReg64 .x0
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_shim pkKit s.sp hsp_ub).symm) (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, _, _, hvregs_cs1⟩
  have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs_cs1.trans hvregs
  have htr1_pfx : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  have hfs1 := hfs.of_steps_nil hst1 htr1
  have h2c8_un : memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h3a := p4_seg3a_vregs_placed_wp ext s1 coroPtr ctxPtr boxPtr
    (0#64 + pkKit.removeFutVtOff) (0#64 + pkKit.removePollOff) u_2c8 u_2d0
    hpc1 hrun1 rfl hx1_1 (hx19_cs1.trans hx19) (hx27_cs1.trans hx27)
  refine SepWPp.bind_sepWP_frame_steps h3a (by sep_focus)
    fun s2 P2 hpc2 hrun2 hst2 ⟨hP2, hsp2_1, htr2_1, hx0_2, _, hx8_2,
      hx19_2, hx24_2, hx25_2, hx26_2, hx27_2, _, _, hlr2, hvregs2_1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP2 (by sep_focus) ?_
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcro2 := lscro_of_steps hst2 hcro1
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2] using hsp_al
  have htr2_pfx : s0.trace <+: s2.trace := htr2_1 ▸ htr1_pfx
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rw [hsp1] at hx8_2
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_poll pkKit s.sp hsp_ub)) (by sep_focus) ?_
  let pollCall : PreKeyPollCall :=
    { fut := boxPtr, out := s.sp + 0x3e0#64, self := preKeyStorePtr, id := opkId }
  refine call_rocl_frame
    (spec := kitPreKeyRemovePollSpecE pkKit)
    (x := (pollCall, pst0))
    (φ := pkKit.envOk s2.fs.files ∧ (0#64 &&& 0xfff#64) = 0#64 ∧
          s2.readReg64 .x0 = boxPtr ∧ s2.readReg64 .x8 = s.sp + 0x3e0#64 ∧
          pkKit.removeIdOk opkId)
    (T := pkKit.removeBoxAt boxPtr preKeyStorePtr opkId 0#8 ∗
          pkKit.storeAt preKeyStorePtr pst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          A.pool ∗ stackAt s.sp pkKit.removePollStack)
    hcro2 htr2_pfx (hpkKit.removePoll (by decide)) hpc2 hrun2 hsp2_al hlr2
    (by
      dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec, pollCall]
      rw [hsp2]
      refine Entails.pure_left fun ⟨henv, hb', hx0', hx8', hrok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hb', hx0', hx8', hrok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨hfs2.envOk_here, rfl, hx0_2, hx8_2, hremOk⟩ (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 hsp3_al hcs3 hcro3 hst3 => ?_)
  dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec, pollCall]
  rw [hsp2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr3_2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_poll pkKit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x310#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_330s => SepWPp.exists_elim fun u_328s =>
    SepWPp.exists_elim fun u_320s => SepWPp.exists_elim fun u_318s =>
    SepWPp.exists_elim fun u_310s => ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _, _, hvregs_cs3⟩
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs_cs3.trans hvregs2
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by rw [hx24_cs3, hx24_2, hx24_cs1, hx24, hsp3]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_cs3, hx25_2, hx25_cs1, hx25, hsp3]
  have hx26_3 : s3.readReg64 .x26 = outPtr := hx26_cs3.trans (hx26_2.trans (hx26_cs1.trans hx26))
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2
  have htr2_s : s2.trace = s.trace := htr2_1.trans htr1
  have hst_to3 : Steps (lsProg_518 ext) s s3 := hst1.trans (hst2.trans hst3)
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ boxPtr) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + pkKit.removeFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live boxPtr pkKit.removeBoxSize 8 ∗ pkKit.removeBoxAt boxPtr preKeyStorePtr opkId 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 pkKit.removeBoxSize).toNat (8#64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 pkKit.removeBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (pkKit.removeBoxAt_memRegion _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  rcases ans with e | ⟨⟩
  ·
    dsimp only [preKeyRemovePollOutAt, unitSpePollOutAt, speErrAt]
    simp only [sepConj_assoc]
    let S := pkKit.removeErr
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (speWordsAt_eq_pollCellsAt (s.sp + 0x3e0#64)
        (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)))
      (by sep_focus) ?_
    have h3b := p4_seg3b_gen_vregs_placed_wp ext s3 coroPtr boxPtr
      (0#64 + pkKit.removeFutVtOff) (0#64 + pkKit.removeFutDropOff)
      (S.w0 e)
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      u_310s u_318s u_320s u_328s
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32) u_330s
      (speErrSpec_w0_ne_pend S e) (pkKit.removeFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h3b
    refine SepWPp.bind_sepWP_frame_steps h3b (by sep_focus)
      fun s4 P4 hpc4 hrun4 hst4 ⟨hP4, hsp4_3, htr4_3, _, hx19_4, hx21_4, hx22_4, hx23_4,
        hx24_4, hx25_4, hx26_4, _, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP4 (by sep_focus) ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hcro4 := lscro_of_steps hst4 hcro3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_futDrop_lscro hcro4 (hpkKit.removeFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      fun s5 hpc5 hrun5 hsp5_4 hsp5_al hcs5 htr5_4 hcro5 hst5 => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, _, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_errUnwind pkKit s.sp hsp_ub)) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub)) (by sep_focus) ?_
    have h3c_err := p4_seg3c_err_vregs_placed_wp ext hdealloc s5 coroPtr boxPtr
      (0#64 + pkKit.removeFutVtOff) (BitVec.ofNat 64 pkKit.removeBoxSize) 8#64
      (S.w0 e) pkKit.removeBoxSize_ne_zero (speErrSpec_w0_ne_ok S e) hpc5 hrun5 hsp5_al
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4) (hx28_cs5.trans hx28_4)
    rw [hsp5] at h3c_err
    refine SepWPp.bind_sepWP_frame_steps h3c_err (by sep_focus)
      fun s6 P6 hpc6 hrun6 hst6 ⟨hP6, hsp6_5, htr6_5, hx8_6, hx19_6, hx22_6,
        hx24_6, hx25_6, hx26_6, _, hx28_6, _, hvregs6_5⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp6 : s6.sp = s.sp := hsp6_5
    have hcro6 := lscro_of_steps hst6 hcro5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    have hx22_6' : s6.readReg64 .x22 = ((S.w1 e).extractLsb' 0 32).zeroExtend 64 :=
      hx22_6.trans (hx22_cs5.trans hx22_4)
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by rw [hx24_6, hx24_cs5, hx24_4, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by rw [hx25_6, hx25_cs5, hx25_4, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr := hx26_6.trans (hx26_cs5.trans (hx26_4.trans hx26_3))
    have hunwind := stageP4_err_unwind_550_prev1_vregs_placed_ok ext hdealloc hDropSS3 s0 s6 coroPtr
      (s.sp + 0x310#64) ptCap ptPtr outPtr (S.w0 e) prevCap prevPtr
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32)
      b_2c0 pt enc G st (PanicOomProp s0)
      hpt_le herr_ub hcro6 hpc6 hrun6 hsp6_align hx8_6 hx19_6 hx22_6'
      hx24_6' hx25_6' hx26_6' hx28_6
      (hvregs6_5.trans (hvregs_cs5.trans (hvregs4_3.trans hvregs3)))
    rw [hsp6] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    have hst_all : Steps (lsProg_518 ext) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_unw)))
    have htr_all : sf.trace = s.trace ++ pkKit.removeEvs opkId (.error e) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr3_2, htr2_s]
    refine hErr e sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hcrof ?_
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4RemovePreKeyPrev1ErrPostPlaced stageP4RemovePreKeyPrev1SharedPlaced removePreKeyVtablesAt speErrAt
    rw [stack_removePreKey_to_errUnwind pkKit s.sp hsp_ub,
        speWordsAt_eq_pollCellsAt outPtr (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)]
    exact Entails.of_eq (by ac_rfl)
  ·
    dsimp only [preKeyRemovePollOutAt]
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (unitSpePollOk_eq_exists_pollCells pkKit.removeErr (s.sp + 0x3e0#64)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h3b := p4_seg3b_gen_vregs_placed_wp ext s3 coroPtr boxPtr
      (0#64 + pkKit.removeFutVtOff) (0#64 + pkKit.removeFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_310s u_318s u_320s u_328s o1 o6 u_330s
      (by decide) (pkKit.removeFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h3b
    refine SepWPp.bind_sepWP_frame_steps h3b (by sep_focus)
      fun s4 P4 hpc4 hrun4 hst4 ⟨hP4, hsp4_3, htr4_3, _, hx19_4, hx21_4, _, hx23_4,
        hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP4 (by sep_focus) ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hcro4 := lscro_of_steps hst4 hcro3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_futDrop_lscro hcro4 (hpkKit.removeFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      fun s5 hpc5 hrun5 hsp5_4 hsp5_al hcs5 htr5_4 hcro5 hst5 => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, hx27_cs5, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_removePreKey_to_errUnwind pkKit s.sp hsp_ub)) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub)) (by sep_focus) ?_
    have h3c_ok := p4_seg3c_ok_vregs_placed_wp ext hdealloc s5 coroPtr boxPtr
      (0#64 + pkKit.removeFutVtOff) (BitVec.ofNat 64 pkKit.removeBoxSize) 8#64
      pkKit.removeBoxSize_ne_zero hpc5 hrun5 hsp5_al
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4) (hx28_cs5.trans hx28_4)
    rw [hsp5] at h3c_ok
    refine SepWPp.bind_sepWP_frame_steps h3c_ok (by sep_focus)
      fun s6 P6 hpc6 hrun6 hst6 ⟨hP6, hsp6_5, htr6_5, hx19_6,
        hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, _, hvregs6_5⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_removePreKey_to_errUnwind pkKit s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x310#64) _ _ _ _ _) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (lsProg_518 ext) s s6 := hst_to3.trans (hst4.trans (hst5.trans hst6))
    have htr_all : s6.trace = s.trace ++ pkKit.removeEvs opkId (.ok ()) := by
      rw [htr6_5, htr5_4, htr4_3, htr3_2, htr2_s]
    refine hOk s6 _ hst_all hrel hpc6 hrun6 hsp6_5 htr_all
      hx19_6 (hx24_6.trans (hx24_cs5.trans hx24_4)) (hx25_6.trans (hx25_cs5.trans hx25_4))
      (hx26_6.trans (hx26_cs5.trans (hx26_4.trans hx26_3)))
      (hx27_6.trans (hx27_cs5.trans (hx27_4.trans hx27_3)))
      hx28_6 (hvregs6_5.trans (hvregs_cs5.trans (hvregs4_3.trans hvregs3)))
      (lscro_of_steps hst6 hcro5) ?_
    unfold stageP4RemovePreKeyPrev1OkPostPlaced stageP4RemovePreKeyPrev1SharedPlaced removePreKeyVtablesAt
    exact Entails.of_eq (by ac_rfl)

theorem stageP4_removePreKey_some_prev1_vregs_kits_p4_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (pkKit : PreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpkKit : PreKeyStoreKitPlacedOk pkKit ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    {Qfs : Prop} (s0 s : State)
    (coroPtr ctxPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (opkId : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (pst0 : pkKit.PkState) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hremOk : pkKit.removeIdOk opkId) (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : removePreKeyCallStack pkKit ≤ 2 ^ 64)
    (hfs : FsAt pkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + pkKit.removeShimOff) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = preKeyStorePtr) (hx1 : s.readReg64 .x1 = opkId.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x3c0#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 → pkKit.removeRel pst0 opkId (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 → s1.status = .Running → s1.sp = s.sp →
      s1.trace = s.trace ++ pkKit.removeEvs opkId (.ok ()) →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 → s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ stageP4RemovePreKeyPrev1OkPostPlaced pkKit s0 s coroPtr outPtr preKeyStorePtr
        prevCap prevPtr ptCap ptPtr opkId b_2c0 pt enc pst0 G st ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : pkKit.RemoveErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf → pkKit.removeRel pst0 opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ pkKit.removeEvs opkId (.error e) →
      ClosureCalleeSavedP4 s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4RemovePreKeyPrev1ErrPostPlaced pkKit s0 s coroPtr outPtr preKeyStorePtr
        opkId pst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RemovePreKeyPrev1PrePlaced pkKit s0 s coroPtr outPtr preKeyStorePtr prevCap prevPtr
        ptCap ptPtr b_2c0 pt enc pst0 G st ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_removePreKey_some_prev1_vregs_remove_p4_placed ext pkKit hdealloc hDropSS3
    (preKeyRemoveKitPlacedOk_of_store hpkKit) hpVt s0 s coroPtr ctxPtr outPtr preKeyStorePtr
    prevCap prevPtr ptCap ptPtr opkId b_2c0 pt enc pst0 G st F Q
    hremOk hpt_le hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
    hx0 hx1 hx19 hx24 hx25 hx26 hx27 hlr hvregs hOk hErr

abbrev stageP4_removePreKey_some_prev1_vregs_remove_placed :=
  @stageP4_removePreKey_some_prev1_vregs_remove_p4_placed

abbrev stageP4_removePreKey_some_prev1_vregs_kits_placed :=
  @stageP4_removePreKey_some_prev1_vregs_kits_p4_placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
