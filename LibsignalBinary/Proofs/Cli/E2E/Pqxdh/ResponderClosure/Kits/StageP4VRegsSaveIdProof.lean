/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveId

/-!
# Stage P4.1 Dispatch Proof with `calleeSavedVRegs`

Proves `stageP4_saveIdentity_dispatch_vregs_kits`, threading `calleeSavedVRegs` (`D8..D15`) across
Substage P4.1 (`+0x34dc → kyberMarkUsedShimAddr` on `Ok c` and `s0.readReg64 .x30` on `Err ()`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 1200000 in
/-- Substage P4.1 dispatch (`IdentityKeyStore::save_identity`,
`+0x34dc → kyberMarkUsedShimAddr` / `x30`) preserving `calleeSavedVRegs`. -/
theorem stageP4_saveIdentity_dispatch_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hiVt : IdentityVtablesOk img ikit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddrOk : ikit.addrOk peer.val)
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : saveIdCallStack ikit ≤ 2 ^ 64)
    (hkSlot : ∀ {s' : State} {P : SepProp}, img.FrozenLoaded s' → (s'.mem ⊨ P) →
      s'.mem ⊨ ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗ P)
    (hfs : FsAt ikit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (c : IdentityChange) (s1 : State) (P1 : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      ikit.saveRel ist0 peer.val remoteIk (.ok c) →
      s1.pc = kyberMarkUsedShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) →
      s1.readReg64 .x0 = kyberStorePtr →
      s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 →
      s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 →
      s1.readReg64 .x3 = msgPtr + 0xa8#64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 =
        (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x350#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ stageP4SaveIdOkPost img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 c G st ∗ F) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      ikit.saveRel ist0 peer.val remoteIk (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4SaveIdErrPost img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk ist0 ∗ F) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4SaveIdPre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
        kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G st ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : ikit.saveBoxSize = (BitVec.ofNat 64 ikit.saveBoxSize).toNat :=
    (Nat.mod_eq_of_lt ikit.saveBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine SepWPp.intro_ro
    (R_ro := saveIdVtablesAt ikit ∗ ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr))
    (fun hm => by rw [sepConj_assoc]; exact saveIdVtablesAt_intro hiVt hF (hkSlot hF hm)) ?_
  unfold stageP4SaveIdPre stageP4SaveIdShared saveIdVtablesAt
  simp only [sepConj_assoc]
  let ptLen := BitVec.ofNat 64 pt.length
  have hpt_sp :
      ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗ ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((s.sp + 0x288#64) ↦₆₄ ptLen) =
      ((s.sp + 0x278#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((s.sp + 0x27c#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x284#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x28c#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (s.sp + 0x278#64) ptCap ptPtr ptLen
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have h280_un :
      memRegion (coroPtr + 0x280#64) 24 =
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 32,
        ((coroPtr + 0x280#64) ↦₃₂ u0) ∗ ((coroPtr + 0x284#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x28c#64) ↦₆₄ u2) ∗ ((coroPtr + 0x294#64) ↦₃₂ u3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion24_eq_unaligned_cells (coroPtr + 0x280#64)
  have h250_un :
      memRegion (s.sp + 0x250#64) 20 =
      ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((s.sp + 0x250#64) ↦₆₄ u0) ∗ ((s.sp + 0x258#64) ↦₆₄ u1) ∗
        ((s.sp + 0x260#64) ↦₃₂ u2) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_eq_cells (s.sp + 0x250#64)
  refine SepWPp.weaken_frame (Entails.of_eq hpt_sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq h280_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_coro294 => SepWPp.exists_elim fun u_coro28c =>
    SepWPp.exists_elim fun u_coro284 => SepWPp.exists_elim fun u_coro280 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq h250_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  have h1a := p4_seg1a_vregs_ext_wp img.base ext s coroPtr idStorePtr ikit.id_vt
    (img.base + ikit.saveShimOff) remoteAddrPtr remoteIkPtr
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_250 u_258 u_coro284 u_coro28c v_3d0
    (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_260 u_coro280 u_coro294
    hpc hrun hsp_al hx19 hx25 hx28
  refine SepWPp.bind_sepWP_frame_steps h1a (by sep_focus)
    fun s1 P1 hpc1 hrun1 hst1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1,
      hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hlr1, hvregs1⟩ => ?_
  refine SepWPp.weaken_frame hP1 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hpt_sp.symm) (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ ptLen.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells20_entails_memRegion20 (s.sp + 0x250#64) _ _ _
  refine SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hF1 : img.FrozenLoaded s1 := hF.of_keepsFrozen hst1.keepsFrozen
  have hsym1 : s1.symtab = img.symtab := hst1.symtab_eq.trans hsym
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have htr1_pfx : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  have hfs1 := hfs.of_steps_nil hst1 htr1
  refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub))
    (by sep_focus) ?_
  refine SepWPp.call_inImage_frame
    (x := ({ self := idStorePtr, addrA := remoteAddrPtr, keyA := remoteIkPtr } : IdentityShimCall))
    (φ := s1.readReg64 .x0 = idStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
          s1.readReg64 .x2 = remoteIkPtr)
    (T := A.pool ∗ stackAt s.sp ikit.saveShimStack)
    hF1 hsym1 htr1_pfx hikit.saveShim hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [kitSaveShimSpec]; rw [hsp1]; exact Entails.of_eq (by ac_rfl))
    ⟨hx0_1, hx1_1, hx2_1⟩ (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 hst2 => ?_)
  dsimp only [kitSaveShimSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have htr2_pfx : s0.trace <+: s2.trace := htr2_1 ▸ htr1_pfx
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs_cs2⟩
  let saveIdFutPtr := s2.readReg64 .x0
  have h2c8_un :
      memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h1b := p4_seg1b_vregs_ext_wp img.base ext s2 coroPtr ctxPtr saveIdFutPtr
    (img.base + ikit.saveFutVtOff) (img.base + ikit.savePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine SepWPp.bind_sepWP_frame_steps h1b (by sep_focus)
    fun s3 P3 hpc3 hrun3 hst3 ⟨hP3, hsp3_2, htr3_2, hx0_3, _, hx8_3,
      hx19_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _, hlr3, hvregs3_2⟩ => ?_
  refine SepWPp.weaken_frame hP3 (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hF3 : img.FrozenLoaded s3 := hF2.of_keepsFrozen hst3.keepsFrozen
  have hsym3 : s3.symtab = img.symtab := hst3.symtab_eq.trans hsym2
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have htr3_pfx : s0.trace <+: s3.trace := htr3_2 ▸ htr2_pfx
  have hfs3 := hfs2.of_steps_nil hst3 htr3_2
  rw [hsp2] at hx8_3
  refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : IdentityPollCall :=
    { fut := saveIdFutPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, keyA := remoteIkPtr, key := remoteIk } }
  refine SepWPp.call_inImage_frame
    (spec := withLogOff (kitSavePollSpecE ikit) img)
    (x := (pollCall, idStorePtr, ist0))
    (φ := ikit.envOk s3.fs.files ∧ s3.readReg64 .x0 = saveIdFutPtr ∧
          s3.readReg64 .x8 = s.sp + 0x3e0#64 ∧ ikit.addrOk peer.val)
    (T := ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 0#8 ∗
          ikit.identityAt idStorePtr ist0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗ A.pool ∗
          stackAt s.sp ikit.savePollStack ∗ logOff img)
    hF3 hsym3 htr3_pfx hikit.savePoll hpc3 hrun3 hsp3_al hlr3
    (by
      dsimp only [withLogOff, kitSavePollSpecE, withEnvPre, kitSavePollSpec, pollCall]
      rw [hsp3]
      simp only [sepConj_assoc]
      refine Entails.pure_left fun ⟨henv, hx0', hx8', haok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hx0', hx8', haok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨hfs3.envOk_here, hx0_3, hx8_3, haddrOk⟩ (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hF4 hsym4 hst4 => ?_)
  dsimp only [withLogOff, kitSavePollSpecE, withEnvPre, kitSavePollSpec, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x2b0#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0s => SepWPp.exists_elim fun u_2c8s =>
    SepWPp.exists_elim fun u_2c0s => SepWPp.exists_elim fun u_2b8s =>
    SepWPp.exists_elim fun u_2b0s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, hx27_cs4, hx28_cs4, _, hvregs_cs4⟩
  have hvregs_4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
    hvregs_cs4.trans (hvregs3_2.trans (hvregs_cs2.trans (hvregs1.trans hvregs)))
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hx27_4 : s4.readReg64 .x27 = ctxPtr := hx27_cs4.trans hx27_3
  have htr3_s : s3.trace = s.trace := htr3_2.trans (htr2_1.trans htr1)
  have hst_to4 : Steps (tripleRatchetProgAtExt img.base ext) s s4 :=
    hst1.trans (hst2.trans (hst3.trans hst4))
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
      ((coroPtr + 0x2d0#64) ↦₆₄ (img.base + ikit.saveFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live saveIdFutPtr ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 1#8 ⊢
      A.live saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat (8#64).toNat ∗
      memRegion saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (ikit.saveBoxAt_memRegion _ _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  rcases ans with ⟨⟩ | c
  · -- Err () arm: +0x6c → saveFutDrop → +0x2ec → +0x544 → +0x550 → x30
    refine SepWPp.weaken_frame (savePollErr_unpack_repack img.base (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err => ?_
    refine SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    subst hw0_eq
    have h1c := p4_seg1c_gen_vregs_ext_wp img.base ext s4 coroPtr saveIdFutPtr
      (img.base + ikit.saveFutVtOff) (img.base + ikit.saveFutDropOff)
      0x800000000000001A#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s o1 o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero hb) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine SepWPp.bind_sepWP_frame_steps h1c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5, hx23_5,
        hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hF5 : img.FrozenLoaded s5 := hF4.of_keepsFrozen hst5.keepsFrozen
    have hsym5 : s5.symtab = img.symtab := hst5.symtab_eq.trans hsym4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine SepWPp.call_futDrop hF5 hsym5 hikit.saveFutDrop hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hF6 hsym6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h1d_err := p4_seg1d_err_vregs_ext_wp_p4 img.base ext hA s6 coroPtr saveIdFutPtr
      (img.base + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      0x800000000000001A#64 ikit.saveBoxSize_ne_zero (by decide) hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h1d_err
    refine SepWPp.bind_sepWP_frame_steps h1d_err (by sep_focus)
      fun s7 P7 hpc7 hrun7 hst7 ⟨hP7, hsp7_6, htr7_6, hx8_7, hx19_7, hx22_7,
        hx24_7, hx25_7, hx26_7, _, hx28_7, _, hvregs7_6⟩ => ?_
    refine SepWPp.weaken_frame hP7 (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp7 : s7.sp = s.sp := hsp7_6
    have hF7 : img.FrozenLoaded s7 := hF6.of_keepsFrozen hst7.keepsFrozen
    have hsym7 : s7.symtab = img.symtab := hst7.symtab_eq.trans hsym6
    have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
    have hx8_7' : s7.readReg64 .x8 = s.sp + 0x2b0#64 := hx8_7
    have hx22_7' : s7.readReg64 .x22 = o1.zeroExtend 64 :=
      hx22_7.trans (hx22_cs6.trans hx22_5)
    have hx24_7' : s7.readReg64 .x24 = s7.sp + 0x370#64 := by
      rw [hx24_7, hx24_cs6, hx24_5, hsp7]
    have hx25_7' : s7.readReg64 .x25 = s7.sp + 0x210#64 := by
      rw [hx25_7, hx25_cs6, hx25_5, hsp7]
    have hx26_7' : s7.readReg64 .x26 = outPtr :=
      hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4))
    have hunwind := stageP4_err_unwind_550_vregs_ok_p4 img ext hA hDropSS3 s0 s7 coroPtr
      (s.sp + 0x2b0#64) ptCap ptPtr outPtr 0x800000000000001A#64 prevStatesPtr
      o2 o3 o4 o5 o1 o6 b_2c0 pt G st (PanicOomProp s0)
      hpt_le herr_ub hF7 hsym7 hpc7 hrun7 hsp7_align hx8_7' hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4)))
    rw [hsp7] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hFf, hsymf⟩ => ?_
    have hst_all : Steps (tripleRatchetProgAtExt img.base ext) s sf :=
      hst_to4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw)))
    have htr_all : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    refine hErr sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hFf hsymf ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4SaveIdErrPost stageP4SaveIdShared saveIdVtablesAt
    rw [stack_saveId_to_errUnwind ikit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by ac_rfl)
  · -- Ok c arm: +0x6c → saveFutDrop → +0x2ec → kyberMarkUsedShimAddr
    refine SepWPp.weaken_frame
      (Entails.of_eq (savePollOk_eq_exists_pollCells img.base (s.sp + 0x3e0#64) c))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o2 => ?_
    have h1c := p4_seg1c_gen_vregs_ext_wp img.base ext s4 coroPtr saveIdFutPtr
      (img.base + ikit.saveFutVtOff) (img.base + ikit.saveFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s
      (if c == .replacedExisting then 1#32 else 0#32) o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero hb) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine SepWPp.bind_sepWP_frame_steps h1c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, _, hx23_5,
        hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hF5 : img.FrozenLoaded s5 := hF4.of_keepsFrozen hst5.keepsFrozen
    have hsym5 : s5.symtab = img.symtab := hst5.symtab_eq.trans hsym4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine SepWPp.call_futDrop hF5 hsym5 hikit.saveFutDrop hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hF6 hsym6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, hx27_cs6, hx28_cs6, _, hvregs_cs6⟩
    have h2ac_un :
        memRegion (coroPtr + 0x2ac#64) 20 =
        ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
          ((coroPtr + 0x2ac#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2b4#64) ↦₆₄ u1) ∗
          ((coroPtr + 0x2bc#64) ↦₃₂ u2) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_eq_cells (coroPtr + 0x2ac#64)
    refine SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq h2ac_un) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_2bc => SepWPp.exists_elim fun u_2b4 =>
      SepWPp.exists_elim fun u_2ac => ?_
    have h1d_ok := p4_seg1d_ok_vregs_ext_wp_p4 img.base ext hA s6 coroPtr msgPtr
      kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr saveIdFutPtr
      (img.base + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      u_2ac u_2b4 opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc
      ikit.saveBoxSize_ne_zero hopk_ne2 hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h1d_ok
    refine SepWPp.bind_sepWP_frame_steps h1d_ok (by sep_focus)
      fun s7 P7 hpc7 hrun7 hst7 ⟨hP7, hsp7_6, htr7_6, hx0_7, hx1_7, hx2_7, hx3_7,
        hx19_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, _, hlr7, hvregs7_6⟩ => ?_
    refine SepWPp.weaken_frame hP7 (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x2b0#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (tripleRatchetProgAtExt img.base ext) s s7 :=
      hst_to4.trans (hst5.trans (hst6.trans hst7))
    have htr_all : s7.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) := by
      rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    have hF7 : img.FrozenLoaded s7 := hF6.of_keepsFrozen hst7.keepsFrozen
    have hsym7 : s7.symtab = img.symtab := hst7.symtab_eq.trans hsym6
    refine hOk c s7 _ hst_all hrel hpc7 hrun7 hsp7_6 htr_all hx0_7 hx1_7 hx2_7 hx3_7
      hx19_7 (hx24_7.trans (hx24_cs6.trans hx24_5))
      (hx25_7.trans (hx25_cs6.trans hx25_5))
      (hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4)))
      (hx27_7.trans (hx27_cs6.trans (hx27_5.trans hx27_4)))
      hx28_7 hlr7 hF7 hsym7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4))) ?_
    unfold stageP4SaveIdOkPost stageP4SaveIdShared saveIdVtablesAt
    exact Entails.of_eq (by ac_rfl)

theorem stageP4_saveIdentity_dispatch_vregs_kits {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hiVt : IdentityVtablesOk img ikit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddrOk : ikit.addrOk peer.val)
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : saveIdCallStack ikit ≤ 2 ^ 64)
    (hkSlot : ∀ {s' : State} {P : SepProp}, img.FrozenLoaded s' → (s'.mem ⊨ P) →
      s'.mem ⊨ ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗ P)
    (hfs : FsAt ikit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (c : IdentityChange) (s1 : State) (P1 : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      ikit.saveRel ist0 peer.val remoteIk (.ok c) →
      s1.pc = kyberMarkUsedShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) →
      s1.readReg64 .x0 = kyberStorePtr →
      s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 →
      s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 →
      s1.readReg64 .x3 = msgPtr + 0xa8#64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 =
        (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x350#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ stageP4SaveIdOkPost img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 c G st ∗ F) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      ikit.saveRel ist0 peer.val remoteIk (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4SaveIdErrPost img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk ist0 ∗ F) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4SaveIdPre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
        kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G st ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_saveIdentity_dispatch_vregs_kits_p4 img ext ikit (.of_allocContracts hA) hDropSS3 hikit
    hiVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr
    kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
    kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G st F Q hb haddrOk hopk_ne2 hpt_le
    hsp_ub hkSlot hfs hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    hOk hErr

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
