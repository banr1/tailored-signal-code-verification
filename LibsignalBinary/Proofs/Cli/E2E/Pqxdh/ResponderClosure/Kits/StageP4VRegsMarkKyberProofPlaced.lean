/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyber

/-!
# Relocatable Stage P4.2 Dispatch Proof: `mark_kyber_pre_key_used`

Relocatable `[LibsignalPlacement]` counterpart of `StageP4VRegsMarkKyberProof` on Block `518`
(`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

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
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

/-- Resources shared unchanged across Placed Substage P4.2 (`mark_kyber_pre_key_used`). -/
def stageP4MarkKyberSharedPlaced {A : RustAlloc}
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr msgPtr prevStatesPtr : BitVec 64)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt s.sp (markKyberCallStack kpkKit)

/-- Spatial precondition of Placed Substage P4.2 at `0#64 + kpkKit.markShimOff`. -/
def stageP4MarkKyberPrePlaced {A : RustAlloc}
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MarkKyberSharedPlaced kpkKit s0 s coroPtr msgPtr prevStatesPtr baseKey ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
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
  kpkKit.storeAt kyberStorePtr kst0

/-- Spatial postcondition of Placed Substage P4.2 after `Ok(())` + deallocation. -/
def stageP4MarkKyberOkPostPlaced {A : RustAlloc}
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MarkKyberSharedPlaced kpkKit s0 s coroPtr msgPtr prevStatesPtr baseKey ∗
  markKyberVtablesAt kpkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
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
  kpkKit.storeAt kyberStorePtr (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))

/-- Spatial postcondition of Placed Substage P4.2 on `Err(e)` at `s0.readReg64 .x30`. -/
def stageP4MarkKyberErrPostPlaced {A : RustAlloc}
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState) (e : kpkKit.MarkErr) : SepProp :=
  stageP4MarkKyberSharedPlaced kpkKit s0 s coroPtr msgPtr prevStatesPtr baseKey ∗
  markKyberVtablesAt kpkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  speErrAt kpkKit.markErr outPtr e ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kpkKit.storeAt kyberStorePtr
    (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))

/-- Mark-only subset of `KyberPreKeyStoreKitPlacedOk` used by Stage P4.2. -/
structure KyberPreKeyMarkKitPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : KyberPreKeyStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  markShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markShimOff) (withLsRoCl lsmpl (kitKpkMarkShimSpec kit))
  markPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markPollOff) (withLsRoCl lsmpl (kitKpkMarkPollSpecE kit))
  markFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markFutDropOff) (withLsRoCl lsmpl futDropSpec)

theorem kyberPreKeyMarkKitPlacedOk_of_store [LibsignalPlacement] {A : RustAlloc}
    {kit : KyberPreKeyStoreSpec A 0#64} {H : LibsignalHooks}
    (h : KyberPreKeyStoreKitPlacedOk kit H) : KyberPreKeyMarkKitPlacedOk kit H :=
  ⟨h.markShim, h.markPoll, h.markFutDrop⟩

set_option maxHeartbeats 1200000 in
theorem stageP4_markKyber_to_38c_vregs_mark_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (_hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk38c : ∀ (boxPtr : BitVec 64) (s5 : State) (P5 : SepProp),
      Steps (lsProg_518 ext) s s5 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.pc = (blkPl_518).base + 0x38c#64 →
      s5.status = .Running →
      s5.sp = s.sp →
      s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.readReg64 .x19 = coroPtr →
      s5.readReg64 .x21 = boxPtr →
      s5.readReg64 .x23 = 0#64 + kpkKit.markFutVtOff →
      s5.readReg64 .x24 = s.sp + 0x370#64 →
      s5.readReg64 .x25 = s.sp + 0x210#64 →
      s5.readReg64 .x26 = outPtr →
      s5.readReg64 .x27 = ctxPtr →
      s5.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem →
      calleeSavedVRegs s5 = calleeSavedVRegs s0 →
      (P5 ⊢
        A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat ∗
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s5 P5 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kpkKit.markBoxSize = (BitVec.ofNat 64 kpkKit.markBoxSize).toNat :=
    (Nat.mod_eq_of_lt kpkKit.markBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  have hx1_w : s.readReg32 .x1 = kyberPreKeyId := by
    simp only [State.readReg32, hx1]; bv_omega
  have hx2_w : s.readReg32 .x2 = signedPreKeyId := by
    simp only [State.readReg32, hx2]; bv_omega
  refine SepWPp.intro_ro (R_ro := markKyberVtablesAt kpkKit)
    (fun hm => markKyberVtablesAt_placed_intro hkVt hcro.2 hm) ?_
  unfold stageP4MarkKyberPrePlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_shim kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  refine call_rocl_frame
    (spec := kitKpkMarkShimSpec kpkKit)
    (x := { self := kyberStorePtr, id := kyberPreKeyId,
            signedId := signedPreKeyId, baseKeyA := msgPtr + 0xa8#64 })
    (φ := (0#64 &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = kyberStorePtr ∧
          s.readReg32 .x1 = kyberPreKeyId ∧ s.readReg32 .x2 = signedPreKeyId ∧
          s.readReg64 .x3 = msgPtr + 0xa8#64)
    (T := A.pool ∗ stackAt s.sp kpkKit.markShimStack)
    hcro htr_pfx (hkpkKit.markShim (by decide)) hpc hrun hsp_al hlr
    (by dsimp only [kitKpkMarkShimSpec]; exact Entails.of_eq (by ac_rfl))
    ⟨rfl, hx0, hx1_w, hx2_w, hx3⟩ (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1 hsp1_al hcs1 hcro1 hst1 => ?_)
  dsimp only [kitKpkMarkShimSpec]
  simp only [sepConj_assoc]
  let boxPtr := s1.readReg64 .x0
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_shim kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, hx28_cs1, _, hvregs_cs1⟩
  have htr1_pfx : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  have hfs1 := hfs.of_steps_nil hst1 htr1
  have h2c8_un :
      memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h2a := p4_seg2a_vregs_placed_wp ext s1 coroPtr ctxPtr boxPtr
    (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markPollOff) u_2c8 u_2d0
    hpc1 hrun1 rfl hx1_1 (hx19_cs1.trans hx19) (hx27_cs1.trans hx27)
  refine SepWPp.bind_sepWP_frame_steps h2a (by sep_focus)
    fun s2 P2 hpc2 hrun2 hst2 ⟨hP2, hsp2_1, htr2_1, hx0_2, _, hx8_2,
      hx19_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hlr2, hvregs2_1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcro2 := lscro_of_steps hst2 hcro1
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2] using hsp_al
  have htr2_pfx : s0.trace <+: s2.trace := htr2_1 ▸ htr1_pfx
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rw [hsp1] at hx8_2
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_poll kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : KyberMarkPollCall :=
    { fut := boxPtr
      out := s.sp + 0x3e0#64
      self := kyberStorePtr
      baseKeyA := msgPtr + 0xa8#64
      id := kyberPreKeyId
      signedId := signedPreKeyId
      baseKey := baseKey }
  refine call_rocl_frame
    (spec := kitKpkMarkPollSpecE kpkKit)
    (x := (pollCall, kst0))
    (φ := kpkKit.envOk s2.fs.files ∧ (0#64 &&& 0xfff#64) = 0#64 ∧
          s2.readReg64 .x0 = boxPtr ∧ s2.readReg64 .x8 = s.sp + 0x3e0#64 ∧
          kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (T := kpkKit.markBoxAt boxPtr kyberStorePtr (msgPtr + 0xa8#64) kyberPreKeyId signedPreKeyId 0#8 ∗
          kpkKit.storeAt kyberStorePtr kst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          A.pool ∗ stackAt s.sp kpkKit.markPollStack)
    hcro2 htr2_pfx (hkpkKit.markPoll (by decide)) hpc2 hrun2 hsp2_al hlr2
    (by
      dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, pollCall]
      rw [hsp2]
      refine Entails.pure_left fun ⟨henv, hb', hx0', hx8', hmok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hb', hx0', hx8', hmok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨hfs2.envOk_here, rfl, hx0_2, hx8_2, hmarkOk⟩ (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 hsp3_al hcs3 hcro3 hst3 => ?_)
  dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, pollCall]
  rw [hsp2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr3_2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_poll kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x2e0#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_300s => SepWPp.exists_elim fun u_2f8s =>
    SepWPp.exists_elim fun u_2f0s => SepWPp.exists_elim fun u_2e8s =>
    SepWPp.exists_elim fun u_2e0s => ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _, _, hvregs_cs3⟩
  have hvregs_3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 :=
    hvregs_cs3.trans (hvregs2_1.trans (hvregs_cs1.trans hvregs))
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by
    rw [hx24_cs3, hx24_2, hx24_cs1, hx24, hsp3]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by
    rw [hx25_cs3, hx25_2, hx25_cs1, hx25, hsp3]
  have hx26_3 : s3.readReg64 .x26 = outPtr :=
    hx26_cs3.trans (hx26_2.trans (hx26_cs1.trans hx26))
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2
  have htr2_s : s2.trace = s.trace := htr2_1.trans htr1
  have hst_to3 : Steps (lsProg_518 ext) s s3 :=
    hst1.trans (hst2.trans hst3)
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ boxPtr) ∗
      ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + kpkKit.markFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live boxPtr kpkKit.markBoxSize 8 ∗
      kpkKit.markBoxAt boxPtr kyberStorePtr (msgPtr + 0xa8#64) kyberPreKeyId signedPreKeyId 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (kpkKit.markBoxAt_memRegion _ _ _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  rcases ans with e | ⟨⟩
  · -- Err(e): +0x180 → markFutDrop → +0x38c → +0x550 → x30
    dsimp only [kpkMarkPollOutAt, unitSpePollOutAt, speErrAt]
    simp only [sepConj_assoc]
    let S := kpkKit.markErr
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (speWordsAt_eq_pollCellsAt (s.sp + 0x3e0#64)
        (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)))
      (by sep_focus) ?_
    have h2b := p4_seg2b_gen_vregs_placed_wp ext s3 coroPtr boxPtr
      (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markFutDropOff)
      (S.w0 e)
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      u_2e0s u_2e8s u_2f0s u_2f8s
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32) u_300s
      (speErrSpec_w0_ne_pend S e) (kpkKit.markFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h2b
    refine SepWPp.bind_sepWP_frame_steps h2b (by sep_focus)
      fun s4 P4 hpc4 hrun4 hst4 ⟨hP4, hsp4_3, htr4_3, _, hx19_4, hx21_4, hx22_4, hx23_4,
        hx24_4, hx25_4, hx26_4, _, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP4 (by sep_focus) ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hcro4 := lscro_of_steps hst4 hcro3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_futDrop_lscro hcro4 (hkpkKit.markFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      fun s5 hpc5 hrun5 hsp5_4 hsp5_al hcs5 htr5_4 hcro5 hst5 => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, _, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h2c_err := p4_seg2c_err_vregs_placed_wp ext hdealloc s5 coroPtr boxPtr
      (0#64 + kpkKit.markFutVtOff) (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64
      (S.w0 e) kpkKit.markBoxSize_ne_zero (speErrSpec_w0_ne_ok S e) hpc5 hrun5 hsp5_al
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4)
      (hx28_cs5.trans hx28_4)
    rw [hsp5] at h2c_err
    refine SepWPp.bind_sepWP_frame_steps h2c_err (by sep_focus)
      fun s6 P6 hpc6 hrun6 hst6 ⟨hP6, hsp6_5, htr6_5, hx8_6, hx19_6, hx22_6,
        hx24_6, hx25_6, hx26_6, _, hx28_6, _, hvregs6_5⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp6 : s6.sp = s.sp := hsp6_5
    have hcro6 := lscro_of_steps hst6 hcro5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    have hx22_6' : s6.readReg64 .x22 = ((S.w1 e).extractLsb' 0 32).zeroExtend 64 :=
      hx22_6.trans (hx22_cs5.trans hx22_4)
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by
      rw [hx24_6, hx24_cs5, hx24_4, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by
      rw [hx25_6, hx25_cs5, hx25_4, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr :=
      hx26_6.trans (hx26_cs5.trans (hx26_4.trans hx26_3))
    have hunwind := stageP4_err_unwind_550_vregs_placed_ok ext hdealloc hDropSS3 s0 s6 coroPtr
      (s.sp + 0x2e0#64) ptCap ptPtr outPtr (S.w0 e) prevStatesPtr
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32)
      b_2c0 pt G st (PanicOomProp s0)
      hpt_le herr_ub hcro6 hpc6 hrun6 hsp6_align hx8_6 hx19_6 hx22_6'
      hx24_6' hx25_6' hx26_6' hx28_6
      (hvregs6_5.trans (hvregs_cs5.trans (hvregs4_3.trans hvregs_3)))
    rw [hsp6] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    have hst_all : Steps (lsProg_518 ext) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_unw)))
    have htr_all :
        sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr3_2, htr2_s]
    refine hErr e sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hcrof ?_
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4MarkKyberErrPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt speErrAt
    rw [stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub,
        speWordsAt_eq_pollCellsAt outPtr (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)]
    exact Entails.of_eq (by ac_rfl)
  · -- Ok(()) arm: +0x180 → markFutDrop → +0x38c
    dsimp only [kpkMarkPollOutAt]
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (unitSpePollOk_eq_exists_pollCells kpkKit.markErr (s.sp + 0x3e0#64)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h2b := p4_seg2b_gen_vregs_placed_wp ext s3 coroPtr boxPtr
      (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_2e0s u_2e8s u_2f0s u_2f8s o1 o6 u_300s
      (by decide) (kpkKit.markFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h2b
    refine SepWPp.bind_sepWP_frame_steps h2b (by sep_focus)
      fun s4 P4 hpc4 hrun4 hst4 ⟨hP4, hsp4_3, htr4_3, _, hx19_4, hx21_4, _, hx23_4,
        hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP4 (by sep_focus) ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hcro4 := lscro_of_steps hst4 hcro3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_futDrop_lscro hcro4 (hkpkKit.markFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      fun s5 hpc5 hrun5 hsp5_4 _ hcs5 htr5_4 hcro5 hst5 => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, hx27_cs5, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x2e0#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (lsProg_518 ext) s s5 :=
      hst_to3.trans (hst4.trans hst5)
    have htr_all :
        s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) := by
      rw [htr5_4, htr4_3, htr3_2, htr2_s]
    refine hOk38c boxPtr s5 _ hst_all hrel hpc5 hrun5 hsp5 htr_all
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4)
      (hx24_cs5.trans hx24_4) (hx25_cs5.trans hx25_4)
      (hx26_cs5.trans (hx26_4.trans hx26_3))
      (hx27_cs5.trans (hx27_4.trans hx27_3))
      (hx28_cs5.trans hx28_4) hcro5
      (hvregs_cs5.trans (hvregs4_3.trans hvregs_3)) ?_
    unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
    exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` Substage P4.2 (`None` OPK ID, `markShim → +0x3cc` / `x30`)
preserving `calleeSavedVRegs`. -/
theorem stageP4_markKyber_none_dispatch_vregs_mark_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
          prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  refine stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit hdealloc hDropSS3 hkpkKit hkVt
    s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
    kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st
    (((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) Q
    hmarkOk hpt_le hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
    hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs
    (fun boxPtr s5 P5 hst5 hrel hpc5 hrun5 hsp5 htr5 hx19_5 hx21_5 hx23_5
      hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hcro5 hvregs5 hP5 => ?_)
    (fun e sf Pf hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof hPf =>
      hErr e sf Pf hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof
        (Entails.trans hPf (Entails.of_eq (by ac_rfl))))
  refine SepWPp.weaken_pre hP5 ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
    (by sep_focus) ?_
  have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_align
  have h2c := p4_seg2c_none_vregs_placed_wp ext hdealloc s5 coroPtr boxPtr
    (0#64 + kpkKit.markFutVtOff) (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64
    kpkKit.markBoxSize_ne_zero hpc5 hrun5 hsp5_al hx19_5 hx21_5 hx23_5 hx28_5
  rw [hsp5] at h2c
  refine SepWPp.bind_sepWP_frame_steps h2c (by sep_focus)
    fun s6 P6 hpc6 hrun6 hst6 ⟨hP6, hsp6_5, htr6_5, hx19_6, hx24_6, hx25_6,
      hx26_6, hx27_6, hx28_6, _, hvregs6_5⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine hOk s6 _ (hst5.trans hst6) hrel hpc6 hrun6 hsp6_5 (htr6_5.trans htr5)
    hx19_6 (hx24_6.trans hx24_5) (hx25_6.trans hx25_5)
    (hx26_6.trans hx26_5) (hx27_6.trans hx27_5) hx28_6
    (lscro_of_steps hst6 hcro5)
    (hvregs6_5.trans hvregs5) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` Substage P4.2 (`Some` OPK ID,
`markShim → removePreKeyShimAddr` / `x30`) preserving `calleeSavedVRegs`. -/
theorem stageP4_markKyber_some_dispatch_vregs_mark_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr preKeyStoreVt
     removePreKeyShimAddr prevStatesPtr ptCap ptPtr : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hpSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      m ⊨ ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗ P)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = removePreKeyShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x0 = preKeyStorePtr →
      s1.readReg64 .x1 = opkId.zeroExtend 64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 = (blkPl_518).base + 0x3c0#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗
        ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
          prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗
       ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
       ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  refine stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit hdealloc hDropSS3 hkpkKit hkVt
    s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
    kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st
    (((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
     ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
     ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
     ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) Q
    hmarkOk hpt_le hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
    hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs
    (fun boxPtr s5 P5 hst5 hrel hpc5 hrun5 hsp5 htr5 hx19_5 hx21_5 hx23_5
      hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hcro5 hvregs5 hP5 => ?_)
    (fun e sf Pf hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof hPf =>
      hErr e sf Pf hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof
        (Entails.trans hPf (Entails.of_eq (by ac_rfl))))
  refine SepWPp.weaken_pre hP5 ?_
  refine SepWPp.intro_ro (R_ro := ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr))
    (fun hm => hpSlot hcro5.2 hm) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
    (by sep_focus) ?_
  have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_align
  have h2c := p4_seg2c_some_vregs_placed_wp ext hdealloc s5 coroPtr preKeyStorePtr preKeyStoreVt
    removePreKeyShimAddr boxPtr (0#64 + kpkKit.markFutVtOff)
    (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64 opkId
    kpkKit.markBoxSize_ne_zero hpc5 hrun5 hsp5_al hx19_5 hx21_5 hx23_5 hx28_5
  rw [hsp5] at h2c
  refine SepWPp.bind_sepWP_frame_steps h2c (by sep_focus)
    fun s6 P6 hpc6 hrun6 hst6 ⟨hP6, hsp6_5, htr6_5, hx0_6, hx1_6, hx19_6,
      hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, _, hlr6, hvregs6_5⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine hOk s6 _ (hst5.trans hst6) hrel hpc6 hrun6 hsp6_5 (htr6_5.trans htr5)
    hx0_6 hx1_6 hx19_6 (hx24_6.trans hx24_5) (hx25_6.trans hx25_5)
    (hx26_6.trans hx26_5) (hx27_6.trans hx27_5) hx28_6 hlr6
    (lscro_of_steps hst6 hcro5)
    (hvregs6_5.trans hvregs5) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  exact Entails.of_eq (by ac_rfl)

theorem stageP4_markKyber_to_38c_vregs_kits_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk38c : ∀ (boxPtr : BitVec 64) (s5 : State) (P5 : SepProp),
      Steps (lsProg_518 ext) s s5 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.pc = (blkPl_518).base + 0x38c#64 →
      s5.status = .Running →
      s5.sp = s.sp →
      s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.readReg64 .x19 = coroPtr →
      s5.readReg64 .x21 = boxPtr →
      s5.readReg64 .x23 = 0#64 + kpkKit.markFutVtOff →
      s5.readReg64 .x24 = s.sp + 0x370#64 →
      s5.readReg64 .x25 = s.sp + 0x210#64 →
      s5.readReg64 .x26 = outPtr →
      s5.readReg64 .x27 = ctxPtr →
      s5.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem →
      calleeSavedVRegs s5 = calleeSavedVRegs s0 →
      (P5 ⊢
        A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat ∗
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s5 P5 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit hdealloc hDropSS3 (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt
    s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId
    signedPreKeyId b_2c0 pt baseKey kst0 G st F Q hmarkOk hpt_le hsp_ub hfs hcro hpc hrun
    hsp_align htr_pfx hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs hOk38c hErr

theorem stageP4_markKyber_none_dispatch_vregs_kits_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
          prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_markKyber_none_dispatch_vregs_mark_placed ext kpkKit hdealloc hDropSS3 (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit)
    hkVt s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId
    signedPreKeyId b_2c0 pt baseKey kst0 G st F Q hmarkOk hpt_le hsp_ub hfs hcro hpc hrun
    hsp_align htr_pfx hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs hOk hErr

theorem stageP4_markKyber_some_dispatch_vregs_kits_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr preKeyStoreVt
     removePreKeyShimAddr prevStatesPtr ptCap ptPtr : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hpSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      m ⊨ ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗ P)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = removePreKeyShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x0 = preKeyStorePtr →
      s1.readReg64 .x1 = opkId.zeroExtend 64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 = (blkPl_518).base + 0x3c0#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st ∗
        ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (e : kpkKit.MarkErr) (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
          prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
        ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗
       ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
       ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_markKyber_some_dispatch_vregs_mark_placed ext kpkKit hdealloc hDropSS3 (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit)
    hkVt s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr preKeyStoreVt
    removePreKeyShimAddr prevStatesPtr ptCap ptPtr opkId kyberPreKeyId signedPreKeyId b_2c0 pt
    baseKey kst0 G st F Q hmarkOk hpt_le hsp_ub hpSlot hfs hcro hpc hrun hsp_align htr_pfx
    hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs hOk hErr

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
