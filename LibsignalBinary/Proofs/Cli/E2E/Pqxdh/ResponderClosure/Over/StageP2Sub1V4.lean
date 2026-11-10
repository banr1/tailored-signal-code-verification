/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Stage P2 Over-Path Substage P2.1 Outer `v4`

Proves `stageP2_over_sub1_v4_kits` and `stageP2_over_sub1_v4_kits_ext` (`+0x0868 → +0x0f14`, outer
`v4`) when `load_session` returned a populated 1-session record whose current session misses
(`PromoteMatchingMissAtProp`).
-/

@[expose] public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

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

/-! ## Stack and Buffer Helpers -/

theorem p2_boxU8Buf_pk_serialize_entails (A : RustAlloc) (ptr : BitVec 64)
    (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  unfold boxU8Buf
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => Entails.refl _

theorem p2_serBytes_entails_memRegion33 (ptr : BitVec 64) (pk : PublicKey) :
    (ptr ↦ₛ pk.serialize) ⊢ memRegion ptr 33 := by
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  simpa only [hlen] using ProofLib.pointsToBytes_entails_memRegion ptr pk.serialize

theorem p2_sp3e0_16_rejoin (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
      memRegion (sp + 0x3e9#64) 7 ⊢
    memRegion (sp + 0x3e0#64) 16 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 8 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

theorem p2_sp3e0_24_split_16_8 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 24 =
      memRegion (sp + 0x3e0#64) 16 ∗ memRegion (sp + 0x3f0#64) 8 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 16 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem p2_sp3e0_24_rejoin (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
      memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 8 ⊢
    memRegion (sp + 0x3e0#64) 24 := by
  rw [p2_sp3e0_24_split_16_8]
  refine Entails.trans (Q :=
    (((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗ memRegion (sp + 0x3e9#64) 7) ∗
      memRegion (sp + 0x3f0#64) 8) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left (p2_sp3e0_16_rejoin sp w0 b8)

/-! ## Substage P2.1 Outer `v4` (`+0x0868 → +0x0f14`) -/

set_option maxHeartbeats 1200000 in
/-- Over-path Substage P2.1 (`+0x0868 → +0x0f14`, outer `v4`): serializes `baseKey`, runs
`PromoteMatchingMissAtProp` at `msgVer = 4#8` returning `Ok(false)` with the populated 1-session
record intact, frees the 33-byte buffer, and invokes `spkKit.getShim`. -/
theorem stageP2_over_sub1_v4_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hPure : StageP2PureCallees P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtProp A img ext coroPtr g recG sess 4#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 16 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
       A.pool ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = img.base + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            prevSessionsEmptyAt A coroPtr g ∗
            sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 16 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hstk_base : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_pure
  have hstep1 := p2_seg1a_ext_wp img.base ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  rw [p2_fnAddr_pkSerialize_eq] at hpc1
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_frame_frozen_oom_prefix hF1 hsym1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp publicKeySerializeStack)
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (by intro _; rfl) (by intro _ _; rfl)
    fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 _ => ?_
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_wp img.base ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, hx22_3,
    _, hx24_3, _, hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  rw [p2_fnAddr_promoteMatching_eq] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le s.sp stk p2PromoteMissStack
    (Nat.le_trans p2_over_promoteMiss_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF3 hsym3 hPromMiss
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, s.sp + 0x3e0#64⟩)
    (φ := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (4#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (s.sp + 0x3e0#64) 16 ∗
      stackAt s.sp p2PromoteMissStack)
    (by dsimp only [p2PromoteMatchingMissAtSpec]; rw [hsp3])
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [p2PromoteMatchingMissAtSpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3,
      show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
      show (s.sp + 0x3e0#64) + 9#64 = s.sp + 0x3e9#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_ext_wp img.base ext hA s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (img.base + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_steps_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp3e0_16_rejoin s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_oom_steps_frame
    (x := ({ self := spkStorePtr, id := spkId } : PreKeyShimCall))
    hF5 hsym5 (htr5_eq ▸ htr) hspkOk.getShim hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro hF5 hsym5 hb hx0_5 hx1_5_32)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hFf hsymf => ?_)
  dsimp only [Spec.inImage, kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Contract-backed (`StageP2ClosureHooks` / `StageP2PureCallees4K`) Over-path Substage P2.1
(`+0x0868 → +0x0f14`, outer `v4`). -/
theorem stageP2_over_sub1_v4_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A img.base ext)
    (hPure : StageP2PureCallees4K P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtPropExt A img ext coroPtr g recG sess 4#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 16 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
       A.pool ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = img.base + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            prevSessionsEmptyAt A coroPtr g ∗
            sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 16 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hstk_base : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_pure
  have hstep1 := p2_seg1a_ext_wp img.base ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  rw [p2_fnAddr_pkSerialize_eq] at hpc1
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_frame_frozen_oom_prefix hF1 hsym1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp publicKeySerializeStack)
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (by intro _; rfl) (by intro _ _; rfl)
    fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 _ => ?_
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_wp img.base ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, hx22_3,
    _, hx24_3, _, hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  rw [p2_fnAddr_promoteMatching_eq] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le s.sp stk p2OverPromoteMissStackExt
    (Nat.le_trans p2_over_promoteMissExt_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF3 hsym3 hPromMiss
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, s.sp + 0x3e0#64⟩)
    (φ := (img.FrozenLoaded s3 ∧ s3.symtab = img.symtab) ∧
      (s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (4#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = s.sp + 0x3e0#64))
    (T := prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (s.sp + 0x3e0#64) 16 ∗
      stackAt s.sp p2OverPromoteMissStackExt)
    (by dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt]; rw [hsp3, pure_sepConj_pure_assoc])
    ⟨⟨hF3, hsym3⟩, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3,
      show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
      show (s.sp + 0x3e0#64) + 9#64 = s.sp + 0x3e9#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_hooks_wp img.base ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (img.base + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_steps_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp3e0_16_rejoin s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_oom_steps_frame
    (x := ({ self := spkStorePtr, id := spkId } : PreKeyShimCall))
    hF5 hsym5 (htr5_eq ▸ htr) hspkOk.getShim hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro hF5 hsym5 hb hx0_5 hx1_5_32)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hFf hsymf => ?_)
  dsimp only [Spec.inImage, kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
