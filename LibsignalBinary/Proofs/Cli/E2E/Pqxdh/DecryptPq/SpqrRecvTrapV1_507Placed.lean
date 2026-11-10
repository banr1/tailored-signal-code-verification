/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvErr507Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1Placed
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Segments S5 & S6 (`PqRecv` + `DeriveKeys`, `blkPl_508`)

Proves `deriveKeys_507_placed_ok : S6SeamPlaced` and `pqRecv_507_placed_ok_WT : S5WTSeamPlaced`
for `try_decrypt_with_state::<signal_session_handshake::Coins>` (`blkPC_508` / `blkPl_508`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.CliHandshake.TryDecPlaced

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding memRegion_eight
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.Cli.SpqrV1.M4

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem deriveKeys_507_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (H : String → Option (State → State))
    (hgen : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A))) :
    S6SeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base C A ctl := by
  intro x trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segDeriveKeysPC_at at hpc
  unfold VerifyMacStatePlaced
  refine reaches_pc_midMeta_placed hcl ?_
  unfold segVerifyMacPC_at tryDecryptMidMetaCore
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29 ⊢
  clear hsp29_eq
  unfold cliTryDecryptCommonHeapPlaced at hmem ⊢
  rw [lsLogOff_eq_logOff_placed] at hmem ⊢
  generalize s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hmem ⊢
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  refine reaches_pc_of_sepWP_placed hmem hcl
    (mid := lsmpl.base 69)
    (RegMid := fun sm =>
      newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
      sm.readReg64 .x0 = sp + 400#64 ∧
      sm.readReg64 .x1 = sp + 864#64 ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_508).base + 1596#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 976#64 ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      mkgAt A (sp + 400#64) mkg ∗
      spqrRecvKeyAt A (sp + 864#64) pqrKey ∗
      memRegion (sp + 1280#64) 84 ∗
      A.pool ∗ stackAt sp tryDecryptSubStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 16#64) 12 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 440#64) 424 ∗
      memRegion (sp + 888#64) 216 ∗
      memRegion (sp + 1104#64) 176 ∗
      memRegion (sp + 1364#64) 44 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      tryDecryptSavedRegs s0.sp s0)
    ?_ ?_
  · wp_conv_pre =>
      simp only [sepConj_assoc]
      unfold vecU8At vecHeader
      rw [memRegion_split sp 8 8 (by decide),
        mr_cut_add sp 320 80 704 (by decide),
        mr_cut_add sp 400 8 696 (by decide),
        mr_cut_add sp 408 8 688 (by decide),
        mr_cut_add sp 416 8 680 (by decide),
        mr_cut_add sp 424 8 672 (by decide),
        mr_cut_add sp 432 8 664 (by decide),
        mr_cut_add sp 440 8 656 (by decide),
        mr_cut_add sp 448 8 648 (by decide),
        mr_cut_add sp 456 8 640 (by decide),
        mr_cut_add sp 464 8 632 (by decide),
        mr_cut_add sp 472 8 624 (by decide),
        mr_cut_add sp 480 8 616 (by decide),
        mr_cut_add sp 488 376 240 (by decide),
        mr_cut_add sp 864 8 232 (by decide),
        mr_cut_add sp 872 8 224 (by decide),
        mr_cut_add sp 880 8 216 (by decide),
        mr_cut_add sp 1116 4 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
      simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        memRegion_eight (sp + 8#64),
        memRegion_eight (sp + 400#64),
        memRegion_eight (sp + 408#64),
        memRegion_eight (sp + 416#64),
        memRegion_eight (sp + 424#64),
        memRegion_eight (sp + 432#64),
        memRegion_eight (sp + 440#64),
        memRegion_eight (sp + 448#64),
        memRegion_eight (sp + 456#64),
        memRegion_eight (sp + 464#64),
        memRegion_eight (sp + 472#64),
        memRegion_eight (sp + 480#64),
        memRegion_eight (sp + 864#64),
        memRegion_eight (sp + 872#64),
        memRegion_eight (sp + 880#64),
        memRegion_four (sp + 1116#64),
        memRegion_eight (sp + 1120#64),
        memRegion_eight (sp + 1128#64),
        memRegion_eight (sp + 1136#64),
        memRegion_eight (sp + 1144#64),
        memRegion_eight (sp + 1152#64),
        memRegion_eight (sp + 1160#64),
        KeyDerive.pointsTo64_split32 (sp + 400#64)]
    refine SepWP.focus_weaken (optKeyAt_split A (sp + 1304#64) pqrKey) (by sep_focus) ?_
    wp_pull_exists
    wp_focus_pure
    rintro ⟨hnp1, hnp2, hnp3⟩
    refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
    wp_steps
    rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
      rw [hseed_len]]
    refine SepWP.focus_weaken (optKeyAt_fold A (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
    refine SepWP.focus_weaken (mkgAt_fold A (sp + 400#64) seedCap seedPtr _ _ mkg hseed) (by sep_focus) ?_
    have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
      simpa using mr_cut_add sp 16 8 4 (by decide)
    have hm440 : memRegion (sp + 440#64) 424 =
        memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
        (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
        memRegion (sp + 488#64) 376))))) := by
      rw [mr_cut_add sp 440 8 416 (by decide),
        mr_cut_add sp 448 8 408 (by decide),
        mr_cut_add sp 456 8 400 (by decide),
        mr_cut_add sp 464 8 392 (by decide),
        mr_cut_add sp 472 8 384 (by decide),
        mr_cut_add sp 480 8 376 (by decide)]
    have hm1104 : memRegion (sp + 1104#64) 176 =
        memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
        (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
        (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
      rw [mr_cut_add sp 1104 8 168 (by decide),
        mr_cut_add sp 1112 8 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
    have hm1280 : memRegion (sp + 1280#64) 84 =
        memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 1328#64) 36))))) := by
      rw [mr_cut_add sp 1280 8 76 (by decide),
        mr_cut_add sp 1288 8 68 (by decide),
        mr_cut_add sp 1296 8 60 (by decide),
        mr_cut_add sp 1304 8 52 (by decide),
        mr_cut_add sp 1312 8 44 (by decide),
        mr_cut_add sp 1320 8 36 (by decide)]
    have hm1328 : memRegion (sp + 1328#64) 80 =
        memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
      simpa using mr_cut_add sp 1328 36 44 (by decide)
    rw [hm16, hm440, hm1104, hm1280, hm1328]
    wp_done
  · intro sm hpcm hrunm ⟨hcl_code, hcl_ro⟩ hReg
    rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
      hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    rw [stackAt_sub sp tryDecryptSubStack generateKeysStack]
    wp_call hgen { genA := sp + 400#64, g := mkg, pqrKeyA := sp + 864#64, pqrKey := pqrKey, ret := sp + 1280#64 }
    have hm320 : memRegion (sp + 320#64) 960 =
        memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
        (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
        (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
      rw [mr_cut_add sp 320 80 880 (by decide),
        mr_cut_add sp 400 40 840 (by decide),
        mr_cut_add sp 440 424 416 (by decide),
        mr_cut_add sp 864 24 392 (by decide),
        mr_cut_add sp 888 216 176 (by decide)]
    rw [hm320]
    wp_done

private theorem pqr_len_lt_placed {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {m : SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem pqr_len_lt_of_pre_placed {P F R : SepProp} {A : RustAlloc}
    {g : SignalMessageGhost} {a : BitVec 64} {m : SignalMessage} {mem : Memory}
    (h : mem ⊨ P ∗ ((signalMessageRestAt A g a m ∗ F) ∗ R)) :
    m.pqRatchet.length < 2 ^ 40 := by
  have h' : mem ⊨ signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by
    have heq : P ∗ ((signalMessageRestAt A g a m ∗ F) ∗ R) =
        signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by ac_rfl
    exact heq ▸ h
  exact pqr_len_lt_placed h'

private theorem spqrRecvStack_le_placed {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    omega

private theorem pre_spqrRecvRawSpecT [LibsignalPlacement] {A : RustAlloc} {S : SpqrModel}
    {stArg msgArg : VecArg} {ret : BitVec 64} {sm : State} {F R : SepProp}
    (h1 : stArg.bytes.length < 2 ^ 32)
    (h2 : msgArg.bytes.length < 2 ^ 40)
    (h3 : spqrRecvStack ≤ sm.sp.toNat)
    (h : sm.mem ⊨ (spqrRecvRawSpec A S).pre (stArg, msgArg, ret) sm ∗
      (F ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R))) :
    sm.mem ⊨ (spqrRecvRawSpecT A S).pre (stArg, msgArg, ret) sm ∗ (F ∗ R) := by
  dsimp only [spqrRecvRawSpecT]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  have heq :
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvRawSpec A S).pre (stArg, msgArg, ret) sm) ∗ F ∗ R =
      (spqrRecvRawSpec A S).pre (stArg, msgArg, ret) sm ∗ (F ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R)) := by
    ac_rfl
  exact heq ▸ h

private theorem post_spqrRecvRawSpecT [LibsignalPlacement] {A : RustAlloc} {S : SpqrModel}
    {x : VecArg × VecArg × BitVec 64} {sm sf1 : State} {F R : SepProp}
    (h : sf1.mem ⊨ ((spqrRecvRawSpecT A S).post x sm sf1 ∗ F) ∗ R) :
    sf1.mem ⊨ ((spqrRecvRawSpec A S).post x sm sf1 ∗ F) ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
  dsimp only [spqrRecvRawSpecT] at h
  have heq :
      ((SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvRawSpec A S).post x sm sf1) ∗ F) ∗ R =
      ((spqrRecvRawSpec A S).post x sm sf1 ∗ F) ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
    ac_rfl
  exact heq ▸ h

private theorem onPanic_absorb_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 sf ∗ R := by
  rw [cliTryDecryptSpecPlaced_onPanic_eq] at h ⊢
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced,
    tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hp, hmem⟩
  refine ⟨hp, ?_⟩
  rw [← sepConj_assoc] at hmem
  exact Satisfies.mono (sepConj_mono_left (Entails.top_right (fun _ => True.intro))) hmem

private theorem err_out_add_np_absorb [LibsignalPlacement] {prog : Program} {s0 s : State}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {F R : SepProp} {AState : State → Prop} {c : Prop}
    (hc : c)
    (h : ∃ s', Steps prog s s' ∧
      (AState s' ∨ (s'.status = .Panicked ∧
        s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ (F ∗ R)))) :
    ∃ s', Steps prog s s' ∧
      ((AState s' ∧ c) ∨ (s'.status = .Panicked ∧
        s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)) := by
  obtain ⟨s', hs, hA | ⟨hpan, hm⟩⟩ := h
  · exact ⟨s', hs, Or.inl ⟨hA, hc⟩⟩
  · exact ⟨s', hs, Or.inr ⟨hpan, onPanic_absorb_placed hm⟩⟩

theorem pqRecv_507_placed_ok_WT [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpecT A S)))
    (hfmt_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5WTSeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl uuidTryParse S := by
  intro x trG tr st1 mkg draws R s0 s hQ hstack hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  generalize hR'_def : (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) = R' at hmem
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStatePlaced (blkPl_508).base A ctl x trG tr st1 mkg newPqrState pqrKey draws
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailStatePlaced (blkPl_508).base A ctl x trG tr st1 e draws
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) by
    subst hR'_def
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_508).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    subst hR'_def
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call0 : sm.mem ⊨ (spqrRecvRawSpec A S).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((signalMessageRestAt A x.msgG x.msgA x.msg ∗
          trRestAt A sp trG tr ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
            (seedPtr ↦ₛ mkg.seed) ∗
            memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 16 ∗
          ((sp + 16#64) ↦₆₄ seedPtr) ∗
          memRegion (sp + 24#64) 4 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₆₄ seedCap) ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 784 ∗
          ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
          memRegion (sp + 1116#64) 164 ∗
          memRegion (sp + 1328#64) 80 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R)) := by
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    have hpq_lt : msgArg.bytes.length < 2 ^ 40 := pqr_len_lt_of_pre_placed hpre_call0
    have hst_lt : stArg.bytes.length < 2 ^ 32 := by
      show tr.pqrState.length < 2 ^ 32
      rw [hpqr_eq]
      exact hQ
    have hsp_lt : spqrRecvStack ≤ sm.sp.toNat := by
      rw [hspm]
      exact spqrRecvStack_le_placed hstack hsp_def
    have hpre_call := pre_spqrRecvRawSpecT hst_lt hpq_lt hsp_lt hpre_call0
    clear hpre_call0
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (ctl := ctl) (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1_raw
      have hpost1 := post_spqrRecvRawSpecT hpost1_raw
      clear hpost1_raw
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗
           trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      refine s5_out_add_np hnpF ?_
      generalize hR'_def : (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) = R' at hpost1' ⊢
      simp only [← sepConj_assoc] at hpost1'
      unfold DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R'))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore cliTryDecryptCommonHeapPlaced
      rw [lsLogOff_eq_logOff_placed]
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (ctl := ctl) (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1_raw
      have hpost1 := post_spqrRecvRawSpecT hpost1_raw
      clear hpost1_raw
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
           memRegion (sp + 1296#64) 32 ∗
           trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           FromRecordCallees.lsLogOff ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
        rw [lsLogOff_eq_logOff_placed]
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact err_out_add_np_absorb hnpF
          (pqRecv_recv_err_true_507_placed C A ctl S H x trG tr st1 mkg draws
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0
            hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact err_out_add_np_absorb hnpF
          (pqRecv_recv_err_false_507_placed C A ctl S H x trG tr st1 mkg draws
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0
            hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1')

theorem pqRecv_507_placed_ok_WT_of_seams [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : RunGlue.CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) (ctl : BitVec 64)
    (hfmt_call : subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base
        (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec E2E.HooksE.A0))
    (hdealloc_call : subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base
        (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ lsRustDeallocSym) (rustDeallocSpec E2E.HooksE.A0)) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base
        (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (blkPl_508).base SpqrV1.GF.Mul2U16.tokenInitPlacedAt W.C E2E.HooksE.A0 ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) := by
  have _ := CryptoVerification.CliHandshake.TryDecPlaced.instIsLsBlockProg_508
    (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
  exact pqRecv_507_placed_ok_WT W.C E2E.HooksE.A0 ctl (spqrV1 W.C.F W.Q.K)
    (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecT _ _ _ W.C.F W.Q.K
      (hS.spqrRecv_trTrap_at_block (i := 508)))
    hfmt_call hdealloc_call

end CryptoVerification.CliHandshake.TryDecPlaced
