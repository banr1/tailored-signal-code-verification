/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Relocatable Segment 7 (`VerifyMac`) on CLI Block `433`

Proves `S7SeamPlaced` (`VerifyMacStatePlaced` to `AesDecryptStatePlaced` / `ErrTailStatePlaced`) on
CLI Block `433` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.SpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt

theorem lsLogOff_eq_logOff_placed [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = logOff tryDecryptPlacedImg := by
  rw [show FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      logOff_eq_placed]

theorem cliTryDecryptSpecPlaced_onPanic_eq [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) :
    (cliTryDecryptSpecPlaced C A ctl parse S).onPanic =
      (tryDecryptSpecPlaced C A ctl parse S).onPanic := rfl

theorem lsLogOff_eq_macLsLogOff [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = macLsLogOff := rfl

theorem verifyMac_true_433_placed_ok' [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_macLsLogOff,
      trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  rw [cliTryDecryptSpecPlaced_onPanic_eq]
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesPlacedSpec C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [writeReg64_trace, setPC_trace, htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨by rfl, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold cliTryDecryptCommonHeapPlaced
    rw [lsLogOff_eq_macLsLogOff,
        trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_433_placed_ok' [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_macLsLogOff,
      trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  rw [cliTryDecryptSpecPlaced_onPanic_eq]
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesPlacedSpec C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [writeReg64_trace, setPC_trace, htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := sessionShimSpec) (x := ())
    (T := emp) (ret_pc := (blkPl_434).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimSpec]
  apply SepWPp.elim_pure; intro htr2
  simp only [writeReg64_trace, setPC_trace, setPState_trace, htr1] at htr2
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_frame_placed (spec := rustAllocSpec A) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := (blkPl_434).base + bv% (2340))
    hcl3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [writeReg64_trace, setPC_trace, htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_placed C A ctl S x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [writeReg64_trace, setPC_trace, htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_549_intro hcl3.2 hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_434).base + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold cliTryDecryptCommonHeapPlaced speBodyAt
        rw [lsLogOff_eq_macLsLogOff,
            trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_434).base + bv% (2520))
        hcl5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [writeReg64_trace, State.trace_writeVReg128, setPC_trace, setMem_trace, htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC ((blkPl_434).base + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC ((blkPl_434).base + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC ((blkPl_434).base + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC ((blkPl_434).base + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hcl6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hcl6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold cliTryDecryptCommonHeapPlaced speBodyAt
        rw [lsLogOff_eq_macLsLogOff,
            trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_433_placed_ok' [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_433_placed_ok' C A ctl S H hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_433_placed_ok' C A ctl S H hVMac hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

theorem subroutine_ok_verifyMacPlaced_of_spec [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {F : ShaCompress} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg F A parse))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec F A parse)) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
  · dsimp only [withLsCodeRoLoaded, verifyMacWithAddressesPlacedSpec,
      verifyMacWithAddressesPlacedSpecWithStack, verifyMacWithAddressesSpec] at hp ⊢
    rwa [← lsLogOff_eq_macLsLogOff, lsLogOff_eq_logOff_placed] at hp
  · dsimp only [withLsCodeRoLoaded, verifyMacWithAddressesPlacedSpec,
      verifyMacWithAddressesPlacedSpecWithStack, verifyMacWithAddressesSpec] at hq ⊢
    rwa [← lsLogOff_eq_macLsLogOff, lsLogOff_eq_logOff_placed]

theorem verifyMac_true_433_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) :=
  verifyMac_true_433_placed_ok' C A ctl S H (subroutine_ok_verifyMacPlaced_of_spec hVMac)
    x trG tr st1 mks newPqrState draws R s0 s hok h7 hL

theorem verifyMac_false_433_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) :=
  verifyMac_false_433_placed_ok' C A ctl S H (subroutine_ok_verifyMacPlaced_of_spec hVMac)
    hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok h7 hL

theorem verifyMac_433_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S :=
  verifyMac_433_placed_ok' C A ctl S H (subroutine_ok_verifyMacPlaced_of_spec hVMac)
    hshim halloc hdealloc hpan_ext

end CryptoVerification.Cli.SpqrV1.M4
