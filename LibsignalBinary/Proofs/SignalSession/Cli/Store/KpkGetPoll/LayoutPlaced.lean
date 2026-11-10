/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymC
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Callee Cell Wrappers & Outer Bridge for `get_kyber_pre_key::{closure#0}`

Bridges relocatable callee contracts to cell-decomposed `KpkGetPoll` specs and lifts the inner
poll spec to `kpkGetPollSpecPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

private theorem entails_of_eq_p {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem entails_pure_right_p {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have htrue : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [htrue, ProofLib.pure_true, emp_sepConj]
  exact h

private theorem vecU8Buf_cap_lt_p {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {Q : SepProp} {m : Memory} (h : m ⊨ SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ Q) :
    cap.toNat < 2 ^ 63 := by
  unfold SpqrV1.Alloc.vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.1

private theorem vecU8Buf_split_raw_p (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil]
    refine Entails.trans (entails_pure_right_p hpure (Entails.refl _)) ?_
    exact entails_of_eq_p (ProofLib.emp_sepConj _).symm
  · simp only [hcap, ite_false]
    refine Entails.trans ?_ (sepConj_mono_right (entails_pure_right_p hpure (Entails.refl _)))
    exact entails_of_eq_p (by ac_rfl)

private theorem vecU8Buf_unsplit_raw_p (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ⊢ SpqrV1.Alloc.vecU8Buf A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  rw [← sepConj_assoc, sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => entails_pure_right_p hpure ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil, ProofLib.emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ite_false]
    exact entails_of_eq_p (by ac_rfl)

private theorem bytesAt_false_eq_p (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.ChainProofs.bytesAt false ptr bs = (ptr ↦ₛ bs) := rfl

private theorem kyberDeserialize_eq_p (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl
theorem deallocVecBuf_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {calleeStk : Nat} {F0 : FsFiles} {T0 : List TraceEvent}
    (hC : AllocContractsXCliPlaced A H)
    (hFs : TraceFsSound prog)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocVecBufCellsSpec A F0 T0 calleeStk)) := by
  have hDealloc0 := subroutine_ok_withFsInv hFs
    (dealloc_lscro_of_cli (callerProg := prog) hC hi) F0 T0
  intro ⟨cap, ptr, bs, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocVecBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hcap, hx0, hx1, hx2, hfsp⟩, hmem⟩
  subst hfsp
  unfold SpqrV1.Alloc.vecU8Buf at hmem
  have hcap0 : ¬(cap = 0) := hcap
  simp only [hcap0, ite_false] at hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hbs_le, hcap_lt, _⟩, hmem⟩
  have hcap_pos : 0 < cap.toNat := by
    by_cases hz : cap.toNat = 0
    · exact (hcap (BitVec.eq_of_toNat_eq hz)).elim
    · omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  have hreg : (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
    have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv_rhs => rw [heq]
    rw [memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨
      (withFsInv (StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)) F0 T0).pre
        (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by simp [hx1], by simp [hx2], hlay⟩, ?_⟩
    convert hmem_reg using 1; ac_rfl
  rcases hDealloc0 (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      deallocVecBufCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨⟨hfsf, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem decimal_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {F0 : FsFiles} {T0 : List TraceEvent} {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (StoreKit.withLsCodeRoLoaded lsmpl (decimalFsCellsSpec A F0 T0 calleeStk)) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDecimal F0 T0
  intro ⟨n, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [decimalFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨n, ret⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (decimalSpecPlaced A decStk) F0 T0).pre callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    unfold decimalSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hDec0 callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, decimalSpecPlaced, decimalFsCellsSpec,
      callG, keyName] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfsf, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, decimalSpecPlaced,
      decimalFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact allowPanic_frame (F := stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq.2)
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, decimalSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
theorem dirGet_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hFs : TraceFsSound prog)
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirGetFsCellsSpec rd pathOk A F0 T0 calleeStk)) := by
  have hGet0 := subroutine_ok_withFsInv hFs hGet F0 T0
  intro ⟨ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp⟩
    R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dirGetFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, ⟨hnlen, hdlen, hpOk⟩, hx0, hx1, hx2, hx3, hfsp⟩, hmem⟩
  subst hfsp
  have hfiles : s0.fs.files = F0 :=
    hfs0.files_eq (evs := []) (by simp [htr0]) (by intro _ h; cases h)
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName keyId).length := by
    rw [hx3, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  let nRest := vecU8BufRest A nCap nPtr (keyName keyId)
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hmem_sp : s0.mem ⊨ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
      (dirAt A self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hmem_bor : s0.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
      (dirAt A self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) :=
    Satisfies.mono (sepConj_mono_left (vecU8Buf_split_raw_p A nCap nPtr (keyName keyId))) hmem_sp
  let callG : DirGetGhost := ⟨ret, self, dir, nPtr, keyName keyId, false⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (dirGetSpecPlaced rd pathOk A getStk) F0 T0).pre callG s0 ∗
        (nRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    rw [memRegion_48_words6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk⟩, ?_⟩
    rw [bytesAt_false_eq_p]
    convert hmem_bor using 1; ac_rfl
  rcases hGet0 callG (nRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetFsCellsSpec, callG] at hq ⊢
    rw [hfiles, bytesAt_false_eq_p] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hr_disj, hq⟩
    have hq_unbor : sf.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
        (getResultAt A ret r ∗ dirAt A self dir ∗ stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) := by
      convert hq using 1; ac_rfl
    have hq_rest : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
        (getResultAt A ret r ∗ dirAt A self dir ∗ stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) :=
      Satisfies.mono (sepConj_mono_left (vecU8Buf_unsplit_raw_p A nCap nPtr (keyName keyId))) hq_unbor
    clear hq hq_unbor
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt, vecU8] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨fPtr, msgBs, sCap, sPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hspe1 : speWord 1 = 0x8000000000000001#64 := by decide
      have herr_tag : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = errTag := by decide
      let H := SpqrV1.Alloc.vecU8Buf A sCap sPtr msgBs ∗ (fPtr ↦ᵣ utf8 "read")
      refine ⟨.error (), 0x8000000000000001#64, sCap, sPtr,
        BitVec.ofNat 64 msgBs.length, fPtr, BitVec.ofNat 64 (utf8 "read").length, H, ?_⟩
      have hprop : dirGetPostProp rd A F0 T0 dir keyId sf (.error ())
          0x8000000000000001#64 sCap sPtr (BitVec.ofNat 64 msgBs.length)
          fPtr (BitVec.ofNat 64 (utf8 "read").length) H := by
        refine ⟨rfl, ⟨hr_disj.1.symm, hr_disj.2.trans htr0⟩, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, errResultAt, speAt, vecU8]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        have h40_eq : out + 8#64 + 32#64 = out + 40#64 := by bv_omega
        rw [herr_tag, ← hspe1, h8_eq, h16_eq, h40_eq]
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
        have hv : ((out + 16#64) ↦₆₄ sCap) ∗ ((out + 24#64) ↦₆₄ sPtr) ∗
            ((out + 32#64) ↦₆₄ BitVec.ofNat 64 msgBs.length) ∗
            SpqrV1.Alloc.vecU8Buf A sCap sPtr msgBs ⊢
            ∃∗ bs0 : List (BitVec 8), ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 16#64) c0 p0 bs0 := by
          refine Entails.trans ?_
            (Entails.sepExists_right msgBs
              (Entails.sepExists_right sCap
                (Entails.sepExists_right sPtr (Entails.refl _))))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by ac_rfl)
        have hf : ((out + 40#64) ↦₆₄ fPtr) ∗
            ((out + 48#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (fPtr ↦ᵣ utf8 "read") ⊢
            strRefAt (out + 40#64) (utf8 "read") := by
          unfold strRefAt
          refine Entails.sepExists_right fPtr ?_
          have h48_eq : out + 40#64 + asm64% boxSliceLenOff = out + 48#64 := by bv_omega
          rw [h48_eq]
          exact Entails.refl _
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right (sepConj_mono hv hf)) h32))
        exact entails_of_eq_p (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, H, stkRem] at hq ⊢
      rw [hspe1] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; ac_rfl
    · rcases hr_disj with ⟨hget_eq, htr_eq⟩
      dsimp only [getResultAt, vecResultAt, vecU8] at hq_rest
      rw [memRegion_16_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨g5, g4, bCap, bPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hok_tag : okTagVec = 0xFFFFFFFFFFFFFFFE#64 := by decide
      refine ⟨.ok bs, 0xFFFFFFFFFFFFFFFE#64, bCap, bPtr,
        BitVec.ofNat 64 bs.length, g4, g5, SpqrV1.Alloc.vecU8Buf A bCap bPtr bs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hget_eq.symm, hfsf, htr_eq.trans htr0, rfl, rfl, rfl⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, stkRem] at hq ⊢
      rw [hok_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    have hp : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (nRest ∗ stkRem)) ∗ R := by
      have h := hq.2
      convert h using 1; ac_rfl
    exact allowPanic_frame _root_.id hp
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim


theorem decode_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {F0 : FsFiles} {T0 : List TraceEvent} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 595) (decodeKyberPreKeyPlacedSpec A))
    (hFs : TraceFsSound prog)
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 595)
      (StoreKit.withLsCodeRoLoaded lsmpl (decodeFsCellsSpec A F0 T0 calleeStk)) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDec F0 T0
  intro ⟨ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp⟩
    R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [decodeFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, hlen_pos, hlen_lt, hx0, hx1, hx2, hfsp⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let bRest := vecU8BufRest A bCap bPtr bytes
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  have hmem_sp : s0.mem ⊨ SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hmem_bor : s0.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) :=
    Satisfies.mono (sepConj_mono_left (vecU8Buf_split_raw_p A bCap bPtr bytes)) hmem_sp
  let callG : DecodeGhost := ⟨bPtr, bytes, ret⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (decodeKyberPreKeyPlacedSpec A) F0 T0).pre callG s0 ∗
        (bRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    unfold decodeKyberPreKeyPlacedSpec decodeKyberPreKeyRawSpec
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    rw [memRegion_88_words11]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt⟩, ?_⟩
    convert hmem_bor using 1; ac_rfl
  rcases hDec0 callG (bRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec, decodeFsCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr_eq, hq⟩
    have hq_unbor : sf.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
        (kyberPreKeyResultAt A ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) := by
      convert hq using 1; ac_rfl
    have hq_rest : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
        (kyberPreKeyResultAt A ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) :=
      Satisfies.mono (sepConj_mono_left (vecU8Buf_unsplit_raw_p A bCap bPtr bytes)) hq_unbor
    clear hq hq_unbor
    have hdes := kyberDeserialize_eq_p bytes
    cases hsd : SignedPreKeyRecordStructure.decode bytes with
    | none =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, errResultAt, speAt] at hq_rest
      rw [show (asm% (speSize - spePayloadOff)) = 40 by rfl,
        show (88 - asm% (resultErrSpeOff + speSize)) = 32 by rfl,
        memRegion_40_cells, memRegion_32_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest ⊢
      rcases hq_rest with ⟨w10, w9, w8, w7, w6, w5, w4, w3, w2, hq⟩
      have herr_tag : errTag = 0xFFFFFFFFFFFFFFFF#64 := by decide
      refine ⟨0xFFFFFFFFFFFFFFFF#64, speWord 2, w2, w3, w4, w5, w6, w7, w8, w9, w10, emp, ?_⟩
      have hprop : decodePostProp A F0 T0 bytes sf
          0xFFFFFFFFFFFFFFFF#64 (speWord 2) w2 w3 w4 w5 w6 w7 w8 w9 w10 emp := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, rfl, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, kyberPreKeyResultAt, errResultAt, speAt]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        rw [h8_eq, h16_eq, ← herr_tag, sepConj_emp]
        have h40 := words5_entails_memRegion_40 (out + 16#64) w2 w3 w4 w5 w6
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40 h32
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right h40) h32))
        exact entails_of_eq_p (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words11At, stkRem] at hq ⊢
      rw [herr_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq ⊢
      convert hq using 1; ac_rfl
    | some m =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, signedPreKeyStructAt, vecU8] at hq_rest
      rw [memRegion_eq_exists_bytes (ret + 0x54#64) 4 (by decide)] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest ⊢
      rcases hq_rest with ⟨pad4, sigCap, sigPtr, skCap, skPtr, pkCap, pkPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf,
        SpqrV1.Alloc.vecU8At_eq_header_sep_buf,
        SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      have hpk_ex : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length)) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           (⌜pad4.length = 4⌝ ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      have hpk_lt : pkCap.toNat < 2 ^ 63 := vecU8Buf_cap_lt_p hpk_ex
      clear hpk_ex
      have hpad_ex : sf.mem ⊨ ⌜pad4.length = 4⌝ ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hpad_ex
      rcases hpad_ex with ⟨hpad_len, hq_nopad⟩
      have hlen8 : (unpack32 m.id ++ pad4).length = 8 := by simp [hpad_len]
      obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 hlen8
      have htail_word : ∀ a : BitVec 64,
          ((a + 0x50#64) ↦₃₂ m.id) ∗ ((a + 0x54#64) ↦ₛ pad4) =
            ((a + 0x50#64) ↦₆₄ w10) := fun a => by
        rw [pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, ← hw10,
          pointsToBytes_append, unpack32_length]
        have ha : a + 0x50#64 + BitVec.ofNat 64 4 = a + 0x54#64 := by bv_omega
        rw [ha]
      let H := SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ∗
        SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey ∗
        SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature
      refine ⟨pkCap, pkPtr, BitVec.ofNat 64 m.publicKey.length,
        skCap, skPtr, BitVec.ofNat 64 m.privateKey.length,
        sigCap, sigPtr, BitVec.ofNat 64 m.signature.length,
        m.timestamp, w10, H, ?_⟩
      have hprop : decodePostProp A F0 T0 bytes sf
          pkCap pkPtr (BitVec.ofNat 64 m.publicKey.length)
          skCap skPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp w10 H := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, hpk_lt, fun out => ?_⟩
        unfold words11At kpkAnsAt pkAnsAt kyberPreKeyResultAt signedPreKeyStructAt vecU8
        have h80 : out + 80#64 = out + 0x50#64 := rfl
        rw [h80, ← htail_word out]
        have hv1 : (out ↦₆₄ pkCap) ∗ ((out + 8#64) ↦₆₄ pkPtr) ∗
            ((out + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64, vecU8At A out c0 p0 m.publicKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right pkCap (Entails.sepExists_right pkPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          exact entails_of_eq_p (by ac_rfl)
        have hv2 : ((out + 24#64) ↦₆₄ skCap) ∗ ((out + 32#64) ↦₆₄ skPtr) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 0x18#64) c0 p0 m.privateKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right skCap (Entails.sepExists_right skPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by ac_rfl)
        have hv3 : ((out + 48#64) ↦₆₄ sigCap) ∗ ((out + 56#64) ↦₆₄ sigPtr) ∗
            ((out + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 0x30#64) c0 p0 m.signature := by
          refine Entails.trans ?_
            (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by ac_rfl)
        have hpad_ent : ((out + 0x54#64) ↦ₛ pad4) ⊢ memRegion (out + 0x54#64) 4 := by
          rw [← hpad_len]
          exact pointsToBytes_entails_memRegion (out + 0x54#64) pad4
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono hv1
            (sepConj_mono hv2
              (sepConj_mono hv3
                (sepConj_mono_right (sepConj_mono_right hpad_ent)))))
        exact entails_of_eq_p (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      have hre_pad : ((ret + 80#64) ↦₃₂ m.id) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) =
          (((ret + 80#64) ↦₃₂ m.id) ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by ac_rfl
      have hq_w10 : sf.mem ⊨ ((ret + 80#64) ↦₆₄ w10) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        rw [show ret + 80#64 = ret + 0x50#64 from rfl, ← htail_word ret, ← hre_pad]
        convert hq_nopad using 1; ac_rfl
      dsimp only [words11At, H, stkRem] at hq_w10 ⊢
      convert hq_w10 using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec, decodeFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    have hp : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (bRest ∗ stkRem)) ∗ R := by
      have h := hq.2
      convert h using 1; ac_rfl
    exact allowPanic_frame _root_.id hp
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, decodeKyberPreKeyPlacedSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem kpkGetPoll_placed_of_inner [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog ((blkPl_576).base)
        (StoreKit.withLsCodeRoLoaded lsmpl (cliKpkGetPollInnerSpec rd pathOk A calleeStk)))
    (hstk : 0x1b0 + calleeStk ≤ stk) :
    subroutine_ok prog ((blkPl_576).base)
      (kpkGetPollSpecPlaced rd pathOk A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  unfold kpkGetPollSpecPlaced at hpre
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hn1, hn2, hs1, hs2⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        memRegion x.out 88 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 432 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
    stackAt_kpkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 432))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (cliKpkGetPollInnerSpec rd pathOk A calleeStk)).pre x s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliKpkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨withFsInv_entry s0, hx0, hx8, hn1, hn2, hs1, hs2⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliKpkGetPollInnerSpec,
      kpkGetPollSpecPlaced, pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
      stackAt_kpkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliKpkGetPollInnerSpec,
      kpkGetPollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

end Placed

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
