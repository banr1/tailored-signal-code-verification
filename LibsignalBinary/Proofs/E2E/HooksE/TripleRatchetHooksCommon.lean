/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksE.Common
import ProofLib.VCGen
import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitness -- shake: keep

/-!
# `TripleRatchetHooks` Witnesses for `absE`

Proves `HookOk` for the allocator, AES-256-CBC, and formatting hooks in
`TripleRatchetHooks C A0 spqrModelE (absE C env)`.
-/

@[expose] public section

namespace CryptoVerification.E2E.HooksE

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ witnessDeallocHook witnessDeallocHook_ok satisfies_mapFresh_unmapped
   readReg64_setPC_writeReg64_x0 bytesOf64 pointsTo64_eq_pointsToBytes)
open CryptoVerification.E2E
open HooksOkAux

namespace TripleRatchetHookFacts

theorem flatMap_blockToBytesLE_length (cs : List CBC.Block) :
    (cs.flatMap CBC.blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, CBC.blockToBytesLE,
      List.length_ofFn]
    omega

theorem aesCbcEncrypt_length_lt {E : CBC.AesKey → CBC.Block → CBC.Block}
    {k : CBC.AesKey} {iv : CBC.Block} {pt : List (BitVec 8)} (hpt : pt.length < 2 ^ 40) :
    (aesCbcEncrypt E k iv pt).length < 2 ^ 63 := by
  have hlen : (aesCbcEncrypt E k iv pt).length = 16 * (pt.length / 16 + 1) := by
    unfold aesCbcEncrypt
    rw [flatMap_blockToBytesLE_length, List.Vector.toList_length]
    rfl
  omega

theorem cbcDecryptBlocks_length (g : CBC.Block → CBC.Block) (prev : CBC.Block)
    (cs : List CBC.Block) :
    (CBC.cbcDecryptBlocks g prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [CBC.cbcDecryptBlocks, ih]

theorem pkcs7Unpad_length_le {bs pt : List (BitVec 8)} (h : CBC.pkcs7Unpad bs = some pt) :
    pt.length ≤ bs.length := by
  unfold CBC.pkcs7Unpad at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [List.length_take]
        omega
      · contradiction

theorem aesCbcDecrypt_length_lt {D : CBC.AesKey → CBC.Block → CBC.Block}
    {k : CBC.AesKey} {iv : CBC.Block} {ct pt : List (BitVec 8)}
    (hct : ct.length < 2 ^ 40) (hdec : aesCbcDecrypt D k iv ct = some pt) :
    pt.length < 2 ^ 63 := by
  unfold aesCbcDecrypt CBC.cbcDecRaw at hdec
  split at hdec
  · simp at hdec
  · have hle := pkcs7Unpad_length_le hdec
    rw [flatMap_blockToBytesLE_length, cbcDecryptBlocks_length, CBC.chunks16,
      List.length_ofFn] at hle
    omega

end TripleRatchetHookFacts

open TripleRatchetHookFacts

/-! ## Allocator Witnesses -/

theorem allocHook0_nw_ok : HookOk allocHook0 (rustAllocNWSpec A0) := by
  have heq : allocHook0 = retHook fun s =>
      match bumpAddr? s.mem (allocReq s).1 (allocReq s).2 with
      | some p => (s.setMem (s.mem.mapFresh p (allocReq s).1 Perm.rw)).writeReg64 .x0 p
      | none => (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64 := by
    funext s; unfold allocHook0 bumpThen allocFail retHook; dsimp only
    cases bumpAddr? s.mem (allocReq s).1 (allocReq s).2 <;> rfl
  rw [heq]
  refine retHook_ok fun ⟨size, align⟩ R s0 hrun hpre _hsp => ?_
  simp only [rustAllocNWSpec, rustAllocSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _hlayout⟩, hmem⟩
  unfold retHook allocReq
  dsimp only
  rw [hx0, hx1]
  split
  · rename_i p hp
    rcases bumpAddr?_spec hp with ⟨hp_ne, hp_al, _, hp_bound, hp_unmap⟩
    have hbase : heapBase.toNat = 2 ^ 60 := heapBase_toNat
    have hsize : heapSize = 2 ^ 60 := rfl
    have hp_nw : p.toNat + size < 2 ^ 64 := by omega
    refine ⟨Memory.keepsFrozen_mapFresh s0.mem p size Perm.rw, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [rustAllocNWSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hp_ne, ↓reduceIte, sepConj_assoc]
    have hmap := satisfies_mapFresh_unmapped hmem hp_unmap
    change s0.mem.mapFresh p size Perm.rw ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜p.toNat % align = 0 ∧ p.toNat + size < 2 ^ 64 ∧ s0.trace = s0.trace⌝ ∗
          (memRegion p size ∗ R))
    have heq' :
        (stackAt s0.sp allocHookStack ∗
          (⌜p.toNat % align = 0 ∧ p.toNat + size < 2 ^ 64 ∧ s0.trace = s0.trace⌝ ∗
            (memRegion p size ∗ R))) =
        (⌜p.toNat % align = 0 ∧ p.toNat + size < 2 ^ 64 ∧ s0.trace = s0.trace⌝ ∗
          (memRegion p size ∗ (stackAt s0.sp allocHookStack ∗ R))) := by
      ac_rfl
    rw [heq', satisfies_pure_sepConj]
    exact ⟨⟨hp_al, hp_nw, rfl⟩, hmap⟩
  · refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hzero : (0#64 : BitVec 64) = 0 := rfl
    dsimp only [rustAllocNWSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hzero, ↓reduceIte, sepConj_assoc]
    change s0.mem ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜s0.trace ++ [allocFailedEvent] = s0.trace ++ [allocFailedEvent]⌝ ∗ R)
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    exact ⟨rfl, hmem⟩

theorem allocHook0_ok : HookOk allocHook0 (rustAllocSpec A0) :=
  hookOk_rustAllocSpec_of_NW allocHook0_nw_ok

theorem deallocHook_ok : HookOk deallocHook (rustDeallocSpec A0) :=
  witnessDeallocHook_ok

theorem reallocHook0_ok : HookOk reallocHook0 (rustReallocSpec A0) := by
  have heq : reallocHook0 = retHook fun s =>
      let bs := s.mem.readBytes (s.readReg64 .x0) (min (s.readReg64 .x1).toNat (s.readReg64 .x3).toNat)
      match bumpAddr? s.mem (reallocReq s).1 (reallocReq s).2 with
      | some q => (s.setMem ((s.mem.mapFresh q (reallocReq s).1 Perm.rw).writeBytes q bs)).writeReg64 .x0 q
      | none => (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64 := by
    funext s; unfold reallocHook0 bumpThen allocFail retHook; dsimp only
    cases bumpAddr? s.mem (reallocReq s).1 (reallocReq s).2 <;> rfl
  rw [heq]
  refine retHook_ok fun ⟨p, old, align, new, bs⟩ R s0 hrun hpre _hsp => ?_
  simp only [rustReallocSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlayout, hbs_old, hbs_new⟩, hmem⟩
  have hnew_le : new ≤ 2 ^ 64 := by
    rcases hlayout with ⟨_, _, hle⟩
    omega
  unfold retHook reallocReq
  dsimp only
  rw [hx0, hx1, hx2, hx3]
  split
  · rename_i q hq
    rcases bumpAddr?_spec hq with ⟨hq_ne, hq_al, _, _, hq_unmap⟩
    let c := min old new
    have hc_le_new : c ≤ new := Nat.min_le_right old new
    have hbs_le_c : bs.length ≤ c := Nat.le_min.mpr ⟨hbs_old, hbs_new⟩
    obtain ⟨_, hread_bs⟩ := (IsBlock.pointsToBytes p bs).read hmem
    have hcopy_eq : s0.mem.readBytes p c =
        bs ++ s0.mem.readBytes (p + BitVec.ofNat 64 bs.length) (c - bs.length) := by
      have hc_split : c = bs.length + (c - bs.length) := by omega
      conv => lhs; rw [hc_split]
      rw [ProofLib.readBytes_add, hread_bs]
    let extra := s0.mem.readBytes (p + BitVec.ofNat 64 bs.length) (c - bs.length)
    have hextra_len : extra.length = c - bs.length := Memory.readBytes_length ..
    let copied := s0.mem.readBytes p c
    have hcopied_len : copied.length = c := Memory.readBytes_length ..
    let m1 := s0.mem.mapFresh q new Perm.rw
    have hm1 : m1 ⊨ memRegion q new ∗
        ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          (stackAt s0.sp allocHookStack ∗ R))) :=
      satisfies_mapFresh_unmapped hmem hq_unmap
    have hnew_split : new = copied.length + (new - c) := by omega
    rw [hnew_split, memRegion_split q copied.length (new - c) (by omega), sepConj_assoc] at hm1
    have hkf1 : s0.mem.KeepsFrozen m1 := Memory.keepsFrozen_mapFresh s0.mem q new Perm.rw
    have hkf2 : m1.KeepsFrozen (m1.writeBytes q copied) :=
      keepsFrozen_writeBytes_of_memRegion copied (by omega) hm1
    have hm2 := satisfies_writeBytes copied (by omega) hm1
    rw [hcopied_len] at hm2
    refine ⟨hkf1.trans hkf2, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [rustReallocSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hq_ne, ↓reduceIte, sepConj_assoc]
    change m1.writeBytes q copied ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜q.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗
          ((q ↦ₛ bs) ∗
            (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)))
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hq_al, rfl⟩, ?_⟩
    rw [show copied = bs ++ extra from hcopy_eq, pointsToBytes_append, sepConj_assoc] at hm2
    have hm2_ent : m1.writeBytes q (bs ++ extra) ⊨
        (q ↦ₛ bs) ∗
          (memRegion (q + BitVec.ofNat 64 bs.length) extra.length ∗
            (memRegion (q + BitVec.ofNat 64 c) (new - c) ∗
              ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                (stackAt s0.sp allocHookStack ∗ R))))) := by
      refine Satisfies.mono (sepConj_mono_right (sepConj_mono_left ?_)) hm2
      exact pointsToBytes_entails_memRegion (q + BitVec.ofNat 64 bs.length) extra
    rw [hextra_len, ← sepConj_assoc (memRegion (q + BitVec.ofNat 64 bs.length) (c - bs.length))] at hm2_ent
    have haddr_c : q + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (c - bs.length) =
        q + BitVec.ofNat 64 c := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hbs_le_c]
    have hmerge :
        (memRegion (q + BitVec.ofNat 64 bs.length) (c - bs.length) ∗
          memRegion (q + BitVec.ofNat 64 c) (new - c)) =
        memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) := by
      have hlen_eq : c - bs.length + (new - c) = new - bs.length := by omega
      rw [← haddr_c, ← memRegion_split (q + BitVec.ofNat 64 bs.length) (c - bs.length) (new - c) (by omega), hlen_eq]
    rw [hmerge] at hm2_ent
    have hrearr1 :
        ((q ↦ₛ bs) ∗
          (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
            ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              (stackAt s0.sp allocHookStack ∗ R))))) =
        (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) ∗
          (stackAt s0.sp allocHookStack ∗
            ((q ↦ₛ bs) ∗ (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)))) := by
      ac_rfl
    rw [hrearr1] at hm2_ent
    rw [← show copied = bs ++ extra from hcopy_eq] at hm2_ent
    exact Satisfies.of_sep_right hm2_ent
  · refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hzero : (0#64 : BitVec 64) = 0 := rfl
    dsimp only [rustReallocSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hzero, ↓reduceIte, sepConj_assoc]
    change s0.mem ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜s0.trace ++ [allocFailedEvent] = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)))
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    have hrearr :
        (stackAt s0.sp allocHookStack ∗
          ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R))) =
        ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          (stackAt s0.sp allocHookStack ∗ R))) := by
      ac_rfl
    rw [hrearr]
    exact hmem

theorem allocZeroedHook0_ok : HookOk allocZeroedHook0 (rustAllocZeroedSpec A0) := by
  have heq : allocZeroedHook0 = retHook fun s =>
      match bumpAddr? s.mem (allocReq s).1 (allocReq s).2 with
      | some p =>
        (s.setMem ((s.mem.mapFresh p (allocReq s).1 Perm.rw).writeBytes p
          (List.replicate (allocReq s).1 0#8))).writeReg64 .x0 p
      | none => (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64 := by
    funext s; unfold allocZeroedHook0 bumpThen allocFail retHook; dsimp only
    cases bumpAddr? s.mem (allocReq s).1 (allocReq s).2 <;> rfl
  rw [heq]
  refine retHook_ok fun ⟨size, align⟩ R s0 hrun hpre _hsp => ?_
  simp only [rustAllocZeroedSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlayout⟩, hmem⟩
  have hsize_le : size ≤ 2 ^ 64 := by
    rcases hlayout with ⟨_, _, hle⟩
    omega
  unfold retHook allocReq
  dsimp only
  rw [hx0, hx1]
  split
  · rename_i p hp
    rcases bumpAddr?_spec hp with ⟨hp_ne, hp_al, _, _, hp_unmap⟩
    let zs := List.replicate size (0#8 : BitVec 8)
    have hzs_len : zs.length = size := List.length_replicate ..
    let m1 := s0.mem.mapFresh p size Perm.rw
    have hm1 : m1 ⊨ memRegion p zs.length ∗ (stackAt s0.sp allocHookStack ∗ R) := by
      rw [hzs_len]
      exact satisfies_mapFresh_unmapped hmem hp_unmap
    have hkf1 : s0.mem.KeepsFrozen m1 := Memory.keepsFrozen_mapFresh s0.mem p size Perm.rw
    have hkf2 : m1.KeepsFrozen (m1.writeBytes p zs) :=
      keepsFrozen_writeBytes_of_memRegion zs (by omega) hm1
    have hm2 := satisfies_writeBytes zs (by omega) hm1
    refine ⟨hkf1.trans hkf2, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [rustAllocZeroedSpec, State.setMem] at hm2 ⊢
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hp_ne, ↓reduceIte, sepConj_assoc]
    change m1.writeBytes p zs ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜p.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗ ((p ↦ₛ zs) ∗ R))
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hp_al, rfl⟩, ?_⟩
    ac_nf at hm2 ⊢
  · refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hzero : (0#64 : BitVec 64) = 0 := rfl
    dsimp only [rustAllocZeroedSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, readReg64_setPC_writeReg64_x0, hzero, ↓reduceIte, sepConj_assoc]
    change s0.mem ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜s0.trace ++ [allocFailedEvent] = s0.trace ++ [allocFailedEvent]⌝ ∗ R)
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    exact ⟨rfl, hmem⟩

/-! ## AES-256-CBC Witnesses -/

theorem aesEncHook0_ok (E : CBC.AesKey → CBC.Block → CBC.Block) :
    HookOk (aesEncHook0 E) (aesEncSpec E A0) := by
  intro x R s0 hrun hpre hsp
  have hpre' := hpre
  simp only [aesEncSpec, AesCall.pre, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey_len, hiv_len, hin_lt⟩, hmem⟩
  obtain ⟨_, hread_in⟩ := (IsBlock.pointsToBytes x.inA x.input).read hmem
  have hmem_k : s0.mem ⊨ (x.keyA ↦ₛ x.key) ∗
      ((x.inA ↦ₛ x.input) ∗ ((x.ivA ↦ₛ x.iv) ∗ (memRegion x.ret 24 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  obtain ⟨_, hread_k⟩ := (IsBlock.pointsToBytes x.keyA x.key).read hmem_k
  have hmem_iv : s0.mem ⊨ (x.ivA ↦ₛ x.iv) ∗
      ((x.inA ↦ₛ x.input) ∗ ((x.keyA ↦ₛ x.key) ∗ (memRegion x.ret 24 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  obtain ⟨_, hread_iv⟩ := (IsBlock.pointsToBytes x.ivA x.iv).read hmem_iv
  have hin_eq : aesInput s0 = x.input := by
    unfold aesInput; rw [hx0, hx1, hread_in]
  have hkey_eq : aesKey s0 = x.key := by
    unfold aesKey; rw [hx2, ← hkey_len, hread_k]
  have hiv_eq : aesIv s0 = x.iv := by
    unfold aesIv; rw [hx4, ← hiv_len, hread_iv]
  let ct := aesCbcEncrypt E (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input
  have hout_eq : aesEncOut E s0 = ct := by
    unfold aesEncOut; rw [hin_eq, hkey_eq, hiv_eq]
  have hct_lt : ct.length < 2 ^ 63 := aesCbcEncrypt_length_lt hin_lt
  have hkv_ok : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
    rw [hx3, hx5]; decide
  have hcap_ok : ¬ 2 ^ 63 ≤ ((s0.readReg64 .x1).toNat / 16 + 1) * 16 := by
    rw [hx1]; omega
  unfold aesEncHook0
  simp only [hkv_ok, Bool.false_eq_true, hcap_ok, ↓reduceIte]
  rw [hout_eq]
  unfold returnFreshVecU8 bumpThen
  split
  · rename_i p hp
    have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
        (x.frame ∗ (stackAt s0.sp extHookStack ∗ R)) := by
      unfold AesCall.frame
      ac_nf at hmem ⊢
    have hx8' : (s0.setMem (s0.mem.mapFresh p ct.length Perm.rw)).readReg64 .x8 = x.ret := hx8
    dsimp only [retHook]
    rw [hx8']
    dsimp only [State.setMem]
    obtain ⟨hkf, hvec⟩ := vecOutThen_some hct_lt hp hmem_ret
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [aesEncSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    change writeVecHeader ((s0.mem.mapFresh p ct.length Perm.rw).writeBytes p ct)
      x.ret (BitVec.ofNat 64 ct.length) p (BitVec.ofNat 64 ct.length) ⊨
      x.frame ∗ (vecU8 A0 x.ret ct ∗ (stackAt s0.sp extHookStack ∗ R))
    ac_nf at hvec ⊢
  · exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre hsp

private theorem aesDecErr_ok {D : CBC.AesKey → CBC.Block → CBC.Block}
    {x : AesCall} {R : SepProp} {s0 : State} {m : Memory}
    (hrun : s0.status = .Running) (hx8 : s0.readReg64 .x8 = x.ret)
    (hdec : aesCbcDecrypt D (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input = none)
    (hkf0 : s0.mem.KeepsFrozen m)
    (hm_ret : m ⊨ memRegion x.ret 24 ∗ (x.frame ∗ (stackAt s0.sp extHookStack ∗ R))) :
    let sf := retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) (s0.setMem m)
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (aesDecSpec D A0) x R s0 sf := by
  have hx8' : (s0.setMem m).readReg64 .x8 = x.ret := hx8
  unfold retHook
  dsimp only
  rw [hx8']
  dsimp only [State.setMem]
  have hsplit : memRegion x.ret 24 =
      (∃∗ w0 : BitVec 64, x.ret ↦₆₄ w0) ∗
        ((∃∗ w1 : BitVec 64, (x.ret + 8#64) ↦₆₄ w1) ∗ memRegion (x.ret + 16#64) 8) := by
    rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide),
      memRegion_eight x.ret,
      memRegion_split' (b := x.ret + 8#64) (n := 8) (k := 8) (b' := x.ret + 16#64)
        rfl (by bv_omega) (by decide),
      memRegion_eight (x.ret + 8#64)]
  rw [hsplit] at hm_ret
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hm_ret
  rcases hm_ret with ⟨w1, w0, hmem0⟩
  have hkf1 := keepsFrozen_write64_of_pointsTo64 errTag hmem0
  have hw1 := satisfies_write64_of_pointsTo64 errTag hmem0
  have hmem1 : m.write64 x.ret errTag ⊨
      ((x.ret + 8#64) ↦₆₄ w1) ∗
        ((x.ret ↦₆₄ errTag) ∗ (memRegion (x.ret + 16#64) 8 ∗ (x.frame ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hw1 ⊢
  have hkf2 := hkf0.trans (hkf1.trans (keepsFrozen_write64_of_pointsTo64 1#64 hmem1))
  have hw2 := satisfies_write64_of_pointsTo64 1#64 hmem1
  refine ⟨hkf2, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [aesDecSpec]
  rw [hdec]
  simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists]
  refine ⟨1#64, ?_⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, satisfies_pure_sepConj]
  refine ⟨by decide, ?_⟩
  ac_nf at hw2 ⊢

theorem aesDecHook0_ok (D : CBC.AesKey → CBC.Block → CBC.Block) :
    HookOk (aesDecHook0 D) (aesDecSpec D A0) := by
  intro x R s0 hrun hpre hsp
  have hpre' := hpre
  simp only [aesDecSpec, AesCall.pre, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey_len, hiv_len, hin_lt⟩, hmem⟩
  obtain ⟨_, hread_in⟩ := (IsBlock.pointsToBytes x.inA x.input).read hmem
  have hmem_k : s0.mem ⊨ (x.keyA ↦ₛ x.key) ∗
      ((x.inA ↦ₛ x.input) ∗ ((x.ivA ↦ₛ x.iv) ∗ (memRegion x.ret 24 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  obtain ⟨_, hread_k⟩ := (IsBlock.pointsToBytes x.keyA x.key).read hmem_k
  have hmem_iv : s0.mem ⊨ (x.ivA ↦ₛ x.iv) ∗
      ((x.inA ↦ₛ x.input) ∗ ((x.keyA ↦ₛ x.key) ∗ (memRegion x.ret 24 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  obtain ⟨_, hread_iv⟩ := (IsBlock.pointsToBytes x.ivA x.iv).read hmem_iv
  have hin_eq : aesInput s0 = x.input := by
    unfold aesInput; rw [hx0, hx1, hread_in]
  have hkey_eq : aesKey s0 = x.key := by
    unfold aesKey; rw [hx2, ← hkey_len, hread_k]
  have hiv_eq : aesIv s0 = x.iv := by
    unfold aesIv; rw [hx4, ← hiv_len, hread_iv]
  have hout_eq : aesDecOut D s0 =
      aesCbcDecrypt D (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input := by
    unfold aesDecOut; rw [hin_eq, hkey_eq, hiv_eq]
  have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
      (x.frame ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    unfold AesCall.frame
    ac_nf at hmem ⊢
  unfold aesDecHook0
  dsimp only
  rw [hx1]
  by_cases hbad : (x.input.length == 0 || x.input.length % 16 != 0) = true
  · simp only [hbad, ↓reduceIte]
    have hdec0 : aesCbcDecrypt D (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input = none := by
      unfold aesCbcDecrypt CBC.cbcDecRaw
      have hor : x.input = [] ∨ x.input.length % 16 ≠ 0 := by
        simpa [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, List.length_eq_zero_iff] using hbad
      simp [hor]
    have hs0_id : s0.setMem s0.mem = s0 := by cases s0; rfl
    have herr := aesDecErr_ok hrun hx8 hdec0 (Memory.KeepsFrozen.refl s0.mem) hmem_ret
    dsimp only at herr
    rwa [hs0_id] at herr
  · have hkv_ok : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
      rw [hx3, hx5]; decide
    have hcap_ok : ¬ 2 ^ 63 ≤ x.input.length := by omega
    simp only [hbad, hkv_ok, Bool.false_eq_true, hcap_ok, ↓reduceIte]
    rw [hout_eq]
    rcases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input with _ | pt
    · dsimp only [bumpThen]
      split
      · rename_i q hq
        rcases bumpAddr?_spec hq with ⟨_, _, _, _, hq_unmap⟩
        have hkf0 := Memory.keepsFrozen_mapFresh s0.mem q x.input.length Perm.rw
        have hm1 := Satisfies.of_sep_right (satisfies_mapFresh_unmapped hmem_ret hq_unmap)
        exact aesDecErr_ok hrun hx8 hdec hkf0 hm1
      · exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre hsp
    · dsimp only
      by_cases hfit_ct : (bumpAddr? s0.mem x.input.length 1).isNone = true
      · simp only [hfit_ct, ↓reduceIte]
        exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre hsp
      · simp only [hfit_ct, Bool.false_eq_true, ↓reduceIte]
        have hpt_lt : pt.length < 2 ^ 63 := aesCbcDecrypt_length_lt hin_lt hdec
        dsimp only [returnFreshVecU8, bumpThen]
        split
        · rename_i p hp
          have hx8' : (s0.setMem (s0.mem.mapFresh p pt.length Perm.rw)).readReg64 .x8 = x.ret := hx8
          dsimp only [retHook]
          rw [hx8']
          dsimp only [State.setMem]
          obtain ⟨hkf, hvec⟩ := vecOutThen_some hpt_lt hp hmem_ret
          refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
          dsimp only [aesDecSpec]
          rw [hdec]
          simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
            emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨rfl, ?_⟩
          change writeVecHeader ((s0.mem.mapFresh p pt.length Perm.rw).writeBytes p pt)
            x.ret (BitVec.ofNat 64 pt.length) p (BitVec.ofNat 64 pt.length) ⊨
            x.frame ∗ (vecU8 A0 x.ret pt ∗ (stackAt s0.sp extHookStack ∗ R))
          ac_nf at hvec ⊢
        · exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre hsp

/-! ## Formatting Witnesses -/

theorem formatInnerHook0_ok : HookOk formatInnerHook0 (formatInnerSpec A0) := by
  refine retHook_ok fun ret R s0 hrun hpre _hsp => ?_
  simp only [formatInnerSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx8, hmem⟩
  dsimp only [formatInnerHook0, retHook]
  rw [hx8]
  have hkf := keepsFrozen_writeVecHeader_of_memRegion 0#64 1#64 0#64 hmem
  have hw := satisfies_writeVecHeader_of_memRegion 0#64 1#64 0#64 hmem
  have hvec := satisfies_vecU8_empty (by decide : (1#64 : BitVec 64) ≠ 0) hw
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [formatInnerSpec, State.setMem]
  simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepExists_sepConj_left, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  rw [satisfies_sepExists]
  exact ⟨[], hvec⟩

theorem fmtWriteHook0_ok : HookOk fmtWriteHook0 (fmtWriteSpec A0) := by
  refine retHook_ok fun ⟨v, bs⟩ R s0 hrun hpre _hsp => ?_
  simp only [fmtWriteSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hx0, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [fmtWriteSpec, fmtWriteHook0, retHook]
  simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, readReg64_setPC_writeReg64_x0, sepExists_sepConj_left, sepConj_assoc,
    satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [satisfies_sepExists]
  exact ⟨bs, hmem⟩

end CryptoVerification.E2E.HooksE
