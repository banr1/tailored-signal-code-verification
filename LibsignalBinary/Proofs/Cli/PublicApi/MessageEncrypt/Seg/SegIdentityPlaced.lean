/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentity
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Relocatable CLI `SegIdentity` Proof (`segIdentity_placed_okV`)

Verifies `SegIdentitySpecVPlaced` (`OtrStateVPlaced` at `+0x2c8` → `KeyStateVPlaced` at `+0x344`)
on `lsProg_464 Hk` (`blkPl_464`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Steppers (`lsProg_464 Hk`) -/

private theorem segIdentity_placed_step_pre [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x2c8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (lsmpl.base 29) s emp
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x2cc#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ emp)) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
private theorem segIdentity_placed_step_ok [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64}
    {c0 d0 u868 : BitVec 32} {c4 c30 d4 d30 u86c ub08 : BitVec 16}
    {c6 c14 c22 d6 d14 d22 ub00 : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x2cc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x344#64) s
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
        ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = sp + 0xb80#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
          ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true, ikChunks6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-! ## 2. Frame Split/Merge Helpers -/

private theorem exists_pointsTo16_of_memRegion2_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 2 ∗ R) :
    ∃ v : BitVec 16, m ⊨ (a ↦₁₆ v) ∗ R := by
  rw [memRegion_split a 1 1 (by decide), ProofLib.memRegion_one a,
      ProofLib.memRegion_one (a + 1#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨b0, b1, hm⟩ := hm
  rw [pointsTo8_pair] at hm
  exact ⟨_, hm⟩

private theorem exists_pointsTo32_of_memRegion4_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 4 ∗ R) :
    ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [ProofLib.memRegion_four a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem exists_pointsTo64_of_memRegion8_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 8 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private def identityRestFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordWithoutRemIk A sp g G sess taken ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  memRegion (sp + 0x350#64) 0x118 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

private theorem otrState_placed_mem_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr sp : BitVec 64)
    (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ (g : RecordGhost) (G : SessionGhost),
      g.cur = some G ∧
      (match taken.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      (m ⊨ emp ∗
        ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
          memRegion (sp + 0x580#64) 34 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt sp remoteIdentityKeyStack ∗
          identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) := by
  unfold takenSlots at hm
  simp only [sepConj_assoc] at hm
  obtain ⟨g, G, hgcur, hrem, hm⟩ := sessionRecordAt_taken_extract_remIk A sp sess taken hm
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x5de := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide)]
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  unfold encCommonPlaced at hm
  rw [hsp0, hlog, h46a, stackAt_sub sp encSubStack remoteIdentityKeyStack] at hm
  refine ⟨g, G, hgcur, hrem, ?_⟩
  unfold identityRestFramePlaced
  rw [emp_sepConj]
  exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm

private theorem remoteIk_placed_pre_frame [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R Pm1 : SepProp) (s0 s1 : State)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hrem : match taken.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm1 : Pm1 ⊢ emp)
    (hm1 : s1.mem ⊨ Pm1 ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        memRegion (sp + 0x580#64) 34 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) :
    s1.mem ⊨
      (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).pre
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 ∗
      (identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0 ∗ R) := by
  have hm1' := Satisfies.mono (sepConj_mono_left hPm1) hm1
  rw [emp_sepConj] at hm1'
  dsimp only [StoreKit.withLsRoCl, remoteIdentityKeyPlacedSpec]
  rw [hsp1]
  have h1 : s1.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64 ∧
        (match taken.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)⌝ ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        memRegion (sp + 0x580#64) 34 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) := by
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcrl1, ⟨hx0, hx8, hrem⟩, hm1'⟩
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) h1

private theorem remoteIk_placed_post_repack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hgcur : g.cur = some G)
    (htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨
      ((StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).post
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 s2 ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧
    s2.trace = s1.trace ∧
    (s2.mem ⊨
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) := by
  dsimp only [StoreKit.withLsRoCl, remoteIdentityKeyPlacedSpec] at hpost
  rw [hsp1, htaken_rem] at hpost
  dsimp only [remoteIdentityOkAt] at hpost
  have h581 : (sp + 0x580#64) + 1#64 = sp + 0x581#64 := by bv_omega
  have h582 : (sp + 0x580#64) + 2#64 = sp + 0x582#64 := by bv_omega
  rw [h581, h582] at hpost
  have h1 : s2.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
      ⌜s2.trace = s1.trace⌝ ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hcrl2, htr, hmem⟩
  refine ⟨hcrl2, htr, ?_⟩
  unfold identityRestFramePlaced at hmem
  have hrec := sessionRecordAt_taken_restore_remIk A sp g G sess taken hgcur
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  have hmem_rearr : s2.mem ⊨
      (vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        sessionRecordWithoutRemIk A sp g G sess taken) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
        stackAt sp remoteIdentityKeyStack) ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack remoteIdentityKeyStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold encCommonPlaced
  rw [hsp0, hlog]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem_fold

private def identityStepFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64) (s0 : State) : SepProp :=
  (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5a2#64) 0x2c6 ∗
  memRegion (sp + 0x86e#64) 0x292 ∗
  memRegion (sp + 0xb0a#64) 0x76 ∗
  memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0

private theorem remoteIk_placed_ok_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64)
    (R : SepProp) (s0 s2 : State)
    (hm : s2.mem ⊨
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ (c0 d0 u868 : BitVec 32) (c4 c30 d4 d30 u86c ub08 : BitVec 16)
      (c6 c14 c22 d6 d14 d22 ub00 : BitVec 64),
      (∀ o : BitVec 64,
        (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) =
          ikChunks6 o c0 c4 c6 c14 c22 c30) ∧
      (s2.mem ⊨
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
          ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08)) ∗
        (identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R)) := by
  obtain ⟨c0, c4, c6, c14, c22, c30, hpack⟩ :=
    exists_ikChunks6_of_length_32 (bs := otr.remoteIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  rw [hpack (sp + 0x582#64)] at hm
  have h350 : memRegion (sp + 0x350#64) 0x118 =
      memRegion (sp + 0x350#64) 32 ∗ memRegion (sp + 0x370#64) 0xf8 :=
    mr_cut_add sp 0x350 32 0xf8 (by decide)
  have h5a2 : memRegion (sp + 0x5a2#64) 0x5de =
      memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x5a2#64 = sp + BitVec.ofNat 64 0x5a2 from rfl,
        mr_cut_add sp 0x5a2 0x2c6 0x318 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6) 4 0x314 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4) 2 0x312 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  rw [h350, h5a2] at hm
  have hm_d : s2.mem ⊨ memRegion (sp + 0x350#64) 32 ∗
      (memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R) := by
    unfold identityStepFramePlaced
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm
  obtain ⟨d0, d4, d6, d14, d22, d30, hm_d⟩ :=
    exists_ikChunks6_of_memRegion32 (sp + 0x350#64) hm_d
  have hm_868 : s2.mem ⊨ memRegion (sp + 0x868#64) 4 ∗
      (memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0xb00#64) 8 ∗
        memRegion (sp + 0xb08#64) 2 ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_d
  obtain ⟨u868, hm_868⟩ := exists_pointsTo32_of_memRegion4_placed (sp + 0x868#64) hm_868
  have hm_86c : s2.mem ⊨ memRegion (sp + 0x86c#64) 2 ∗
      (memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_868
  obtain ⟨u86c, hm_86c⟩ := exists_pointsTo16_of_memRegion2_placed (sp + 0x86c#64) hm_86c
  have hm_b00 : s2.mem ⊨ memRegion (sp + 0xb00#64) 8 ∗
      (memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_86c
  obtain ⟨ub00, hm_b00⟩ := exists_pointsTo64_of_memRegion8_placed (sp + 0xb00#64) hm_b00
  have hm_b08 : s2.mem ⊨ memRegion (sp + 0xb08#64) 2 ∗
      (((sp + 0xb00#64) ↦₆₄ ub00) ∗
        ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_b00
  obtain ⟨ub08, hm_b08⟩ := exists_pointsTo16_of_memRegion2_placed (sp + 0xb08#64) hm_b08
  refine ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, ?_⟩
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_b08

private theorem remoteIk_placed_ok_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (c0 : BitVec 32) (c4 c30 : BitVec 16) (c6 c14 c22 : BitVec 64)
    (sp : BitVec 64) (R Pm3 : SepProp) (s0 s3 : State)
    (hpack : ∀ o : BitVec 64,
      (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) =
        ikChunks6 o c0 c4 c6 c14 c22 c30)
    (hPm3 : Pm3 ⊢
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
      ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))
    (hm3 : s3.mem ⊨ Pm3 ∗ (identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R)) :
    s3.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm3) hm3
  rw [← hpack (sp + 0x350#64)] at hm1
  have h580_ent :
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ⊢
      memRegion (sp + 0x580#64) 34 := by
    rw [show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
        mr_cut_add sp 0x580 1 33 (by decide),
        mr_cut_add sp (0x580 + 1) 1 32 (by decide)]
    exact sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (ikChunks6_entails_memRegion _ _ _ _ _ _ _))
  have h868_ent :
      ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ⊢
      memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 :=
    sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo16_entails_memRegion _ _)
  have hb00_ent :
      ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30) ⊢
      memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 :=
    sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo16_entails_memRegion _ _)
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34) 0x2c6 0x318 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6) 4 0x314 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4) 2 0x312 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  unfold identityStepFramePlaced at hm1
  have hm_rearr : s3.mem ⊨
      (((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30) ∗
      (((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4)) ∗
      (((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30)) ∗
      ((∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗
        memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb0a#64) 0x76 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono h580_ent (sepConj_mono h868_ent (sepConj_mono_left hb00_ent))) hm_rearr
  have hm_poll : s3.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold takenSlots
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_poll

/-! ## 3. Main Segment Proof (`segIdentity_placed_okV`) -/

theorem segIdentity_placed_okV [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegIdentitySpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk := by
  intro env x r sess otr taken pqCap pqPtr R0 s0 s hotrState
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hotrState with ⟨hcur, hsc, hfrom, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hsp_x29 : s0.sp - 0x60#64 = sp + 0xb80#64 := by
    rw [← hsp0]; bv_omega
  have hs_pc' : s.pc = encEntryPlaced + 0x2c8#64 := hs_pc
  have htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey :=
    taken_remoteIdentity_eq_some hfrom
  obtain ⟨g, G, hgcur, hrem, hm_unp⟩ :=
    otrState_placed_mem_unpack A ctl x sess otr taken pqCap pqPtr sp R s0 hsp0 hm
  refine SegExitPlaced.of_sepWP hm_unp
    (segIdentity_placed_step_pre hs_pc' hrun hsp) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x22, hs1_x23, hs1_x24, hs1_x25,
      hs1_x26, hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := remoteIk_placed_pre_frame A ctl x g G sess taken pqCap pqPtr otr sp R Pm1 s0 s1
    hcrl1 hrem hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExitPlaced.call env.callees.remoteIk
    ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).onExit
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ code s1 _ = ⌜False⌝
            from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun _ _ _ hpan => by
      rw [show (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).onPanic
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 _ = ⌜False⌝
            from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan
      exact hpan.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x23 : s2.readReg64 .x23 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x29 : s2.readReg64 .x29 = sp + 0xb80#64 := by reg_chain
  obtain ⟨hcrl2, hs2_tr, hm2⟩ := remoteIk_placed_post_repack A ctl x g G sess taken pqCap pqPtr otr
    sp R s0 s1 s2 hgcur htaken_rem hsp0 hs1_sp hpost2
  obtain ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, hm2_unp⟩ :=
    remoteIk_placed_ok_unpack A ctl x sess taken pqCap pqPtr otr sp R s0 s2 hm2
  refine SegExitPlaced.of_sepWP hm2_unp
    (segIdentity_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x23 hs2_x24 hs2_x25 hs2_x29) ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x25, hs3_x26,
      hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_ok := remoteIk_placed_ok_pack A ctl x sess taken pqCap pqPtr otr
    c0 c4 c30 c6 c14 c22 sp R Pm3 s0 s3 hpack hPm3 hm3
  refine SegExitPlaced.next ⟨otr.remoteIdentityKey, hcur, hsc, hfrom, htaken_rem, ?_⟩
  exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
    by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩, by reg_chain,
    ⟨hs3_x0, hs3_x8, by reg_chain, by reg_chain, hs3_x23, hs3_x25,
      by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk, hm3_ok⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
