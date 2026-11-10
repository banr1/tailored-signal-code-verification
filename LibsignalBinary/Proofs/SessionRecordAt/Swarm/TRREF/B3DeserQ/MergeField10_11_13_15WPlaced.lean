/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenIdentityRootKeysExt
public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` `SessionStructure::merge_field` on Tags 10, 11, 13, and 15

Verifies `<SessionStructure as prost::Message>::merge_field::<&mut &[u8]>` on `lsProg_15 H`
(Block `15`) at `mergeFieldStackX` with slice length `< 2 ^ 62` for tags 10 and 11 (`uint32` via
`int32::merge`) and tags 13 and 15 (`Vec<u8>` via `bytes::merge`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ.DQ5Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
open CryptoVerification.E2E.Record.L1GX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem L1_MergeField10_11_13_15WPlaced : True := trivial

private theorem int64_raw_toBitVec_dq5p (n : Nat) (h : n < 2 ^ 64) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % (2 ^ 64)
  exact (Nat.mod_eq_of_lt h).symm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys int64_raw_toBitVec_dq5p
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys

/-- The 4 jump-table bytes at `lsmpl.ρ mergeFieldRodataSym + k` for tags 10 (`+9 = 214#8`),
11 (`+10 = 203#8`), 13 (`+12 = 0x0b#8`), and 15 (`+14 = 0x24#8`). -/
def mfRoBytes_placed [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ mergeFieldRodataSym + 9#64) ↦₈ᵣ 214#8) ∗
  ((lsmpl.ρ mergeFieldRodataSym + 10#64) ↦₈ᵣ 203#8) ∗
  ((lsmpl.ρ mergeFieldRodataSym + 12#64) ↦₈ᵣ 0x0b#8) ∗
  ((lsmpl.ρ mergeFieldRodataSym + 14#64) ↦₈ᵣ 0x24#8)

theorem rodata_placed_intro [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ mfRoBytes_placed ∗ P := by
  have h14 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 14#64) ↦₈ᵣ 0x24#8) ∗ P :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) hP
  have h12 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 12#64) ↦₈ᵣ 0x0b#8) ∗
      (((lsmpl.ρ mergeFieldRodataSym + 14#64) ↦₈ᵣ 0x24#8) ∗ P) :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) h14
  have h10 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 10#64) ↦₈ᵣ 203#8) ∗
      (((lsmpl.ρ mergeFieldRodataSym + 12#64) ↦₈ᵣ 0x0b#8) ∗
        (((lsmpl.ρ mergeFieldRodataSym + 14#64) ↦₈ᵣ 0x24#8) ∗ P)) :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) h12
  have h9 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 9#64) ↦₈ᵣ 214#8) ∗
      (((lsmpl.ρ mergeFieldRodataSym + 10#64) ↦₈ᵣ 203#8) ∗
        (((lsmpl.ρ mergeFieldRodataSym + 12#64) ↦₈ᵣ 0x0b#8) ∗
          (((lsmpl.ρ mergeFieldRodataSym + 14#64) ↦₈ᵣ 0x24#8) ∗ P))) :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) h10
  unfold mfRoBytes_placed
  simpa only [sepConj_assoc] using h9

private theorem stackAt_bytesMergeW_eq_int32MergeW_p (sp : BitVec 64) :
    stackAt sp Prost.X.bytesMergeStackW =
      memRegion (sp - 24880#64) 144 ∗ stackAt sp Prost.X.int32MergeStackW :=
  ProofLib.stackAt_split_bottom sp Prost.X.int32MergeStackW 144 (by decide)

theorem step_cbz_epilogue_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (retOff w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hret : retOff = 936#64 ∨ retOff = 892#64 ∨ retOff = 124#64 ∨ retOff = 224#64)
    (hpc : s.pc = (blkPl_15).base + retOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s P Q Qp := by
  apply ProofLib.SepWPp.of_sepWP (mid := (blkPl_15).base + 1880#64)
  rcases hret with rfl | rfl | rfl | rfl
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys (H := H) w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys (H := H) w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys (H := H) w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys (H := H) w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext

def bytesPost (ss fieldOff bufRef slot ptr : BitVec 64)
    (bytes payload tail : List (BitVec 8)) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
    vecU8 A0 (ss + fieldOff) bytes ∗ (bufRef ↦₆₄ slot) ∗
    Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
    stackAt s0.sp mergeFieldStackX

def u32Post (ss fieldOff bufRef slot ptr : BitVec 64) (val : BitVec 32)
    (payload tail : List (BitVec 8)) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
    ((ss + fieldOff) ↦₃₂ val) ∗ (bufRef ↦₆₄ slot) ∗
    Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
    stackAt s0.sp mergeFieldStackX

def panicPost (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem finish_post_placed_bytes [LibsignalPlacement]
    (ss fieldOff bufRef slot ptr w56 : BitVec 64)
    (bytes payload tail : List (BitVec 8))
    {s0 sf : State} {R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((bufRef ↦₆₄ slot) ∗
          stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          vecU8 A0 (ss + fieldOff) bytes ∗
          Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))) ∗ R) :
    sf.mem ⊨ bytesPost ss fieldOff bufRef slot ptr bytes payload tail s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_placed ∗
      ((mfUnusedStack_identityRootKeys_extW s0.sp ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        (vecU8 A0 (ss + fieldOff) bytes ∗
          (bufRef ↦₆₄ slot) ∗
          Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          R)) := by
    convert hmf using 1; sep_eq
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono
    (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys_extW s0.sp s0 w56)) h2
  dsimp only [bytesPost]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; sep_eq

set_option maxHeartbeats 1600000 in
theorem step_bytesMerge_call_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H)
    (ss fieldOff bufRef slot ptr retOff w56 : BitVec 64)
    (oldBytes bytes payload tail : List (BitVec 8))
    {s0 sm : State} {R : SepProp}
    (hret : retOff = 124#64 ∨ retOff = 224#64)
    (hpcm : sm.pc = lsmpl.base 7)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hcrlm : LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = (blkPl_15).base + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = ss + fieldOff)
    (hx2m : sm.readReg64 .x2 = bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hmerge : mergeBytes .lengthDelimited (payload ++ tail) = some (bytes, tail))
    (hlen : (payload ++ tail).length < 2 ^ 62) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) sm
      (vecU8 A0 (ss + fieldOff) oldBytes ∗
        (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ bytesPost ss fieldOff bufRef slot ptr bytes payload tail s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ panicPost s0 sf ∗ R)) := by
  have hcall : subroutine_ok (lsProg_15 H) (lsmpl.base 7) (Prost.X.bytesMergePlacedSpecW A0) :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine ProofLib.SepWPp.exists_elim (fun cap0 => ProofLib.SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, ss + fieldOff, cap0, ptr0, oldBytes, bufRef, slot, ptr, payload ++ tail⟩
  refine SepWPp.call_lscro (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
      (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
    hcall hpcm hrunm hspm_align hcrlm hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    have hpool : A0.pool = emp := rfl
    dsimp only [Prost.X.bytesMergeRawSpecW, g]
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = ss + fieldOff ∧ sm.readReg64 .x2 = bufRef ∧
        (payload ++ tail).length < 2 ^ 62 :=
      ⟨hx0m, hx1m, hx2m, hlen⟩
    rw [hspm, hpool, pure_true_emp_identityRootKeys hp2]
    simp only [emp_sepConj]
    convert hm using 1; sep_eq
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.X.bytesMergeRawSpecW, panicPost] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 _hcrl2 hcs2
    dsimp only [Prost.X.bytesMergeRawSpecW, g]
    rw [hmerge]
    dsimp only
    rw [sepConj_assoc]
    refine ProofLib.SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine ProofLib.SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A0 (ss + fieldOff) cap' ptr' bytes) =
        vecU8 A0 (ss + fieldOff) bytes := rfl
    rw [hvec]
    refine step_cbz_epilogue_placed (H := H) retOff w56
      (F := (bufRef ↦₆₄ slot) ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        vecU8 A0 (ss + fieldOff) bytes ∗
        Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
      (Or.inr (Or.inr hret)) hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      ((CalleeSavedPreserved.vregs hcs2).trans hvm)
      (by sep_eq) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_placed_bytes ss fieldOff bufRef slot ptr w56 bytes payload tail htrf hx0f, hspf, hcsf⟩

set_option maxHeartbeats 1600000 in
theorem mergeFieldBytes_placed_sepWPp [LibsignalPlacement]
    {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H)
    (h_case : (tag = 13 ∧ fieldOff = 0x60#64) ∨ (tag = 15 ∧ fieldOff = 0x78#64))
    (ss bufRef slot ptr : BitVec 64)
    (oldBytes bytes payload tail : List (BitVec 8))
    {s0 : State} {R : SepProp}
    (hpc : s0.pc = (blkPl_15).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hmerge : mergeBytes .lengthDelimited (payload ++ tail) = some (bytes, tail))
    (hlen : (payload ++ tail).length < 2 ^ 62)
    (hmem : s0.mem ⊨
      vecU8 A0 (ss + fieldOff) oldBytes ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt s0.sp mergeFieldStackX ∗ R) :
    ∃ P F : SepProp, (s0.mem ⊨ P ∗ F) ∧
      SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ F) → (sf.mem ⊨ bytesPost ss fieldOff bufRef slot ptr bytes payload tail s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ F) → (sf.mem ⊨ panicPost s0 sf ∗ R)) := by
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_placed ∗ vecU8 A0 (ss + fieldOff) oldBytes ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt s0.sp mergeFieldStackX) ∗ R := by
    refine Satisfies.mono (Entails.of_eq (by sep_eq))
      (rodata_placed_intro hcrl0.2 hmem)
  refine ⟨mfRoBytes_placed ∗ vecU8 A0 (ss + fieldOff) oldBytes ∗ (bufRef ↦₆₄ slot) ∗
    Prost.sliceCursorAt slot ptr (payload ++ tail) ∗ stackAt s0.sp mergeFieldStackX,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys_extW s0.sp]
  unfold mfRoBytes_placed
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWPp.exists_elim (fun w80 => ProofLib.SepWPp.exists_elim (fun w72 =>
    ProofLib.SepWPp.exists_elim (fun w64 => ProofLib.SepWPp.exists_elim (fun w56 =>
      ProofLib.SepWPp.exists_elim (fun w48 => ProofLib.SepWPp.exists_elim (fun w40 =>
        ProofLib.SepWPp.exists_elim (fun w32 => ProofLib.SepWPp.exists_elim (fun w24 =>
          ProofLib.SepWPp.exists_elim (fun w16 => ProofLib.SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  rcases h_case with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_bytesMerge_call_placed hbytes ss 0x60#64 bufRef slot ptr 124#64 w56
        oldBytes bytes payload tail
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_bytesMerge_call_placed hbytes ss 0x78#64 bufRef slot ptr 224#64 w56
        oldBytes bytes payload tail
        (Or.inr rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq

private theorem finish_post_placed_u32 [LibsignalPlacement]
    (ss fieldOff bufRef slot ptr w56 : BitVec 64)
    (val : BitVec 32) (payload tail : List (BitVec 8))
    {s0 sf : State} {R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((bufRef ↦₆₄ slot) ∗
          (memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
            stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW) ∗
          ((ss + fieldOff) ↦₃₂ val) ∗
          Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))) ∗ R) :
    sf.mem ⊨ u32Post ss fieldOff bufRef slot ptr val payload tail s0 sf ∗ R := by
  rw [← stackAt_bytesMergeW_eq_int32MergeW_p (s0.sp - 240#64)] at hmf
  have h1 : sf.mem ⊨ mfRoBytes_placed ∗
      ((mfUnusedStack_identityRootKeys_extW s0.sp ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        (((ss + fieldOff) ↦₃₂ val) ∗
          (bufRef ↦₆₄ slot) ∗
          Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          R)) := by
    convert hmf using 1; sep_eq
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono
    (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys_extW s0.sp s0 w56)) h2
  dsimp only [u32Post]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; sep_eq

set_option maxHeartbeats 1600000 in
theorem step_int32Merge_call_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H)
    (ss fieldOff bufRef slot ptr retOff w56 : BitVec 64)
    (oldVal val : BitVec 32) (payload tail : List (BitVec 8))
    {s0 sm : State} {R : SepProp}
    (hret : retOff = 936#64 ∨ retOff = 892#64)
    (hpcm : sm.pc = lsmpl.base 8)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hcrlm : LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = (blkPl_15).base + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 0#8)
    (hx1m : sm.readReg64 .x1 = ss + fieldOff)
    (hx2m : sm.readReg64 .x2 = bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hmerge : mergeUint32 .varint (payload ++ tail) = some (val, tail))
    (hlen : (payload ++ tail).length < 2 ^ 62) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) sm
      (((ss + fieldOff) ↦₃₂ oldVal) ∗
        (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ u32Post ss fieldOff bufRef slot ptr val payload tail s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ panicPost s0 sf ∗ R)) := by
  have hcall : subroutine_ok (lsProg_15 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.int32MergeSpecW A0)) :=
    ls_call_ro_of_cl (callerProg := lsProg_15 H) hint32
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  let g : Prost.Int32MergeGhost :=
    ⟨.varint, ss + fieldOff, bufRef, slot, ptr, payload ++ tail⟩
  refine SepWPp.call_lscro (x := g)
    (F := memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
      mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
      (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
    hcall hpcm hrunm hspm_align hcrlm hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_bytesMergeW_eq_int32MergeW_p (s0.sp - 240#64)] at hm
    have hcell : ((ss + fieldOff) ↦₃₂ oldVal) ⊢ memRegion (ss + fieldOff) 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right oldVal (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hcell)) hm
    have hpool : A0.pool = emp := rfl
    dsimp only [Prost.X.int32MergeSpecW, g]
    have hlen63 : (payload ++ tail).length < 2 ^ 63 :=
      Nat.lt_trans hlen (by decide)
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
        sm.readReg64 .x1 = ss + fieldOff ∧ sm.readReg64 .x2 = bufRef ∧
        (payload ++ tail).length < 2 ^ 63 :=
      ⟨hx0m, hx1m, hx2m, hlen63⟩
    rw [hspm, hpool, pure_true_emp_identityRootKeys hp2]
    simp only [emp_sepConj]
    convert hm1 using 1; sep_eq
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.X.int32MergeSpecW, panicPost] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 _hcrl2 hcs2
    dsimp only [Prost.X.int32MergeSpecW, g]
    rw [hmerge]
    dsimp only
    rw [sepConj_assoc]
    refine ProofLib.SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine ProofLib.SepWPp.pure_left (fun hx0_2 => ?_)
    have hret_all : retOff = 936#64 ∨ retOff = 892#64 ∨ retOff = 124#64 ∨ retOff = 224#64 := by
      rcases hret with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    refine step_cbz_epilogue_placed (H := H) retOff w56
      (F := (bufRef ↦₆₄ slot) ∗
        (memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
          stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW) ∗
        ((ss + fieldOff) ↦₃₂ val) ∗
        Prost.sliceCursorAfter slot ptr (payload ++ tail) tail ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed))
      hret_all hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      ((CalleeSavedPreserved.vregs hcs2).trans hvm)
      (by sep_eq) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_placed_u32 ss fieldOff bufRef slot ptr w56 val payload tail htrf hx0f, hspf, hcsf⟩

set_option maxHeartbeats 1600000 in
theorem mergeFieldU32_placed_sepWPp [LibsignalPlacement]
    {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H)
    (h_case : (tag = 10 ∧ fieldOff = 0x150#64) ∨ (tag = 11 ∧ fieldOff = 0x154#64))
    (ss bufRef slot ptr : BitVec 64)
    (oldVal val : BitVec 32) (payload tail : List (BitVec 8))
    {s0 : State} {R : SepProp}
    (hpc : s0.pc = (blkPl_15).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hmerge : mergeUint32 .varint (payload ++ tail) = some (val, tail))
    (hlen : (payload ++ tail).length < 2 ^ 62)
    (hmem : s0.mem ⊨
      ((ss + fieldOff) ↦₃₂ oldVal) ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt s0.sp mergeFieldStackX ∗ R) :
    ∃ P F : SepProp, (s0.mem ⊨ P ∗ F) ∧
      SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ F) → (sf.mem ⊨ u32Post ss fieldOff bufRef slot ptr val payload tail s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ F) → (sf.mem ⊨ panicPost s0 sf ∗ R)) := by
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_placed ∗ ((ss + fieldOff) ↦₃₂ oldVal) ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot ptr (payload ++ tail) ∗
        stackAt s0.sp mergeFieldStackX) ∗ R := by
    refine Satisfies.mono (Entails.of_eq (by sep_eq))
      (rodata_placed_intro hcrl0.2 hmem)
  refine ⟨mfRoBytes_placed ∗ ((ss + fieldOff) ↦₃₂ oldVal) ∗ (bufRef ↦₆₄ slot) ∗
    Prost.sliceCursorAt slot ptr (payload ++ tail) ∗ stackAt s0.sp mergeFieldStackX,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys_extW s0.sp]
  unfold mfRoBytes_placed
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWPp.exists_elim (fun w80 => ProofLib.SepWPp.exists_elim (fun w72 =>
    ProofLib.SepWPp.exists_elim (fun w64 => ProofLib.SepWPp.exists_elim (fun w56 =>
      ProofLib.SepWPp.exists_elim (fun w48 => ProofLib.SepWPp.exists_elim (fun w40 =>
        ProofLib.SepWPp.exists_elim (fun w32 => ProofLib.SepWPp.exists_elim (fun w24 =>
          ProofLib.SepWPp.exists_elim (fun w16 => ProofLib.SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  rcases h_case with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_int32Merge_call_placed hint32 ss 0x150#64 bufRef slot ptr 936#64 w56
        oldVal val payload tail
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_int32Merge_call_placed hint32 ss 0x154#64 bufRef slot ptr 892#64 w56
        oldVal val payload tail
        (Or.inr rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq

end Symbolic.Swarm.TRREF.B3DeserQ.DQ5Placed

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open Proofs.libsignal.Hooks2

/-- Image-free raw `L1GX.mergeFieldXSpec` at `mergeFieldStackX` with slice length `< 2 ^ 62`. -/
def mergeFieldXRawSpecW (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostSSGXAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGXAt A0 x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- Relocatable `mergeFieldXRawSpecW P` wrapped with `LibsignalCodeRoLoaded lsmpl`. -/
abbrev mergeFieldXPlacedSpecW [LibsignalPlacement] (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldXRawSpecW P)

/-- `subroutine_ok` for `mergeFieldXPlacedSpecW P` on `lsProg_15 H` (`(blkPl_15).base`). -/
def MergeFieldXPlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldX → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldXPlacedSpecW P)

/-- General framing combinator lifting a placed single-field `subroutine_ok` contract to a
full-struct `Spec` with `Serialization.allocPanic` by placing untouched struct fields in `F`. -/
theorem placedOk_of_imp_frame {α β : Type} {prog : Program} {entry : BitVec 64}
    {specField : Spec α} {specFull : Spec β}
    (hField : subroutine_ok prog entry specField)
    (h_exit : ∀ (g : α) (code : BitVec 64) (s0 sf : State),
      specField.onExit g code s0 sf = ⌜False⌝)
    (h_panic : ∀ (g : α) (x : β) (s0 sf : State) (F R : SepProp),
      (sf.mem ⊨ specField.onPanic g s0 sf ∗ (F ∗ R)) →
      (sf.mem ⊨ specFull.onPanic x s0 sf ∗ R))
    (h_step : ∀ (x : β) (s0 : State) (R : SepProp),
      (s0.mem ⊨ specFull.pre x s0 ∗ R) →
      ∃ (g : α) (F : SepProp),
        (s0.mem ⊨ specField.pre g s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ specField.post g s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specFull.post x s0 sf ∗ R)))
    (h_oom : ∀ (g : α) (s0 sf : State), specField.onOom g s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry specFull := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨g, F, hpre', hpost_imp⟩ := h_step x s0 R hpre
  refine hField.mono_outcome g (F ∗ R) s0 hpc hrun hpre' hal fun sf h_out => ?_
  rcases h_out with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanic⟩ | ⟨code, _, hexit⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost_imp sf hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, h_panic g x s0 sf F R hpanic⟩)
  · rw [h_exit g code s0 sf, satisfies_pure_sepConj] at hexit
    exact False.elim hexit.1
  · rw [h_oom g s0 sf, satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

end Symbolic.Swarm.TRREF.B3DeserQ
