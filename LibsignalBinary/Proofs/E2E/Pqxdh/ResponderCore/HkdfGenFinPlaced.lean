/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable Long-IKM `Hkdf::extract` (Block `54`)

Proves `extract_none_long_placed_runsToE_of_inv` and `extract_none_long_placed_ro_runsToE` for
`GenericHkdf<Hmac<Sha256>>::extract` (Block `54`) under `[LibsignalPlacement]` when `x.salt = none`
and `x.ikm.length ∈ {160, 192, 224}`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet
open FinalizeFixedProof

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

local macro "fin_reg_ext" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

@[simp, arm64_norm]
theorem extPlacedFakeB_off_308 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 308) =
      (blkPl_54).base + 308#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

/-! ## Placed Cut Predicates for Long-IKM `extract` -/

def ENfs1LongPlaced [LibsignalPlacement] (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64)
    (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = lsmpl.base 114 ∧
  s.readReg64 .lr = (blkPl_54).base + 80#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = Extract.saltPtrOf sp0 x ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.readBytes (Extract.saltPtrOf sp0 x) 32 = effectiveSalt x.salt

def ECompLongPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = lsρ lsCompress256Sym ∧
  s.readReg64 .lr = (blkPl_54).base + 308#64 ∧
  s.readReg64 .x0 = sp0 + 0x40#64 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length / 64) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EMemcpyLongPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = lsρ lsMemcpySym ∧
  s.readReg64 .lr = (blkPl_54).base + 328#64 ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 (x.ikm.length % 64) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 =
    shaStateBytes ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl F
      (hmacInnerInit F (effectiveSalt x.salt))) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EFinLongPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = (blkPl_123).base ∧
  s.readReg64 .lr = (blkPl_54).base + 380#64 ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem (sp0 + 176#64) F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

/-! ## Segment Proofs on Block `54` -/

section LongExtractPlaced

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

set_option maxHeartbeats 3200000 in
theorem seg0_long_placed_runsTo {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = (blkPl_54).base)
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s0 (ENfs1LongPlaced x s0 sp0) := by
  iterate 20 s2_step
  refine RunsTo.refl ?_
  have hsaved : Extract.ExtSaved s0 sp0
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) :=
    { h29 := by simp (config := { decide := true }) only [arm64_norm]
      hlr := by simp (config := { decide := true }) only [arm64_norm]
      h28 := by simp (config := { decide := true }) only [arm64_norm]
      h26 := by simp (config := { decide := true }) only [arm64_norm]
      h25 := by simp (config := { decide := true }) only [arm64_norm]
      h24 := by simp (config := { decide := true }) only [arm64_norm]
      h23 := by simp (config := { decide := true }) only [arm64_norm]
      h22 := by simp (config := { decide := true }) only [arm64_norm]
      h21 := by simp (config := { decide := true }) only [arm64_norm]
      h20 := by simp (config := { decide := true }) only [arm64_norm]
      h19 := by simp (config := { decide := true }) only [arm64_norm] }
  have hag : AgreesOutside s0.mem
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) sp0 432 := by
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide))
  have hframe : Extract.ExtFrame s0 sp0 _ :=
    Extract.ExtFrame.of_agreesOutside_sp0 (n := 432) (Extract.S2Frame.refl _ _) (by decide) hag
  unfold ENfs1LongPlaced
  refine ⟨⟨hstat, rfl, rfl, rfl, rfl, hsaved, hframe⟩,
    rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp [Extract.saltPtrOf, hsalt, hx1, hsaltA]
  · simp [hx1, hsaltA]
  · rw [Extract.saltPtrOf, effectiveSalt, hsalt]
    dsimp only [Option.map, Option.getD, State.setMem]
    refine Extract.readBytes_32_zero_of_read64_zero ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]

theorem nfs1_long_placed_runsTo {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hInv : Inv s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_salt : RW s0.mem (Extract.saltPtrOf sp0 x) 32)
    (hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hd_salt_176 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1LongPlaced x s0 sp0 s) :
    Extract.RunsToE ((blkPC_54).rebase (blkPl_54).base H) s
      (ERet1Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := Extract.nfs32_runsTo_placed hNfs hInv
    hpc hstat hx0 hx1 hx2
    (Extract.effectiveSalt_length x.salt)
    hsalt_mem
    (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_544.2))
    hd_salt_176.symm
    (by rw [hsp]; exact (Extract.disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Extract.disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) := by
    rw [hlr, extPlacedFakeB_off_80]
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (Extract.CallingConventionPreserved.x19 hcs).trans hx19,
    (Extract.CallingConventionPreserved.x27 hcs).trans hx27,
    (Extract.CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (Extract.CallingConventionPreserved.x20 hcs).trans hx20,
    (Extract.CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

theorem seg1a_long_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1Long extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ECompLongPlaced C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hpos : s.mem.read8 (sp0 + 247#64) = 0#8 := by
    have heq : sp0 + 247#64 = (sp0 + 184#64) + 0x3f#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.1
  have hcnt1 : s.mem.read64 (sp0 + 280#64) = 1#64 := by
    have heq : sp0 + 280#64 = (sp0 + 184#64) + 0x60#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.2.2.1
  have hcnt2 : s.mem.read64 (sp0 + 320#64) = 1#64 := by
    have heq : sp0 + 320#64 = (sp0 + 184#64) + 0x88#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.2.2.2.2
  rcases hikm_len with hlen | hlen | hlen <;> {
    rw [hlen] at hx21
    iterate 35 s2_step
    refine RunsTo.refl ?_
    unfold ECompLongPlaced
    rw [hlen]
    refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
      by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext,
      by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, ?_, ?_, ?_, ?_⟩
    · dsimp only [State.setMem]
      refine Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
      repeat' (first
        | with_reducible exact AgreesOutside.rfl' _ _ _
        | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide)
        | with_reducible refine Extract.agreesOutside_sp0_write64_zero ?_ (by decide))
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt1]
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt2]
  }

theorem seg1b1_long_placed_runsTo [HkdfPlacedHooks C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyLongPlaced C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hx22, hx24, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hblk_s : s.mem.readBytes x.ikmA (64 * (x.ikm.length / 64)) =
      x.ikm.take (64 * (x.ikm.length / 64)) := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
    simpa using h
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_40 : s.mem.RW (sp0 + 0x40#64) 32 :=
    hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length / 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_compress256_multi_step_placed C H
    hstat hpc hx0 hx1 hx2_nat hlr hist hblk_s hrw_sp0_40 ?_
  generalize hist_def : shaStateBytes
    ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl C.F
      (hmacInnerInit C.F (effectiveSalt x.salt))) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (sp0 + 0x40#64) ist') sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [hist'_len]; bv_omega)
  have hrw_sp0_1 : (s.mem.writeBytes (sp0 + 0x40#64) ist').RW sp0 432 :=
    rw_of_perm_eq hag_comp.2 hrw_sp0_s
  iterate 5 s2_step
  refine RunsTo.refl ?_
  have hnrem_8 : BitVec.truncate 8 (BitVec.ofNat 64 (x.ikm.length % 64)) =
      BitVec.ofNat 8 (x.ikm.length % 64) := by
    rcases hikm_len with hlen | hlen | hlen <;> (rw [hlen]; rfl)
  have hag_w8 : AgreesOutside s.mem
      ((s.mem.writeBytes (sp0 + 0x40#64) ist').write8 (sp0 + 63#64)
        (BitVec.ofNat 8 (x.ikm.length % 64))) sp0 328 :=
    Extract.agreesOutside_sp0_write8 hag_comp (by decide)
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]
    exact hcnt1
  have hm := HmacStGen.of_comp_write8 (nrem := x.ikm.length % 64) hcnt1' hout hcnt2
  rw [hblk_len, Nat.mul_div_cancel_left _ (by decide), hist_def] at hm
  unfold EMemcpyLongPlaced Extract.ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_true, ite_false]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  rw [hnrem_8]
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29,
    Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_w8⟩,
    rfl, trivial, trivial, trivial, trivial, hx22, hm.1, hm.2.1.trans hist_def.symm,
    hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩

theorem seg1b2_long_placed_runsTo [HkdfPlacedHooks C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hs : EMemcpyLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hrem_len : (x.ikm.drop (64 * (x.ikm.length / 64))).length = x.ikm.length % 64 := by
    simp; omega
  have hrem_s : s.mem.readBytes
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) =
      x.ikm.drop (64 * (x.ikm.length / 64)) := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    have htake : (x.ikm.drop (64 * (x.ikm.length / 64))).take (x.ikm.length % 64) =
        x.ikm.drop (64 * (x.ikm.length / 64)) :=
      List.take_of_length_le (by simp; omega)
    exact h.trans htake
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_nrem : s.mem.RW sp0 (x.ikm.length % 64) :=
    hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length % 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_memcpy_step_placed C H
    hstat hpc hx0 hx1 hx2_nat hlr hrem_s hrw_sp0_nrem ?_
  refine RunsTo.refl ?_
  have hag_mc : AgreesOutside s.mem
      (s.mem.writeBytes sp0 (x.ikm.drop (64 * (x.ikm.length / 64)))) sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [BitVec.sub_self, hrem_len]; bv_omega)
  unfold EC88Long Extract.ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_mc⟩,
    rfl, hx22, ?_⟩
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]
    exact hcnt1
  have hpos' : s.mem.read8 (sp0 + 0x3f#64) =
      BitVec.ofNat 8 (x.ikm.drop (64 * (x.ikm.length / 64))).length := by
    rw [hrem_len]; exact hpos
  exact HmacStGen.of_memcpy_rem (by rw [hblk_len]; omega) (by rw [hblk_len]; omega)
    (by rw [hrem_len]; omega) hpos' hist hcnt1' hout hcnt2

theorem seg1c_long_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88Long extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EFinLongPlaced C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  unfold EFinLongPlaced
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, hx22, ?_⟩
  · dsimp only [State.setMem]
    refine Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide))
  · refine HmacStGen.of_copy_19 hhm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

theorem fin_long_placed_runsTo [HkdfPlacedHooks C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
      (Extract.ERetFin extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hpre : FinGenPre finPlacedFakeB C.F (effectiveSalt x.salt)
      (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64))) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
      status := hstat
      key_le := by rw [Extract.effectiveSalt_length]; decide
      rem_lt := by simp; omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by
        rw [hx0, hx1]; exact Extract.disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by
        rw [hx0, hsp]; exact (Extract.disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (Extract.disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact Extract.sp0_aligned_0b1111 hsp_al }
  refine (finalize_fixed_gen_placed_runsTo_of_other_block (C := C) (H := H) hcl hpre).mono
    fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0, List.take_append_drop] at hout
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_frame hfr' ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Extract.disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact Extract.disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_triple hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

/-- Relocatable `RunsToE` contract for `extract` (Block `54`) when `x.salt = none` and
`x.ikm.length ∈ {160, 192, 224}`, parameterized by any `KeepsFrozen`-preserved invariant `Inv`
implying `LibsignalCodeLoaded lsmpl`. -/
theorem extract_none_long_placed_runsToE_of_inv [HkdfPlacedHooks C.F H]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hInv0 : Inv s0.mem)
    (hpc : s0.pc = (blkPl_54).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976) :
    Extract.RunsToE ((blkPC_54).rebase (blkPl_54).base H) s0 (Extract.EPost C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := Extract.rw_stk_sub hRW_stk sp0 432 hsub_432
  have hRW_salt : RW s0.mem (Extract.saltPtrOf sp0 x) 32 := by
    rw [Extract.saltPtrOf, hsalt]
    exact Extract.rw_stk_sub hRW_stk _ _ hsub_144.2
  have hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    rw [Extract.saltPtrOf, hsalt]
    exact (Extract.disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
  have hd_salt_176 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    rw [Extract.saltPtrOf, hsalt]
    exact Extract.disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
  have h0 := Extract.RunsTo.toE (seg0_long_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)
  have h1 := Extract.RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_long_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    Extract.RunsTo.toE (seg1a_long_placed_runsTo hRW_stk hikm_len hsp_al hs)
  have h3a := h2.trans fun s hs =>
    Extract.RunsTo.toE
      (seg1b1_long_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h3 := h3a.trans fun s hs =>
    Extract.RunsTo.toE
      (seg1b2_long_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hs)
  have h4 := h3.trans fun s hs =>
    Extract.RunsTo.toE (seg1c_long_placed_runsTo hRW_stk hsp_al hs)
  have h5 := Extract.RunsToE.trans_full h4 fun s hs hkf _ =>
    Extract.RunsTo.toE (fin_long_placed_runsTo (hInv_cl (hInv_kf hInv0 hkf)) hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg2_placed_runsTo hsp_al hs)
  have h7 := Extract.RunsToE.trans_full h6 fun s hs hkf _ =>
    Extract.nfs2_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

end LongExtractPlaced

end CryptoVerification.E2E.Pqxdh.ResponderCore
