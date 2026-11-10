/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step10c
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Decode
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Step `+0x244..+0x0e8` of `TripleRatchet::from_session_state`

Per-block verification of the identity-key extraction and result-assembly segment (`+0x244..+0x0e8`)
of `<TripleRatchet>::from_session_state` (block 57) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
  (missingRemoteIdentitySym rodata_missingRemoteIdentity_placed_intro
   withLsRoLoaded sepWP_seq_lscl_ro lscall_blk_ro)
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem SepWP.intro_lsro_missingRemoteIdentity [LibsignalPlacement] {prog : Program}
    {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsρ missingRemoteIdentitySym) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc at h ⊢
  intro R hm
  have hm' : s.mem ⊨ (((lsρ missingRemoteIdentitySym) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_missingRemoteIdentity_placed_intro hro hm
  exact h R hm'

theorem SepWP.call_dropSpe_placed [LibsignalPlacement] {prog : Program}
    {entry target_pc sp_val : BitVec 64} {A : RustAlloc} {s : State}
    (hsub : subroutine_ok prog entry (withMemEq s.mem (dropSpeSpec A))) (x : DropSpeGhost)
    {P F_frame : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp_val) (hx0 : s.readReg64 .x0 = x.a)
    (hpre : P = (speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt sp_val dropSpeStack) ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf → sf.trace = s.trace →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWP prog target_pc sf (memRegion x.a 48 ∗ A.pool ∗ stackAt sp_val dropSpeStack ∗ F_frame) post) :
    SepWP prog target_pc s P post := by
  apply sepWP_seq_lscl_ro hcl hro (mid := s.readReg64 .lr)
  refine SepWP.call_subroutine_frame hsub (x := x) (F := F_frame) (ret_pc := s.readReg64 .lr)
    hpc hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm1 : s.mem ⊨ ((dropSpeSpec A).pre x s ∗ F_frame) ∗ R := by
      rw [hpre, ← hsp_eq] at hm
      dsimp only [dropSpeSpec]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx0, by simpa only [sepConj_assoc] using hm⟩
    dsimp only [withMemEq]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨rfl, by simpa only [sepConj_assoc] using hm1⟩
  · intro R' sf _ hpan_mem
    unfold withMemEq dropSpeSpec at hpan_mem
    dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem
    exact hpan_mem.1
  · intro R' code sf _ hundef_mem
    unfold withMemEq dropSpeSpec at hundef_mem
    dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem
    exact hundef_mem.1
  · intro sm hpcm hrunm hspm hcsm
    have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    dsimp only [withMemEq, dropSpeSpec]
    rw [hsp_eq, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun htrm => ?_
    refine SepWP.done hpcm hrunm fun hclm hrom => ?_
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hspm hrunm hsp_alignm hcsm htrm hclm hrom)
  · intro R' sf _ hoom_mem
    unfold withMemEq dropSpeSpec at hoom_mem
    dsimp only at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem
    exact False.elim hoom_mem.1

def pkTryFromOkPlacedSpec_from [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (p, bs, pk, out, out33, out34) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out ∧
      PublicKey.deserialize bs = .ok pk ∧ out + 33#64 = out33 ∧ out + 34#64 = out34⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 33 ∗ memRegion out33 1 ∗ memRegion out34 14 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (p, bs, pk, out, out33, out34) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion out33 1 ∗ memRegion out34 14 ∗ (lsLogFilterAddr ↦₆₄ 0#64)

theorem pkTryFrom_placed_ok_at_from [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      pkTryFromOkPlacedSpec_from := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨p, bs, pk, out, out33, out34⟩ R s0 hpre
  simp only [pkTryFromOkPlacedSpec_from, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes, hout33, hout34⟩, hmem⟩
  subst hout33 hout34
  refine ⟨(p, bs, out), memRegion (out + 40#64) 8 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
    rw [ProofLib.memRegion_split' (b := out) (n := 33) (k := 7) (b' := out + 33#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 1) (k := 6) (b' := out + 34#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 34#64) (n := 6) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)] at hmem
    convert hmem using 1; ac_rfl
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOkPlacedSpec_from, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [ProofLib.memRegion_split' (b := out + 34#64) (n := 6) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 1) (k := 6) (b' := out + 34#64)
          rfl (by bv_omega) (by decide)] at hpost
    convert hpost using 1; ac_rfl

theorem speAt_missingRemoteIdentity_sp_160_placed (A : RustAlloc) (sp p : BitVec 64) :
    (((sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
     ((sp - 152#64) ↦₆₄ p) ∗
     ((sp - 144#64) ↦₆₄ 27#64) ∗
     (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
     memRegion (sp - 136#64) 24) ⊢
      speAt A (utf8 "decrypt") (sp - 160#64) (.invalidSessionStructure .missingRemoteIdentity) := by
  have h := speAt_missingRemoteIdentity_intro A (sp - 160#64) p
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem trFrom_step_244_to_428_placed [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (target_pc : BitVec 64) (F_rest : SepProp)
    (post : State → SepProp → Prop)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hlik_split1 : ∀ a : BitVec 64,
      (a ↦ₛ st.localIdentity.publicKey.bytes.toList) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₈ b7) ∗
         ((a + 8#64) ↦₈ b8) ∗
         ((a + 9#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((a + 13#64) ↦₁₆ (b14 ++ b13)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31)))
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length)
    (hrik : match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx21 : s.readReg64 .x21 = G.pq.ptr)
    (hx22 : s.readReg64 .x22 = ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ sm (remBs : List (BitVec 8))
      (rd0 : BitVec 32) (rh4 : BitVec 16) (rw6 rw14 rw22 : BitVec 64) (rh30 : BitVec 16)
      (u_232 : BitVec 32) (u_228 : BitVec 16) (u_208 : BitVec 32),
      remBs.length = 32 →
      (∀ ik, st.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList) →
      (∀ a : BitVec 64, (a ↦ₛ remBs) =
        ((a ↦₃₂ rd0) ∗ ((a + 4#64) ↦₁₆ rh4) ∗ ((a + 6#64) ↦₆₄ rw6) ∗
         ((a + 14#64) ↦₆₄ rw14) ∗ ((a + 22#64) ↦₆₄ rw22) ∗ ((a + 30#64) ↦₁₆ rh30))) →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.pc = (blkPl_57).base + 1064#64 →
      sm.status = .Running → sm.trace = s0.trace →
      sm.readReg64 .x8 = lsρ missingRemoteIdentitySym →
      sm.readReg64 .x9 = 27#64 →
      sm.readReg64 .x10 = (remoteIdentityTag st.remoteIdentity).zeroExtend 64 →
      sm.readReg64 .x11 = rw14 →
      sm.readReg64 .x12 = rw6 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 →
      sm.readReg64 .x22 = s0.sp - 160#64 →
      sm.readReg64 .x23 = 0x8000000000000014#64 →
      sm.readReg64 .x24 = s0.sp - 184#64 →
      sm.readReg64 .x25 = b7.zeroExtend 64 →
      sm.readReg64 .x26 = (b12 ++ b11 ++ b10 ++ b9).zeroExtend 64 →
      sm.readReg64 .x27 = (b14 ++ b13).zeroExtend 64 →
      sm.readReg64 .x28 = b8.zeroExtend 64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.sp = s0.sp - 496#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc sm
        ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
         vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
         memRegion (s0.sp - 496#64) 8 ∗
         ((s0.sp - 488#64) ↦₃₂ (b5 ++ b4).zeroExtend 32) ∗
         ((s0.sp - 484#64) ↦₃₂ b6.zeroExtend 32) ∗
         ((s0.sp - 480#64) ↦₆₄ w15) ∗
         ((s0.sp - 472#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
         ((s0.sp - 464#64) ↦₆₄ G.pq.ptr) ∗
         ((s0.sp - 280#64) ↦₆₄ w23) ∗
         ((s0.sp - 272#64) ↦₈ b31) ∗
         memRegion (s0.sp - 271#64) 7 ∗
         ((s0.sp - 264#64) ↦₃₂ rd0) ∗
         ((s0.sp - 260#64) ↦₁₆ rh4) ∗
         memRegion (s0.sp - 258#64) 26 ∗
         ((s0.sp - 232#64) ↦₃₂ u_232) ∗
         ((s0.sp - 228#64) ↦₁₆ u_228) ∗
         memRegion (s0.sp - 226#64) 18 ∗
         ((s0.sp - 208#64) ↦₃₂ u_208) ∗
         memRegion (s0.sp - 204#64) 20 ∗
         ((s0.sp - 184#64) ↦₆₄ rw22) ∗
         ((s0.sp - 176#64) ↦₁₆ rh30) ∗
         memRegion (s0.sp - 174#64) 14 ∗
         ((s0.sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
         ((s0.sp - 152#64) ↦₆₄ (lsρ missingRemoteIdentitySym)) ∗
         ((s0.sp - 144#64) ↦₆₄ 27#64) ∗
         ((s0.sp - 136#64) ↦₆₄ rw22) ∗
         ((s0.sp - 128#64) ↦₁₆ rh30) ∗
         memRegion (s0.sp - 126#64) 14 ∗
         memRegion (s0.sp - 112#64) 16 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         F_rest)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc s
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 280#64) 184 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       F_rest)
      post := by
  have hpkTryFrom := pkTryFrom_placed_ok_at_from H
  apply sepWP_seq_lscl_ro hcl hro (mid := (blkPl_57).base + 1064#64)
  apply sepWP_seq_lscl_ro hcl hro (mid := lsmpl.base 29)
  rw [stack_496_40_split s0.sp, stack_280_184_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u_176 => SepWP.exists_elim fun u_184 => ?_
  refine SepWP.exists_elim fun u_208 => SepWP.exists_elim fun u_228 => ?_
  refine SepWP.exists_elim fun u_232 => SepWP.exists_elim fun u_260 => ?_
  refine SepWP.exists_elim fun u_264 => SepWP.exists_elim fun u_272 => ?_
  refine SepWP.exists_elim fun u_280 => SepWP.exists_elim fun u_464 => ?_
  refine SepWP.exists_elim fun u_472 => SepWP.exists_elim fun u_480 => ?_
  refine SepWP.exists_elim fun u_484 => SepWP.exists_elim fun u_488 => ?_
  wp_steps
  wp_call (lscall_blk (callerProg := (blkPC_57).rebase (blkPl_57).base H)
    (spec := pkTryFromOkPlacedSpec_from) hpkTryFrom hcl)
    (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey,
     s0.sp - 160#64, s0.sp - 127#64, s0.sp - 126#64)
  have hsub159 : s0.sp - 160#64 + 1#64 = s0.sp - 159#64 := by bv_omega
  rw [lik_unpack_stack s0.sp hlik_split1]
  simp only [sepConj_assoc]
  have hcmp_ok : (0#8 == 1#8) = false := by decide
  wp_steps
  have hlen_lik : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  have hmr34 :
      (((s0.sp - 160#64) ↦₈ 0#8) ∗
       ((s0.sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((s0.sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
       ((s0.sp - 153#64) ↦₈ b6) ∗
       ((s0.sp - 152#64) ↦₈ b7) ∗
       ((s0.sp - 151#64) ↦₈ b8) ∗
       ((s0.sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
       ((s0.sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
       ((s0.sp - 144#64) ↦₆₄ w15) ∗
       ((s0.sp - 136#64) ↦₆₄ w23) ∗
       ((s0.sp - 128#64) ↦₈ b31) ∗
       memRegion (s0.sp - 127#64) 1) ⊢
      memRegion (s0.sp - 160#64) 34 := by
    have hpack :
        (((s0.sp - 160#64) ↦₈ 0#8) ∗
         ((s0.sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((s0.sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
         ((s0.sp - 153#64) ↦₈ b6) ∗
         ((s0.sp - 152#64) ↦₈ b7) ∗
         ((s0.sp - 151#64) ↦₈ b8) ∗
         ((s0.sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((s0.sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
         ((s0.sp - 144#64) ↦₆₄ w15) ∗
         ((s0.sp - 136#64) ↦₆₄ w23) ∗
         ((s0.sp - 128#64) ↦₈ b31) ∗
         memRegion (s0.sp - 127#64) 1) =
        (((s0.sp - 160#64) ↦₈ 0#8) ∗
         ((s0.sp - 159#64) ↦ₛ st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (s0.sp - 127#64) 1) := by
      rw [lik_unpack_stack s0.sp hlik_split1]
      simp only [sepConj_assoc]
    rw [hpack]
    have hsub127 : s0.sp - 160#64 + 33#64 = s0.sp - 127#64 := by bv_omega
    have h := memRegion_34_of_tag_32_1 (s0.sp - 160#64) 0#8
      st.localIdentity.publicKey.bytes.toList hlen_lik
    rwa [hsub159, hsub127] at h
  refine SepWP.fold hmr34 (by sep_focus) ?_
  rw [stackAt_dropVecChain_eq_remoteIdentityKey s0.sp]
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_rem _hro_rem
  wp_call (lscall_blk_cl (callerProg := (blkPC_57).rebase (blkPl_57).base H)
    (spec := remoteIdentityKeyPlacedSpec A) hRemoteIk hcl_rem)
    ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 160#64⟩
  simp only [arm64_norm, *]
  have hstack_fold :
      (memRegion (s0.sp - 4688#64) 4048 ∗ stackAt (s0.sp - 496#64) remoteIdentityKeyStack) ⊢
        stackAt (s0.sp - 496#64) dropVecChainStack :=
    Entails.of_eq (stackAt_dropVecChain_eq_remoteIdentityKey s0.sp).symm
  refine SepWP.fold hstack_fold (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_unified (s0.sp - 160#64) st.remoteIdentity) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun remBs => ?_
  refine SepWP.pure_elim fun ⟨hrem_len, hrem_eq⟩ => ?_
  obtain ⟨rd0, rh4, rw6, rw14, rw22, rh30, hrem_split⟩ :=
    exists_remoteIk_split_of_length_32 hrem_len
  have hsub158 : s0.sp - 160#64 + 2#64 = s0.sp - 158#64 := by bv_omega
  rw [hsub159, hsub158, rem_unpack_stack s0.sp hrem_split]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_sp_160 s0.sp 0#8 (remoteIdentityTag st.remoteIdentity) rd0 rh4))
    (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_m hro_m
  refine SepWP.mono_pre (by exact Entails.of_eq (by ac_rfl))
    (hcont _ remBs rd0 rh4 rw6 rw14 rw22 rh30 u_232 u_228 u_208
      hrem_len hrem_eq hrem_split hcl_m hro_m
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

theorem trFrom_step_378_to_0e8_placed [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A)))
    (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (senderPad : List (BitVec 8))
    (s0 sm : State) (target_pc : BitVec 64) (F_cs : SepProp)
    (post : State → SepProp → Prop)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {remBs : List (BitVec 8)}
    {rd0 : BitVec 32} {rh4 : BitVec 16} {rw6 rw14 rw22 : BitVec 64} {rh30 : BitVec 16}
    {u_232 : BitVec 32} {u_228 : BitVec 16} {u_208 u_284 : BitVec 32}
    {sc0 sc1 sc2 sc3 sc4 sc5 sc6 sc7 sc8 sc9 sc10 sc11 sc12 : BitVec 64}
    {rk0 rk1 rk2 rk3 : BitVec 64}
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpq_ne : G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_split2 : ∀ a : BitVec 64,
      (a ↦ₛ st.localIdentity.publicKey.bytes.toList) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31)))
    (hsc_split : ∀ a : BitVec 64, (a ↦ₛ optSenderChainBytes st.senderChain senderPad) =
      ((a ↦₆₄ sc0) ∗ ((a + 8#64) ↦₆₄ sc1) ∗ ((a + 16#64) ↦₆₄ sc2) ∗
       ((a + 24#64) ↦₆₄ sc3) ∗ ((a + 32#64) ↦₆₄ sc4) ∗ ((a + 40#64) ↦₆₄ sc5) ∗
       ((a + 48#64) ↦₆₄ sc6) ∗ ((a + 56#64) ↦₆₄ sc7) ∗ ((a + 64#64) ↦₆₄ sc8) ∗
       ((a + 72#64) ↦₆₄ sc9) ∗ ((a + 80#64) ↦₆₄ sc10) ∗ ((a + 88#64) ↦₆₄ sc11) ∗
       ((a + 96#64) ↦₆₄ sc12)))
    (hrk_split : ∀ a : BitVec 64, (a ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) =
      ((a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)))
    (hrem_eq : ∀ ik, st.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList)
    (hrem_split : ∀ a : BitVec 64, (a ↦ₛ remBs) =
      ((a ↦₃₂ rd0) ∗ ((a + 4#64) ↦₁₆ rh4) ∗ ((a + 6#64) ↦₆₄ rw6) ∗
       ((a + 14#64) ↦₆₄ rw14) ∗ ((a + 22#64) ↦₆₄ rw22) ∗ ((a + 30#64) ↦₁₆ rh30)))
    (hcl : LibsignalCodeLoaded lsmpl sm.mem) (hro : LibsignalRoLoaded lsmpl sm.mem)
    (hpc : sm.pc = (blkPl_57).base + 1064#64)
    (hrun : sm.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : sm.trace = s0.trace)
    (_hx8 : sm.readReg64 .x8 = lsρ missingRemoteIdentitySym)
    (_hx9 : sm.readReg64 .x9 = 27#64)
    (hx10 : sm.readReg64 .x10 = (remoteIdentityTag st.remoteIdentity).zeroExtend 64)
    (hx11 : sm.readReg64 .x11 = rw14)
    (hx12 : sm.readReg64 .x12 = rw6)
    (hx19 : sm.readReg64 .x19 = ret)
    (hx20 : sm.readReg64 .x20 = G.pq.cap)
    (hx21 : sm.readReg64 .x21 = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64)
    (hx22 : sm.readReg64 .x22 = s0.sp - 160#64)
    (hx23 : sm.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : sm.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : sm.readReg64 .x25 = b7.zeroExtend 64)
    (hx26 : sm.readReg64 .x26 = (b12 ++ b11 ++ b10 ++ b9).zeroExtend 64)
    (hx27 : sm.readReg64 .x27 = (b14 ++ b13).zeroExtend 64)
    (hx28 : sm.readReg64 .x28 = b8.zeroExtend 64)
    (hx29 : sm.readReg64 .x29 = s0.sp - 96#64)
    (hsp : sm.sp = s0.sp - 496#64)
    (hcont : ∀ sf,
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      sf.pc = (blkPl_57).base + 232#64 →
      sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp - 496#64 →
      calleeSavedVRegs sf = calleeSavedVRegs sm →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc sf
        (A.pool ∗
         trResultAt A ret G
           (match st.remoteIdentity with
            | some rem =>
              .ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
                    st.previousCounter, maxForwardJumps⟩,
                   st.pqRatchetState, st.localIdentity, rem⟩
            | none => .error (.invalidSessionStructure .missingRemoteIdentity)) ∗
         sessionStateAt A ss G.afterTrFrom
           { st with receiverChains := [], pqRatchetState := [] } ∗
         memRegion (s0.sp - 496#64) 400 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         F_cs)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc sm
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 8 ∗
       ((s0.sp - 488#64) ↦₃₂ (b5 ++ b4).zeroExtend 32) ∗
       ((s0.sp - 484#64) ↦₃₂ b6.zeroExtend 32) ∗
       ((s0.sp - 480#64) ↦₆₄ w15) ∗
       ((s0.sp - 472#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
       ((s0.sp - 464#64) ↦₆₄ G.pq.ptr) ∗
       ((s0.sp - 280#64) ↦₆₄ w23) ∗
       ((s0.sp - 272#64) ↦₈ b31) ∗
       memRegion (s0.sp - 271#64) 7 ∗
       ((s0.sp - 264#64) ↦₃₂ rd0) ∗
       ((s0.sp - 260#64) ↦₁₆ rh4) ∗
       memRegion (s0.sp - 258#64) 26 ∗
       ((s0.sp - 232#64) ↦₃₂ u_232) ∗
       ((s0.sp - 228#64) ↦₁₆ u_228) ∗
       memRegion (s0.sp - 226#64) 18 ∗
       ((s0.sp - 208#64) ↦₃₂ u_208) ∗
       memRegion (s0.sp - 204#64) 20 ∗
       ((s0.sp - 184#64) ↦₆₄ rw22) ∗
       ((s0.sp - 176#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 174#64) 14 ∗
       ((s0.sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
       ((s0.sp - 152#64) ↦₆₄ (lsρ missingRemoteIdentitySym)) ∗
       ((s0.sp - 144#64) ↦₆₄ 27#64) ∗
       ((s0.sp - 136#64) ↦₆₄ rw22) ∗
       ((s0.sp - 128#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 126#64) 14 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       (A.pool ∗
        ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
        ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
        ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
        ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
        ((s0.sp - 284#64) ↦₃₂ u_284) ∗
        memRegion ret 264 ∗
        sessionAfter208Frame A ss G st ∗
        F_cs))
      post := by
  have hsc_len : (optSenderChainBytes st.senderChain senderPad).length = 104 :=
    optSenderChainBytes_length st.senderChain hpad
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 st.rootKey).length = 32 :=
    length_keyToBytes32 st.rootKey
  apply sepWP_seq_lscl_ro hcl hro (mid := (blkPl_57).base + bv% (232))
  refine SepWP.fold (sessionStateAt_reassemble_after208 A ss G st hlik) (by sep_focus) ?_
  generalize hS_post :
    sessionStateAt A ss G.afterTrFrom { st with receiverChains := [], pqRatchetState := [] } = S_post at *
  cases hrem : st.remoteIdentity with
  | some rem =>
    have hrem_bs : remBs = rem.publicKey.bytes.toList := hrem_eq rem hrem
    subst hrem_bs
    dsimp only [remoteIdentityTag] at hx10
    refine SepWP.intro_lsro_missingRemoteIdentity hro ?_
    refine SepWP.fold (memRegion_24_of_8_2_14 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold (speAt_missingRemoteIdentity_sp_160_placed A s0.sp (lsρ missingRemoteIdentitySym)) (by sep_focus) ?_
    rw [stackAt_dropVecChain_eq_dropSpe s0.sp]
    apply sepWP_seq_lscl_ro hcl hro (mid := lsmpl.base 5)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_454 hro_454
    refine SepWP.call_dropSpe_placed (sp_val := s0.sp - 496#64)
      (lscall_blk_ro (callerProg := (blkPC_57).rebase (blkPl_57).base H)
        (spec := dropSpeSpec A) hDropSpe hcl_454 hro_454)
      ⟨s0.sp - 160#64, utf8 "decrypt", .invalidSessionStructure .missingRemoteIdentity⟩
      hcl_454 hro_454 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro s_458 hpc_458 hsp_458 hrun_458 _ hcs_458 htr_458 hcl_458 hro_458
    rcases hcs_458 with ⟨hx19_458, hx20_458, hx21_458, hx22_458, hx23_458, hx24_458,
      hx25_458, hx26_458, hx27_458, hx28_458, hx29_458, hvregs_458⟩
    simp only [arm64_norm, hsp, hx19, hx20, hx25, hx26, hx27, hx28, hx29] at hpc_458 hsp_458 hx19_458 hx20_458 hx21_458 hx22_458 hx23_458 hx24_458 hx25_458 hx26_458 hx27_458 hx28_458 hx29_458 hvregs_458
    have hstack_dropSpe_fold :
        (memRegion (s0.sp - 4688#64) 64 ∗ stackAt (s0.sp - 496#64) dropSpeStack) ⊢
          stackAt (s0.sp - 496#64) dropVecChainStack :=
      Entails.of_eq (stackAt_dropVecChain_eq_dropSpe s0.sp).symm
    refine SepWP.fold hstack_dropSpe_fold (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion ret 264)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion (s0.sp - 160#64) 48)) (by sep_focus) ?_
    rw [memRegion_48_split_8_2_38 s0.sp,
        sc_unpack_stack s0.sp hsc_split,
        rk_unpack_stack s0.sp hrk_split,
        ret_264_split_some ret,
        ret_200_split_lik ret,
        ret_232_split_rem ret]
    simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun u_152 => SepWP.exists_elim fun u_160 => ?_
    refine SepWP.exists_elim fun m30 => SepWP.exists_elim fun m22 => ?_
    refine SepWP.exists_elim fun m14 => SepWP.exists_elim fun m6 => ?_
    refine SepWP.exists_elim fun m4 => SepWP.exists_elim fun m0 => ?_
    refine SepWP.exists_elim fun l31 => SepWP.exists_elim fun l23 => ?_
    refine SepWP.exists_elim fun l15 => SepWP.exists_elim fun l7 => ?_
    refine SepWP.exists_elim fun l6 => SepWP.exists_elim fun l4 => ?_
    refine SepWP.exists_elim fun l0 => SepWP.exists_elim fun w24 => ?_
    refine SepWP.exists_elim fun w23_r => SepWP.exists_elim fun w22_r => ?_
    refine SepWP.exists_elim fun w21_r => SepWP.exists_elim fun w20_r => ?_
    refine SepWP.exists_elim fun w19_r => SepWP.exists_elim fun w18_r => ?_
    refine SepWP.exists_elim fun w17_r => SepWP.exists_elim fun w16_r => ?_
    refine SepWP.exists_elim fun w15_r => SepWP.exists_elim fun w14_r => ?_
    refine SepWP.exists_elim fun w13_r => SepWP.exists_elim fun w12_r => ?_
    refine SepWP.exists_elim fun w11_r => SepWP.exists_elim fun w10_r => ?_
    refine SepWP.exists_elim fun w9_r => SepWP.exists_elim fun w8_r => ?_
    refine SepWP.exists_elim fun w7_r => SepWP.exists_elim fun w6_r => ?_
    refine SepWP.exists_elim fun w5_r => SepWP.exists_elim fun w4_r => ?_
    refine SepWP.exists_elim fun w3_r => SepWP.exists_elim fun w2_r => ?_
    refine SepWP.exists_elim fun w1_r => SepWP.exists_elim fun w0_r => ?_
    wp_steps
    refine SepWP.fold (sc_pack_stack s0.sp hsc_split) (by sep_focus) ?_
    refine SepWP.fold (sc_pack_ret ret hsc_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_stack s0.sp hrk_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_ret ret hrk_split) (by sep_focus) ?_
    refine SepWP.fold (lik_pack_ret ret hlik_split2) (by sep_focus) ?_
    refine SepWP.fold (rem_pack_ret ret hrem_split) (by sep_focus) ?_
    refine SepWP.fold (ret_168_split_prev ret st.previousCounter u_284) (by sep_focus) ?_
    refine SepWP.fold (trResultAt_ok_intro A ret G st rem senderPad hclamp hchains hpad) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284).symm) (by sep_focus) ?_
    refine SepWP.fold (memRegion_48_of_8_2_38 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_280_184_fold s0.sp w23 b31 rd0 rh4 u_232 u_228 u_208 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
        w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
    refine SepWP.fold
      (memRegion_24_of_8_8_8 s0.sp G.chainsCap G.chainsPtr
        (BitVec.ofNat 64 st.receiverChains.length)) (by sep_focus) ?_
    refine SepWP.fold
      (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
        (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
        25000#64 st.previousCounter u_284) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_f hro_f
    have hcont' := hcont _ hcl_f hro_f
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    rw [hrem] at hcont'
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'
  | none =>
    apply sepWP_seq_lscl_ro hcl hro (mid := lsmpl.base 2)
    dsimp only [remoteIdentityTag] at hx10
    refine SepWP.intro_lsro_missingRemoteIdentity hro ?_
    obtain ⟨ed0, eh4, ew6, ew14, eh22, herr_split, herr_ret⟩ :=
      exists_err22_split (lsρ missingRemoteIdentitySym) rw22
    refine SepWP.fold (err22_unpack_stack s0.sp (lsρ missingRemoteIdentitySym) rw22 herr_split) (by sep_focus) ?_
    rw [ret_264_split_none ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun r38 => SepWP.exists_elim fun r30 => ?_
    refine SepWP.exists_elim fun r22 => SepWP.exists_elim fun r20 => ?_
    refine SepWP.exists_elim fun r16 => SepWP.exists_elim fun r8 => ?_
    refine SepWP.exists_elim fun r0 => ?_
    wp_steps
    refine SepWP.fold (err22_pack_stack s0.sp (lsρ missingRemoteIdentitySym) rw22 herr_split) (by sep_focus) ?_
    refine SepWP.fold (err22_pack_ret ret (lsρ missingRemoteIdentitySym) herr_ret r38) (by sep_focus) ?_
    refine SepWP.fold
      (trResultAt_err_missingRemoteIdentity_intro A ret G (lsρ missingRemoteIdentitySym)) (by sep_focus) ?_
    refine SepWP.fold
      (memRegion_48_of_8_8_8_8_2_14 s0.sp 0x8000000000000014#64
        (lsρ missingRemoteIdentitySym) 27#64 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_280_184_fold s0.sp w23 b31 rd0 rh4 ed0 eh4 ed0 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
        w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
    refine SepWP.fold (vecAt_chains_stack_fold A s0.sp G st hchains) (by sep_focus) ?_
    by_cases hpq0 : G.pq.cap = 0
    · rw [hpq0] at hx20
      refine SepWP.fold
        (vecU8Buf_zero_entails_emp A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      simp only [emp_sepConj, hpq0, show ((0 : BitVec 64) == 0#64) = true from rfl, not_true_eq_false, ↓reduceIte]
      rw [← hsp]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_dc _hro_dc
      wp_call (lscall_blk_cl (callerProg := (blkPC_57).rebase (blkPl_57).base H)
        (spec := dropVecChainSpec A) hDropVecChain hcl_dc)
        ⟨s0.sp - 456#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
      rw [hsp]
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_f hro_f
      have hcont' := hcont _ hcl_f hro_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'
    · have hpq_beq_false : (G.pq.cap == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; exact hpq0
      simp only [hpq_beq_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      obtain ⟨hpq_pos, hpq_lt, hpq_ptr⟩ := hpq_ne hpq0
      refine SepWP.fold
        (vecU8Buf_entails_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      simp only [sepConj_assoc]
      rw [stackAt_dropVecChain_eq_allocHook s0.sp, ← hsp]
      wp_steps
      wp_apply
      rw [hsp]
      have hstack_dealloc_fold :
          (memRegion (s0.sp - 4688#64) 96 ∗ stackAt (s0.sp - 496#64) allocHookStack) ⊢
            stackAt (s0.sp - 496#64) dropVecChainStack :=
        Entails.of_eq (stackAt_dropVecChain_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_dealloc_fold (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_dc _hro_dc
      wp_call (lscall_blk_cl (callerProg := (blkPC_57).rebase (blkPl_57).base H)
        (spec := dropVecChainSpec A) hDropVecChain hcl_dc)
        ⟨s0.sp - 456#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
      rw [hsp_sf, hsp]
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_f hro_f
      have hcont' := hcont _ hcl_f hro_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'

theorem trFrom_step_244_to_0e8_placed [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A)))
    (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (senderPad : List (BitVec 8))
    (s0 s : State) (target_pc : BitVec 64) (F_cs : SepProp)
    (post : State → SepProp → Prop)
    {u_284 : BitVec 32}
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpq_ne : G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length)
    (hrik : match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = G.pq.cap)
    (hx21 : s.readReg64 .x21 = G.pq.ptr)
    (hx22 : s.readReg64 .x22 = ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ sf,
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      sf.pc = (blkPl_57).base + 232#64 →
      sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp - 496#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc sf
        (A.pool ∗
         trResultAt A ret G
           (match st.remoteIdentity with
            | some rem =>
              .ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
                    st.previousCounter, maxForwardJumps⟩,
                   st.pqRatchetState, st.localIdentity, rem⟩
            | none => .error (.invalidSessionStructure .missingRemoteIdentity)) ∗
         sessionStateAt A ss G.afterTrFrom
           { st with receiverChains := [], pqRatchetState := [] } ∗
         memRegion (s0.sp - 496#64) 400 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_cs))
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc s
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 280#64) 184 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       (A.pool ∗
        ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
        ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
        ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
        ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
        ((s0.sp - 284#64) ↦₃₂ u_284) ∗
        memRegion ret 264 ∗
        sessionAfter208Frame A ss G st ∗
        ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_cs)))
      post := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, w15, w23, b31,
    hlik_split1, hlik_split2⟩ :=
    exists_localIk_split_of_length_32 st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨sc0, sc1, sc2, sc3, sc4, sc5, sc6, sc7, sc8, sc9, sc10, sc11, sc12, hsc_split⟩ :=
    exists_unpack64_of_length_104 (optSenderChainBytes_length st.senderChain hpad)
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_split⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 st.rootKey)
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (trFrom_step_244_to_428_placed hRemoteIk ss G st s0 s target_pc
      (A.pool ∗
       ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
       ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
       ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
       vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
       vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
       ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
       ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
       ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion ret 264 ∗
       sessionAfter208Frame A ss G st ∗
       F_cs) post
      hlik_split1 hlik hlik_toNat hrik hcl hro hpc hrun halign htr
      hx0 hx1 hx8 hx21 hx22 hx23 hx24 hx25 hx29 hsp ?_)
  intro sm remBs rd0 rh4 rw6 rw14 rw22 rh30 u_232 u_228 u_208
    _ hrem_eq hrem_split hcl_m hro_m hpc_m hrun_m htr_m
    hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m hvregs_m
  rw [hx19] at hx19_m
  rw [hx20] at hx20_m
  exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (trFrom_step_378_to_0e8_placed hdealloc hDropSpe hDropVecChain ret ss G st senderPad s0 sm target_pc ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_cs) post
      hpad hclamp hchains hpq_ne hlik hlik_split2 hsc_split hrk_split hrem_eq hrem_split
      hcl_m hro_m hpc_m hrun_m halign htr_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
      hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m
      fun sf hcl_f hro_f hpc_f hrun_f htr_f hsp_f hvregs_f =>
        hcont sf hcl_f hro_f hpc_f hrun_f htr_f hsp_f (hvregs_f.trans hvregs_m))

theorem trFrom_step_10c_to_244_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (A : RustAlloc) (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (target_pc : BitVec 64) (F_tail : SepProp)
    (post : State → SepProp → Prop)
    (w_208 : BitVec 64) (b_200 : BitVec 8) (d_192 : BitVec 32) (h_188 : BitVec 16)
    (u_296 : BitVec 64) (u_288 u_284 : BitVec 32)
    {rk_b0 rk_b1 rk_b2 rk_b3 rk_b4 rk_b5 rk_b6 : BitVec 8}
    {rk_w7 rk_w15 rk_w23 : BitVec 64} {rk_b31 : BitVec 8}
    {rx2 rx3 rx4 rx5 rx6 rx8 rx9 rx10 rx11 rx12 rx13 rx14 rx15 rx16 rx17 rx18 : BitVec 64}
    (hrk : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) =
        ((a ↦₈ rk_b0) ∗ ((a + 1#64) ↦₈ rk_b1) ∗ ((a + 2#64) ↦₈ rk_b2) ∗ ((a + 3#64) ↦₈ rk_b3) ∗
         ((a + 4#64) ↦₈ rk_b4) ∗ ((a + 5#64) ↦₈ rk_b5) ∗ ((a + 6#64) ↦₈ rk_b6) ∗
         ((a + 7#64) ↦₆₄ rk_w7) ∗ ((a + 15#64) ↦₆₄ rk_w15) ∗ ((a + 23#64) ↦₆₄ rk_w23) ∗
         ((a + 31#64) ↦₈ rk_b31)))
    (hcmn_chains : (G.chainsCap + 1#64 == 0#64) = false)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 268#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hw1 : (s.readReg64 .x1).setWidth 32 = 0#32)
    (hx2 : s.readReg64 .x2 = rx2)
    (hx3 : s.readReg64 .x3 = rx3)
    (hx4 : s.readReg64 .x4 = rx4)
    (hx5 : s.readReg64 .x5 = rx5)
    (hx6 : s.readReg64 .x6 = rx6)
    (hx8 : s.readReg64 .x8 = rx8)
    (hx9 : s.readReg64 .x9 = rx9)
    (hx10 : s.readReg64 .x10 = rx10)
    (hx11 : s.readReg64 .x11 = rx11)
    (hx12 : s.readReg64 .x12 = rx12)
    (hx13 : s.readReg64 .x13 = rx13)
    (hx14 : s.readReg64 .x14 = rx14)
    (hx15 : s.readReg64 .x15 = rx15)
    (hx16 : s.readReg64 .x16 = rx16)
    (hx17 : s.readReg64 .x17 = rx17)
    (hx18 : s.readReg64 .x18 = rx18)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = s0.sp - 456#64)
    (hx21 : s.readReg64 .x21 = rk_w15)
    (hx22 : s.readReg64 .x22 = rk_w7)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ s_244,
      LibsignalCodeLoaded lsmpl s_244.mem → LibsignalRoLoaded lsmpl s_244.mem →
      s_244.pc = (blkPl_57).base + 580#64 →
      s_244.status = .Running → s_244.trace = s0.trace →
      s_244.readReg64 .x0 = G.localIk.ptr →
      s_244.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length →
      s_244.readReg64 .x8 = s0.sp - 160#64 →
      s_244.readReg64 .x19 = ret →
      s_244.readReg64 .x20 = G.pq.cap →
      s_244.readReg64 .x21 = G.pq.ptr →
      s_244.readReg64 .x22 = ss →
      s_244.readReg64 .x23 = 0x8000000000000014#64 →
      s_244.readReg64 .x24 = s0.sp - 184#64 →
      s_244.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length →
      s_244.readReg64 .x29 = s0.sp - 96#64 →
      s_244.sp = s0.sp - 496#64 →
      calleeSavedVRegs s_244 = calleeSavedVRegs s →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc s_244
        (((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
         scRawCells s0.sp
           rx4 rx5 rx6 rx2 (rx8.setWidth 32)
           (rx3.setWidth 8) d_192 h_188 rx9 rx10 rx11 (rx14.setWidth 8)
           (rx17.setWidth 32) rx18 (rx16.setWidth 16)
           ((((rx16.setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
           (rx13.setWidth 32) ((rx13 >>> 32).setWidth 8)
           (rx15.setWidth 16)
           ((((rx15.setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
           w_208 b_200 (rx12.setWidth 32) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion (s0.sp - 280#64) 184 ∗
         sessionAfter208Frame A ss G st ∗
         F_tail)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) target_pc s
      (memRegion (s0.sp - 456#64) 160 ∗
       ((s0.sp - 296#64) ↦₆₄ u_296) ∗
       ((s0.sp - 288#64) ↦₃₂ u_288) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion (s0.sp - 280#64) 24 ∗
       memRegion (s0.sp - 256#64) 24 ∗
       ((s0.sp - 232#64) ↦₆₄ rk_w23) ∗
       ((s0.sp - 224#64) ↦₈ rk_b31) ∗ memRegion (s0.sp - 223#64) 7 ∗
       ((s0.sp - 216#64) ↦₈ rk_b0) ∗ ((s0.sp - 215#64) ↦₈ rk_b1) ∗
       ((s0.sp - 214#64) ↦₈ rk_b2) ∗ ((s0.sp - 213#64) ↦₈ rk_b3) ∗
       ((s0.sp - 212#64) ↦₈ rk_b4) ∗ ((s0.sp - 211#64) ↦₈ rk_b5) ∗
       ((s0.sp - 210#64) ↦₈ rk_b6) ∗ memRegion (s0.sp - 209#64) 1 ∗
       ((s0.sp - 208#64) ↦₆₄ w_208) ∗
       ((s0.sp - 200#64) ↦₈ b_200) ∗ memRegion (s0.sp - 199#64) 7 ∗
       ((s0.sp - 192#64) ↦₃₂ d_192) ∗ ((s0.sp - 188#64) ↦₁₆ h_188) ∗ memRegion (s0.sp - 186#64) 2 ∗
       memRegion (s0.sp - 184#64) 24 ∗
       ((s0.sp - 160#64) ↦₆₄ G.chainsCap) ∗
       ((s0.sp - 152#64) ↦₆₄ G.chainsPtr) ∗
       ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
       memRegion (s0.sp - 136#64) 16 ∗
       memRegion (s0.sp - 120#64) 24 ∗
       sessionFromBase A ss G st ∗
       (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
       ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
       vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
       ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
       ((ss + 64#64) ↦₆₄ 32#64) ∗
       (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
       ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
       ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
       optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
       ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
       F_tail)
      post := by
  apply sepWP_seq_lscl_ro hcl hro (mid := (blkPl_57).base + bv% (580))
  rw [stack_456_160_split s0.sp, stack_256_24_split s0.sp, stack_184_24_split_10c s0.sp]
  simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun t_176 => SepWP.exists_elim fun t_184 => ?_
  refine SepWP.exists_elim fun t_234 => SepWP.exists_elim fun t_235 => ?_
  refine SepWP.exists_elim fun t_236 => SepWP.exists_elim fun t_237 => ?_
  refine SepWP.exists_elim fun t_238 => SepWP.exists_elim fun t_239 => ?_
  refine SepWP.exists_elim fun t_240 => SepWP.exists_elim fun t_248 => ?_
  refine SepWP.exists_elim fun t_256 => ?_
  refine SepWP.exists_elim fun k_297 => SepWP.exists_elim fun k_305 => ?_
  refine SepWP.exists_elim fun k_313 => SepWP.exists_elim fun k_321 => ?_
  refine SepWP.exists_elim fun k_322 => SepWP.exists_elim fun k_323 => ?_
  refine SepWP.exists_elim fun k_324 => SepWP.exists_elim fun k_325 => ?_
  refine SepWP.exists_elim fun k_326 => SepWP.exists_elim fun k_327 => ?_
  refine SepWP.exists_elim fun k_328 => SepWP.exists_elim fun s_332 => ?_
  refine SepWP.exists_elim fun s_333 => SepWP.exists_elim fun s_341 => ?_
  refine SepWP.exists_elim fun s_342 => SepWP.exists_elim fun s_344 => ?_
  refine SepWP.exists_elim fun s_345 => SepWP.exists_elim fun s_349 => ?_
  refine SepWP.exists_elim fun s_350 => SepWP.exists_elim fun s_352 => ?_
  refine SepWP.exists_elim fun s_360 => SepWP.exists_elim fun s_364 => ?_
  refine SepWP.exists_elim fun s_365 => SepWP.exists_elim fun s_373 => ?_
  refine SepWP.exists_elim fun s_381 => SepWP.exists_elim fun s_389 => ?_
  refine SepWP.exists_elim fun s_391 => SepWP.exists_elim fun s_395 => ?_
  refine SepWP.exists_elim fun s_396 => SepWP.exists_elim fun s_400 => ?_
  refine SepWP.exists_elim fun s_408 => SepWP.exists_elim fun s_416 => ?_
  refine SepWP.exists_elim fun s_424 => SepWP.exists_elim fun s_432 => ?_
  refine SepWP.exists_elim fun c_440 => SepWP.exists_elim fun c_448 => ?_
  refine SepWP.exists_elim fun c_456 => ?_
  wp_steps 19
  refine SepWP.fold (sp_256_split_32_16_2 s0.sp _) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun h_252 => SepWP.exists_elim fun d_256 => ?_
  wp_steps
  refine SepWP.fold (rk_10c_pack_stack s0.sp hrk) (by sep_focus) ?_
  refine SepWP.fold (scRawCells_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_256_24_fold s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_280_184_fold_10c s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (vecU8At_nil_pq_ss A ss) (by sep_focus) ?_
  refine SepWP.fold (sessionAfter208Frame_intro A ss G st) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_f hro_f
  have h16 : BitVec.truncate 16 (BitVec.truncate 32 rx16) = BitVec.setWidth 16 rx16 := by bv_kernel
  have h15 : BitVec.truncate 16 (BitVec.truncate 32 rx15) = BitVec.setWidth 16 rx15 := by bv_kernel
  have hb200 : BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b_200 &&& 1095216660735#64) = b_200 := by bv_kernel
  rw [h16, h15, hb200]
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hcont _ hcl_f hro_f
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

def trFromRawPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec TrFromGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = 0#32 ∧
      s.readReg64 .x8 = x.ret⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 264 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s.sp trFromStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜x.G.AfterTryDecrypt false x.G.afterTrFrom ∧ sf.trace = s0.trace⌝ ∗
      sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
      trResultAt A x.ret x.G x.model.1 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp trFromStack ∗ A.pool

def trFromPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec TrFromGhost :=
  withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (trFromRawPlacedSpec A))

theorem trFrom_step_244_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A)))
    (x : TrFromGhost) (senderPad : List (BitVec 8))
    (s0 s : State) (post : State → SepProp → Prop)
    (u_284 : BitVec 32)
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, x.st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpq_ne : x.G.pq.cap ≠ 0 → 0 < x.G.pq.cap.toNat ∧ x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length)
    (hrik : match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = x.G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.G.pq.cap)
    (hx21 : s.readReg64 .x21 = x.G.pq.ptr)
    (hx22 : s.readReg64 .x22 = x.ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hdone : ∀ sf,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) sf
        (sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
         trResultAt A x.ret x.G x.model.1 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp trFromStack ∗ A.pool)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) s
      (((x.G.localIk.ptr ↦ₛ x.G.localIk.bytes) ∗
        vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 496#64) 40 ∗
        memRegion (s0.sp - 280#64) 184 ∗
        stackAt (s0.sp - 496#64) dropVecChainStack ∗
        (A.pool ∗
         ((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
         vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain senderPad) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion x.ret 264 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         ((lsLogFilterAddr ↦₆₄ 0#64) ∗ trFromSavedRegs s0.sp s0))))
      post := by
  apply trFrom_step_244_to_0e8_placed hdealloc hRemoteIk hDropSpe hDropVecChain
    x.ret x.ss x.G x.st senderPad s0 s (s0.readReg64 .lr)
    (trFromSavedRegs s0.sp s0) post
    hpad hclamp hchains hpq_ne hlik hlik_toNat hrik hcl hro hpc hrun halign htr
    hx0 hx1 hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hsp
  intro sf hcl_f hro_f hpc_f hrun_f htr_f hsp_f hvregs_f
  have hm1 : ∀ a, a = (match x.st.remoteIdentity with
        | some rem =>
          .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
                x.st.previousCounter, maxForwardJumps⟩,
               x.st.pqRatchetState, x.st.localIdentity, rem⟩
        | none => .error (.invalidSessionStructure .missingRemoteIdentity)) →
      trResultAt A x.ret x.G a = trResultAt A x.ret x.G x.model.1 := by
    rintro _ rfl
    rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
    cases rik <;> rfl
  rw [hm1 _ (by rfl), ← trFromGhost_model_snd x]
  unfold trFromSavedRegs
  apply sepWP_seq_lscl_ro hcl_f hro_f (mid := s0.readReg64 .lr)
  wp_steps
  refine SepWP.fold (stackAt_trFrom_fold s0.sp s0) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_ret hro_ret
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hdone _
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
      hcl_ret hro_ret)

abbrev trFrom10cTailPlaced [LibsignalPlacement] (A : RustAlloc) (x : TrFromGhost) (s0 : State) : SepProp :=
  (x.G.localIk.ptr ↦ₛ x.G.localIk.bytes) ∗
  vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
  memRegion (s0.sp - 496#64) 40 ∗
  stackAt (s0.sp - 496#64) dropVecChainStack ∗
  A.pool ∗
  vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
  vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
  memRegion x.ret 264 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  trFromSavedRegs s0.sp s0

end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet
