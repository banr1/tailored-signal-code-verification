/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WP.Apply

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 1 (Relocatable)

Relocatable `[LibsignalPlacement]` jump-table dispatch (`+36 -> +588`), entry epoch/payload
branch dispatch, and `msg.epoch > st.uc.epoch` exit path for `.ct1Acknowledged` (tag `11#64`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332

/-! ## 1. Relocatable Dispatch (`+36 -> +588`, Block `332`) -/

theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  CryptoVerification.sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem states_recv_dispatch_ct1Acknowledged_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 588#64)
      s1
      ((st_ptr ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧ s2.readReg64 .x0 = s1.readReg64 .x0 ∧ s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧ s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 9#64 ∧ s2.readReg64 .x12 = 11#64 ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧ s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧ s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved s2 s1) :=
  states_recv_dispatch_placed (ext := ext) s1 fsp st_ptr 11#64 Rest
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

/-! ## 2. Relocatable Entry Stepping (`+588 -> +644 / +4516 / +4432`) -/

/-- Framed `memcpy` call rule (`sessionMemcpySpec 4096`) that copies `words66At src w` (`528`B)
    into `memRegion dst 528`, producing `words66At dst w ∗ words66At src w` and forwarding
    `CalleeSavedPreserved s sf`. -/
theorem call_memcpy_words66_cs_stack {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpySpec 4096))
    (dst src : BitVec 64) (w : Words66)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 528)
    (hsplit : P = (memRegion dst 528 ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((words66At dst w ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  let bs := wordsBytes (words66List w)
  have hlen : bs.length = 528 := length_wordsBytes_words66List w
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack]
    rw [hlen, hsp, ← words66At_eq_pointsToBytes src w, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · dsimp only [sessionMemcpySpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← words66At_eq_pointsToBytes dst w, ← words66At_eq_pointsToBytes src w]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((words66At dst w ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame) by ac_rfl)) ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem ct1Ack_step_588_608_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out selfA msgA : BitVec 64) (w : Words66) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 608#64) s
      (memRegion (fsp + 976#64) 528 ∗
       words66At (selfA + 8#64) w ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words66At (fsp + 976#64) w ∗
          words66At (selfA + 8#64) w ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  rw [stackAt_statesRecvCallee_eq_allocHook s.sp]
  dsimp only [lsProg_332, lsρ, memcpyName, allocHookStack, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  wp_steps
  refine call_memcpy_words66_cs_stack (ret_pc := (blkPl_332).base + 608#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x1 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x1 := hcs1.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  wp_done

theorem ct1Ack_step_608_632_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep : BitVec 64) (b1 : Words10) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 632#64) s
      (words10At (fsp + 1056#64) b1 ∗
       (msgA ↦₆₄ msg_ep) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words10At (fsp + 1056#64) b1 ∗
          (msgA ↦₆₄ msg_ep) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = b1.w5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep b1.w5)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep b1.w5) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words10At, BitVec.ofNat_eq_ofNat, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words10At, ekCmpW8, subsPState64, BitVec.ofNat_eq_ofNat, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

/-! ## 3. Epoch & Payload Branch Dispatch (`+632 -> +644 / +4516 / +4432 -> +4448 / +4516`) -/

theorem ct1Ack_step_632_644_gt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (hgt : msg_ep > ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 644#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_gt hgt
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps
  wp_done

theorem ct1Ack_step_632_4516_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (hlt : msg_ep < ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4516#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_lt hlt
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps
  wp_done

theorem ct1Ack_step_632_4432_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (heq : msg_ep = ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4432#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_eq heq
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps
  wp_done

theorem ct1Ack_step_4432_4516_not_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA ep : BitVec 64)
    (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hek : ∀ c, p ≠ .ek c)
    (hekAck : ∀ c, p ≠ .ekCt1Ack c)
    (hpc : s.pc = lsmpl.base 332 + 4432#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4516#64) s
      (((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx9 hx19 hx20 hx24
  have hcond := messagePayloadTag_and6_bne_2_of_not_ek hek hekAck
  have hcond_eq := messagePayloadTag_and6_eq_2_of_not_ek hek hekAck
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hcond hcond_eq ⊢
  wp_steps
  wp_done

theorem ct1Ack_step_4432_4448_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA ep : BitVec 64)
    (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag p) &&& 25769803782#64) != 2#32) = false)
    (hpc : s.pc = lsmpl.base 332 + 4432#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4448#64) s
      (((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx19 hx20 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hcond ⊢
  wp_steps
  wp_done

/-! ## 4. Branch A (`msg.epoch > st.uc.epoch`: `+644 -> +764 -> +19324 -> s0.x30`) -/

set_option maxHeartbeats 600000 in
/-- Writes `Err(EpochOutOfRange(msg_ep))` to `outA` (`x19`) and deallocates the 5 `Vec<u8>`s
    of `st.uc` at `fsp + 976#64..+1104#64` (`+644 -> +764`, Block `332`). -/
theorem ct1Ack_write_err_and_dealloc5_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s3 : State) (fsp outA msg_ep : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 332 + 644#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx2 : s3.readReg64 .x2 = msg_ep)
    (hx19 : s3.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 764#64)
      s3
      (memRegion outA v1RecvSize ∗
        unchunkedCt1SentAt A (fsp + 976#64) uc ∗
        A.pool ∗
        stackAt fsp allocHookStack ∗
        Rest)
      (fun s8 P8 =>
        (P8 ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion (fsp + 976#64) 128 ∗
          A.pool ∗
          stackAt fsp allocHookStack ∗
          Rest) ∧
        s8.sp = fsp ∧
        TraceCalleeSaved s8 s3) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [lsmpl_base_332_eq] at hpc3 ⊢
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, BitVec.ofNat_eq_ofNat] at hpc3 hdealloc_raw ⊢
  wp_conv_pre =>
    rw [memRegion_out_960_split_err outA]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v16_out
  apply ProofLib.SepWP.exists_left; intro b8_out
  apply ProofLib.SepWP.exists_left; intro v0_out
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        unchunkedCt1SentAt A (fsp + 976#64) uc ∗
        ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
         memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Rest) by ac_rfl))
      (sepConj_mono_left (unchunkedCt1Sent976_entails_dealloc A fsp uc))) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro g
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 684#64)
    (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
      (fiveVec976HeadersAt fsp g ∗
       vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
       vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
       vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
    (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s3)
    ?_ ?_
  · have hstep1 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
        ((blkPl_332).base + 684#64) s3
        ((fiveVec976HeadersAt fsp g ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
         ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
          memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest))
        (fun sm Pm =>
          (Pm ⊢ (((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
            memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
            (fiveVec976HeadersAt fsp g ∗
             vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
             vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
          (sm.sp = fsp ∧ TraceCalleeSaved sm s3)) := by
      dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc, noneCap]
      cases hc1 : (g.v1.cap == 0#64) <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_apply; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp3]; ac_rfl)) ?_; wp_done
      · wp_steps; wp_done
    exact SepWP.strengthen_entails_const
      (sepConj_mono_left (sepConj_mono_left
        (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg_ep)))
      hstep1
  · intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 704#64)
      (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
        (fiveVec976HeadersAt fsp g ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
      (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s3)
      ?_ ?_
    · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc]
      cases hc2 : (g.v2.cap == 0#64) <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_apply; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp4]; ac_rfl)) ?_; wp_done
      · wp_steps; wp_done
    · intro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
      refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 724#64)
        (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          (fiveVec976HeadersAt fsp g ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
        (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s3)
        ?_ ?_
      · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc]
        cases hc3 : (g.v3.cap == 0#64) <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_apply; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp5]; ac_rfl)) ?_; wp_done
        · wp_steps; wp_done
      · intro s6 hpc6 hrun6 ⟨hsp6, htr6⟩
        refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 744#64)
          (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            (fiveVec976HeadersAt fsp g ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
          (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s3)
          ?_ ?_
        · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc]
          cases hc4 : (g.v4.cap == 0#64) <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_apply; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp6]; ac_rfl)) ?_; wp_done
          · wp_steps; wp_done
        · intro s7 hpc7 hrun7 ⟨hsp7, htr7⟩
          have hstep5 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
              ((blkPl_332).base + 764#64) s7
              ((resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                (fiveVec976HeadersAt fsp g ∗
                 vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
              (fun s8 P8 =>
                (P8 ⊢ (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                  fiveVec976HeadersAt fsp g) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
                s8.sp = fsp ∧
                TraceCalleeSaved s8 s3) := by
            dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc]
            cases hc5 : (g.v5.cap == 0#64) <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_apply; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp7]; ac_rfl)) ?_; wp_done
            · wp_steps; wp_done
          exact SepWP.strengthen_entails_const
            (Entails.trans
              (sepConj_mono_left (sepConj_mono_right (fiveVec976HeadersAt_entails_memRegion_128 fsp g)))
              (Entails.of_eq (by ac_rfl)))
            hstep5

/-- Calls `drop_glue::<[SortedSet<Pt>; 16]>` (`lsmpl.base 264`) on `fsp + 1104#64`, folds
    `memRegion (fsp + 976#64) 528`, and jumps to `+19324` (`+764 -> +19324`, Block `332`). -/
theorem ct1Ack_drop_decoder_to_19324_placed [LibsignalPlacement]
    {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s8 : State) (fsp : BitVec 64)
    (dec : PolyDecoder)
    (Rest : SepProp)
    (hcl8 : LibsignalCodeLoaded lsmpl s8.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc8 : s8.pc = lsmpl.base 332 + 764#64)
    (hrun8 : s8.status = .Running)
    (hsp8 : s8.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64)
      s8
      (memRegion (fsp + 976#64) 128 ∗
        polyDecoderAt A (fsp + 1104#64) dec ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun s9 P9 =>
        (P9 ⊢
          memRegion (fsp + 976#64) 528 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        s9.sp = fsp ∧
        TraceCalleeSaved s9 s8) := by
  subst hsp8
  rw [lsmpl_base_332_eq] at hpc8 ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc8 ⊢
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        polyDecoderAt A (s8.sp + 1104#64) dec ∗
        (memRegion (s8.sp + 976#64) 128 ∗
         A.pool ∗
         stackAt s8.sp statesRecvCalleeStackX ∗
         Rest) by ac_rfl))
      (sepConj_mono_left (polyDecoderAt_entails_vecs_tail A (s8.sp + 1104#64) dec))) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_dropGluePoly16' s8.sp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dec_vecs
  wp_focus_pure; intro hdec_len
  refine CryptoVerification.sepWP_seq_lscl hcl8 (mid := lsmpl.base 264) ?_
  wp_steps
  refine SepWP.done rfl hrun8 (fun hcl9 => ?_)
  have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
    (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hcl9
  dsimp only [withMemEq, dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hpt16_raw
  wp_call hpt16_raw ⟨s8.sp + 1104#64, dec_vecs⟩
  wp_steps
  have hjoin528 :
      memRegion (s8.sp + 976#64) 128 ∗
        (memRegion (s8.sp + 1104#64) polyArrayBytes ∗
         memRegion ((s8.sp + 1104#64) + 384#64) 16) ⊢
      memRegion (s8.sp + 976#64) 528 := by
    refine Entails.trans (sepConj_mono_right (polyDecoder_post_join (s8.sp + 1104#64))) ?_
    unfold polyDecoderSize
    rw [ProofLib.memRegion_split' (b := s8.sp + 976#64) (n := 128) (k := 400)
          (b' := s8.sp + 1104#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hstack_fold := stackAt_statesRecvCallee_from_dropGluePoly16 s8.sp
  refine CryptoVerification.SpqrV1.States.Recv.align_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s8.sp + 976#64) 128 ∗
          (memRegion (s8.sp + 1104#64) polyArrayBytes ∗
           memRegion ((s8.sp + 1104#64) + 384#64) 16)) ∗
        (memRegion (s8.sp - 19552#64) 15424 ∗ stackAt s8.sp dropGluePoly16Stack) ∗
        (A.pool ∗ Rest) by ac_rfl))
      (Entails.trans (sepConj_mono hjoin528 (sepConj_mono_left hstack_fold))
        (Entails.of_eq (by ac_rfl)))) ?_
  wp_done

/-- Full `EpochOutOfRange` return theorem (`+644 -> s0.readReg64 .x30`) for `.ct1Acknowledged`:
    combines `ct1Ack_write_err_and_dealloc5_placed` (`+644 -> +764`),
    `ct1Ack_drop_decoder_to_19324_placed` (`+764 -> +19324`),
    and `states_recv_epilogue_19324_placed` (`+19324 -> s0.readReg64 .x30`). -/
theorem ct1Ack_gt_644_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 644#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        memRegion selfA chunkedStatesSize ∗
        chunkedCt1AcknowledgedAt A (s0.sp - 4240#64 + 976#64) st ∗
        memRegion (s0.sp - 4240#64 + 1504#64) 352 ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 976 ∗
        memRegion (s0.sp - 4240#64 + 1856#64) 2288 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  set fsp := s0.sp - 4240#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  dsimp only [chunkedCt1AcknowledgedAt, spqrPolyApi]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  refine seq_clean_lscl hcl (mid := lsmpl.base 332 + 764#64)
    (P_mid :=
      memRegion (fsp + 976#64) 128 ∗
      polyDecoderAt A (fsp + 1104#64) st.receiving_ek ∗
      A.pool ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (P_rest ∗
       resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
       memRegion selfA chunkedStatesSize ∗
       memRegion fsp 976 ∗
       memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 2288 ∗
       statesRecvSavedCells s0))
    (Q := fun s8 => s8.sp = fsp ∧ TraceCalleeSaved s8 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_write_err_and_dealloc5_placed hdealloc s fsp outA msg_ep st.uc
      (polyDecoderAt A (fsp + 1104#64) st.receiving_ek ∗
       memRegion (fsp - 19552#64) 15456 ∗
       P_rest ∗
       memRegion selfA chunkedStatesSize ∗
       memRegion fsp 976 ∗
       memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 2288 ∗
       statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx2 hx19
    refine SepWP.weaken_pre ?_ (SepWP.mono hstep1 ?_)
    · rw [stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by ac_rfl)
    · intro s8 P8 _ _ ⟨hP8, hsp8, htr8⟩
      refine ⟨Entails.trans hP8 ?_, hsp8, htr8.trans htr⟩
      rw [stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by ac_rfl)
  · intro s8 hpc8 hrun8 hcl8 ⟨hsp8, htr8⟩
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 19324#64)
      (P_mid :=
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        statesRecvSavedCells s0 ∗
        (P_rest ∗
         resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         A.pool))
      (Q := fun s9 => s9.sp = fsp ∧ TraceCalleeSaved s9 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_drop_decoder_to_19324_placed hdealloc s8 fsp st.receiving_ek
        (P_rest ∗
         resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         memRegion fsp 976 ∗
         memRegion (fsp + 1504#64) 352 ∗
         memRegion (fsp + 1856#64) 2288 ∗
         statesRecvSavedCells s0)
        hcl8 hfsp_align hpc8 hrun8 hsp8
      refine SepWP.mono hstep2 ?_
      intro s9 P9 _ _ ⟨hP9, hsp9, htr9⟩
      refine ⟨Entails.trans hP9 ?_, hsp9, htr9.trans htr8⟩
      have hjoin4144 :
          memRegion fsp 976 ∗
          (memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352) ∗
          memRegion (fsp + 1856#64) 2288 ⊢
          memRegion fsp 4144 := by
        rw [← memRegion_976_880_split_528_352 fsp,
            ProofLib.memRegion_split' (b := fsp) (n := 976) (k := 3168) (b' := fsp + 976#64) rfl rfl (by decide),
            ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide)]
        exact Entails.of_eq (by ac_rfl)
      refine Entails.trans (Entails.of_eq (show _ =
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion fsp 976 ∗
         (memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352) ∗
         memRegion (fsp + 1856#64) 2288) ∗
        statesRecvSavedCells s0 ∗
        (P_rest ∗
         resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         A.pool) by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hjoin4144)
    · intro s9 hpc9 hrun9 ⟨hsp9, htr9⟩
      refine SepWP.mono
        (states_recv_epilogue_19324_placed s0 s9
          (P_rest ∗
           resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
           memRegion selfA chunkedStatesSize ∗
           A.pool)
          hsp0_align hpc9 hrun9 hsp9 htr9)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  states_recv_dispatch_ct1Acknowledged_placed
  call_memcpy_words66_cs_stack
  ct1Ack_step_588_608_placed
  ct1Ack_step_608_632_placed
  ct1Ack_step_632_644_gt_placed
  ct1Ack_step_632_4516_lt_placed
  ct1Ack_step_632_4432_eq_placed
  ct1Ack_step_4432_4516_not_ek_placed
  ct1Ack_step_4432_4448_ek_placed
  ct1Ack_write_err_and_dealloc5_placed
  ct1Ack_drop_decoder_to_19324_placed
  ct1Ack_gt_644_ret_placed
)

end CryptoVerification.SpqrV1.States.Recv
