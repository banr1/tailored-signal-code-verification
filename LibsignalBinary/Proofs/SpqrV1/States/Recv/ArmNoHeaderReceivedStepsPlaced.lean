/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedSteps
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.noHeaderReceived` Arm Steps (Relocatable)

Relocatable `[LibsignalPlacement]` jump-table dispatch (`+36 -> +2132`) and instruction-level
stepping lemmas for `.noHeaderReceived` (`lsmpl.base 332 + 2132#64`, tag `7#64`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append

/-- Jump-table dispatch (`+36 -> +2132`) specialized to `tag = 7#64` (`.noHeaderReceived`). -/
theorem states_recv_dispatch_noHeaderReceived_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 2132#64)
      s1
      ((st_ptr ↦₆₄ 7#64) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ 7#64) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 5#64 ∧
        s2.readReg64 .x12 = 7#64 ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) :=
  states_recv_dispatch_placed (ext := ext) s1 fsp st_ptr 7#64 Rest
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

theorem call_memcpy_words57_cs_stack {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpySpec 4096))
    (dst src : BitVec 64) (w : Words57)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 456)
    (hsplit : P = (memRegion dst 456 ∗ words57At src w ∗ stackAt sp_call 4096) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((words57At dst w ∗ words57At src w ∗ stackAt sp_call 4096) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  let bs := wordsBytes (words57List w)
  have hlen : bs.length = 456 := length_wordsBytes_words57List w
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack]
    rw [hlen, hsp, ← words57At_eq_pointsToBytes src w, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · dsimp only [sessionMemcpySpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← words57At_eq_pointsToBytes dst w, ← words57At_eq_pointsToBytes src w]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((words57At dst w ∗ words57At src w ∗ stackAt sp_call 4096) ∗ Frame) by ac_rfl)) ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

set_option maxHeartbeats 800000 in
theorem nhr_step_2132_2180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out st_ptr msg_ptr msg_ep w62_old : BitVec 64)
    (w : Words57) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 2132#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 2180#64) s
      (memRegion (fsp + 2752#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w62_old) ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 2752#64) w ∗ words57At (st_ptr + 8#64) w ∗
          (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w.b0.w6) ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b0.w6)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b0.w6) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  rw [stackAt_statesRecvCallee_eq_allocHook s.sp]
  dsimp only [lsProg_332, lsρ, memcpyName, allocHookStack, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  wp_steps
  refine call_memcpy_words57_cs_stack (ret_pc := (blkPl_332).base + 2152#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 2752#64) (s.readReg64 .x1 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x1 := hcs1.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  wp_simp_pre [words57At, words10At, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, words10At, ekCmpW8, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc,
    hx19_1, hx21_1, hx24_1, hx29_1, htr1]
  wp_done

set_option maxHeartbeats 800000 in
theorem nhr_step_8984_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 8984#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 18996#64) s
      (sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ sendEkSpillsAt fsp (nhrSpills8984 s sp) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x1 = sp.b1.w6 ∧
        sm.readReg64 .x2 = sp.b1.w0 ∧ sm.readReg64 .x3 = s.readReg64 .x27 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = sp.b2.w6 ∧
        sm.readReg64 .x6 = s.readReg64 .x7 ∧ sm.readReg64 .x7 = s.readReg64 .x20 ∧
        sm.readReg64 .x8 = sp.b2.w5 ∧ sm.readReg64 .x9 = s.readReg64 .x14 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧ sm.readReg64 .x17 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp.b1.w7 ∧
        sm.readReg64 .x21 = sp.b2.w9 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp.b1.w8 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x2 ∧
        sm.readReg64 .x27 = sp.b1.w9 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpills8984, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpills8984, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 1200000 in
theorem nhr_step_8664_8984_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 8664#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8984#64) s
      (words57At (fsp + 2752#64) w ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words57At (fsp + 2752#64) w ∗ sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w.b3.w9 ∧ sm.readReg64 .x1 = w.b2.w7 ∧
        sm.readReg64 .x2 = w.b4.w7 ∧ sm.readReg64 .x3 = w.w54 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w6 ∧
        sm.readReg64 .x6 = w.w50 ∧ sm.readReg64 .x7 = w.b4.w0 ∧
        sm.readReg64 .x9 = w.b1.w7 ∧ sm.readReg64 .x10 = w.b3.w5 ∧
        sm.readReg64 .x11 = w.b3.w4 ∧ sm.readReg64 .x12 = w.b3.w3 ∧
        sm.readReg64 .x13 = w.w52 ∧ sm.readReg64 .x14 = w.b4.w3 ∧
        sm.readReg64 .x15 = w.b3.w6 ∧ sm.readReg64 .x16 = w.w55 ∧
        sm.readReg64 .x17 = w.w53 ∧ sm.readReg64 .x18 = w.b4.w5 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = w.b3.w8 ∧
        sm.readReg64 .x22 = w.w51 ∧ sm.readReg64 .x23 = w.b1.w9 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w2 ∧
        sm.readReg64 .x26 = w.b1.w8 ∧ sm.readReg64 .x27 = w.b2.w9 ∧
        sm.readReg64 .x28 = w.b3.w7 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b4.w1 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words57At, sendEkSpillsAt, words10At, nhrSpills8664, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, sendEkSpillsAt, words10At, nhrSpills8664, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

theorem nhr_step_2180_lt_8664_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 255#32) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8664#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps; wp_done

theorem nhr_step_2180_eq_8568_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = true) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8568#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem nhr_step_8568_non_hdr_8664_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp msg_ptr : BitVec 64) (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hno : ∀ c, p ≠ .hdr c)
    (hpc : s.pc = lsmpl.base 332 + 8568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8664#64) s
      (messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  cases p with
  | hdr c => exact False.elim (hno c rfl)
  | none | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ | ct2 _ =>
    dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
    wp_simp_pre [sepConj_assoc]; wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem nhr_step_8568_hdr_8612_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (chunk : Chunk) (w : Words57) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 8568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msg_ep)
    (hx21 : s.readReg64 .x21 = st_ptr) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8612#64) s
      (memRegion (fsp + 976#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 976#64) w ∗ words57At (st_ptr + 8#64) w ∗
          messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧
        sm.readReg64 .x1 = fsp + 976#64 ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x3 = msg_ptr + 10#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20 hx21 hx24
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  rw [stackAt_statesRecvCallee_eq_allocHook s.sp]
  dsimp only [lsProg_332, lsρ, memcpyName, allocHookStack, messagePayloadAt, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine call_memcpy_words57_cs_stack (ret_pc := (blkPl_332).base + 8596#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x21 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x21 := hcs1.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  wp_steps
  simp only [sepConj_assoc, hx19_1, hx20_1, hx21_1, hx24_1, hx29_1, htr1]
  wp_done

set_option maxHeartbeats 800000 in
theorem nhr_step_2180_gt_19324_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s : State) (fsp out msg_ep u0 u16 : BitVec 64) (u8 : BitVec 8)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 1#32)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msg_ep) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64) s
      ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₈ u8) ∗ ((out + 16#64) ↦₆₄ u16) ∗
       chunkedNoHeaderReceivedAt A (fsp + 2752#64) st ∗
       A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 4#8) ∗ ((out + 16#64) ↦₆₄ msg_ep) ∗
          memRegion (fsp + 2752#64) 456 ∗
          A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, lsρ, spqrDeallocSym,
    chunkedNoHeaderReceivedAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  nth_rw 1 [stackAt_dropStack32_split_bottom s.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_left (unchunkedNoHeaderReceivedAt_entails_dealloc A (s.sp + 2752#64) st.uc)))))) ?_
  wp_pull_exists; rename_i g
  refine LibsignalBinary.Proofs.SpqrV1.States.Recv.seq_clean_lscl hcl (mid := (blkPl_332).base + 2232#64)
    (P_mid := ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
      ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
      ((twoVec56HeadersAt (s.sp + 2752#64) g ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
       polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
      A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s)
    ?_ ?_
  · dsimp only [twoVec56HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
      wp_steps
      refine DropGlueFacts.align_pre
        (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, beq_iff_eq]; ac_rfl) ?_
      wp_done
    · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
      wp_steps; wp_apply
      refine DropGlueFacts.align_pre
        (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, beq_iff_eq]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp_1, hx29_1, htrace_1⟩
    refine LibsignalBinary.Proofs.SpqrV1.States.Recv.seq_clean_lscl hcl1 (mid := (blkPl_332).base + 2252#64)
      (P_mid := ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
        ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
        ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
        (memRegion (s.sp + 2752#64) 56 ∗
         polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
        A.pool ∗ stackAt s.sp dropStack32 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s)
      ?_ ?_
    · have hstep2 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
          ((blkPl_332).base + 2252#64) s1
          ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
            ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
            ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
            ((twoVec56HeadersAt (s.sp + 2752#64) g ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
             polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
            A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
              ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
              ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
              (twoVec56HeadersAt (s.sp + 2752#64) g ∗
               polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
              A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame) ∧
            sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
        dsimp only [twoVec56HeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
          wp_steps
          refine DropGlueFacts.align_pre
            (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; ac_rfl) ?_
          wp_done
        · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
          wp_steps; wp_apply
          refine DropGlueFacts.align_pre
            (by rw [hsp_1]; dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; ac_rfl) ?_
          wp_done
      rw [stackAt_dropStack32_split_bottom s.sp]
      exact SepWP.strengthen_entails_const
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_left (twoVec56HeadersAt_entails_memRegion_56 (s.sp + 2752#64) g))))))
        hstep2
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp_2, hx29_2, htrace_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_right
            (polyDecoderAt_entails_vecs_tail A ((s.sp + 2752#64) + 56#64) st.receiving_hdr)))))) ?_
      wp_pull_exists; rename_i vecs
      have h2808 : (s.sp + 2752#64) + 56#64 = s.sp + 2808#64 := by bv_omega
      have h440 : (s.sp + 2808#64) + 384#64 = (s.sp + 2752#64) + 440#64 := by bv_omega
      rw [h2808, h440]
      wp_focus_pure; intro hvecs_len
      refine CryptoVerification.sepWP_seq_lscl hcl2 (mid := lsmpl.base 264) ?_
      wp_steps
      refine SepWP.done rfl hrun2 (fun hcl3 => ?_)
      have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
        (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hcl3
      dsimp only [withMemEq, dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hpt16_raw
      have hstack_eq : dropStack32 = dropGluePoly16Stack := rfl
      rw [hstack_eq, ← hsp_2]
      wp_call hpt16_raw ⟨s2.sp + 2808#64, vecs⟩
      wp_steps
      rw [← hstack_eq, hsp_2]
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (s.readReg64 (Reg.gpr 19#5) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((s.readReg64 (Reg.gpr 19#5) + 8#64) ↦₈ 4#8) ∗
              ((s.readReg64 (Reg.gpr 19#5) + 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
              (memRegion (s.sp + 2752#64) 56 ∗
               memRegion (s.sp + 2808#64) polyArrayBytes ∗
               memRegion (s.sp + 3192#64) 16) ∗
              A.pool ∗ stackAt s.sp dropStack32 ∗ Frame by ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (chunked_nhr_456_join s.sp)))))) ?_
      dsimp only [Reg.x19, Reg.x20, Reg.x29] at hx29_2 ⊢
      wp_done

theorem nhr_step_8612_call_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp msg_ep msg_ptr : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 8612#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1856#64) (hx1 : s.readReg64 .x1 = fsp + 976#64)
    (hx2 : s.readReg64 .x2 = msg_ep) (hx3 : s.readReg64 .x3 = msg_ptr + 10#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 369) s Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧ sm.readReg64 .x1 = fsp + 976#64 ∧
        sm.readReg64 .x2 = msg_ep ∧ sm.readReg64 .x3 = msg_ptr + 10#64 ∧
        sm.readReg64 .x30 = lsmpl.base 332 + 8616#64 ∧
        CalleeSavedPreserved s sm ∧ TraceCalleeSaved sm s) := by
  subst hsp hx2
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  dsimp only [blkPl_332, Obj.MultiPlacedLib.blockPlacement]
  wp_done

theorem nhr_step_8616_err_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out w1 w2 w3 sp_w61 o0 o1 o2 o3 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64) s
      (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
       ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ sp_w61) ∗
       (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
          ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ w3) ∗
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [sepConj_assoc]; wp_steps; wp_done

set_option maxHeartbeats 1200000 in
theorem nhr_step_8616_ok_15296_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (w : Words60) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w.b0.w0 ≠ 0xfffffffffffffffe#64)
    (hpc : s.pc = lsmpl.base 332 + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 15296#64) s
      (words60At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words60At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w.b0.w9 ∧ sm.readReg64 .x1 = w.b2.w0 ∧
        sm.readReg64 .x2 = w.b1.w5 ∧ sm.readReg64 .x4 = w.b1.w6 ∧
        sm.readReg64 .x5 = w.b5.w3 ∧ sm.readReg64 .x6 = w.b5.w1 ∧
        sm.readReg64 .x7 = w.b2.w6 ∧ sm.readReg64 .x8 = w.b5.w5 ∧
        sm.readReg64 .x9 = w.b1.w7 ∧ sm.readReg64 .x10 = w.b1.w3 ∧
        sm.readReg64 .x11 = w.b4.w8 ∧ sm.readReg64 .x12 = w.b3.w0 ∧
        sm.readReg64 .x13 = w.b4.w3 ∧ sm.readReg64 .x14 = w.b1.w1 ∧
        sm.readReg64 .x15 = w.b1.w2 ∧ sm.readReg64 .x16 = w.b5.w7 ∧
        sm.readReg64 .x17 = w.b5.w4 ∧ sm.readReg64 .x18 = w.b1.w0 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = w.b0.w6 ∧
        sm.readReg64 .x21 = w.b4.w7 ∧ sm.readReg64 .x22 = w.b0.w0 ∧
        sm.readReg64 .x23 = w.b1.w9 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = w.b1.w8 ∧
        sm.readReg64 .x27 = w.b5.w6 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w.b2.w1 ∧
        sm.pstate = addsPState64 w.b0.w0 1#64 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hz : (w.b0.w0 + 2#64 != 0#64) = true := add_two_bne_zero_of_ne hw0
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words60At, sendEkSpillsAt, words10At, nhrSpills15296, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words60At, sendEkSpillsAt, words10At, nhrSpills15296, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 800000 in
theorem nhr_step_15296_still_8984_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 15296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hps : s.pstate = addsPState64 noneCap 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8984#64) s
      (sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ sendEkSpillsAt fsp (nhrSpillsStill8984 s sp) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = sp.b1.w2 ∧ sm.readReg64 .x1 = sp.b3.w4 ∧
        sm.readReg64 .x2 = s.readReg64 .x11 ∧ sm.readReg64 .x3 = sp.b5.w9 ∧
        sm.readReg64 .x4 = sp.b2.w2 ∧ sm.readReg64 .x5 = s.readReg64 .x21 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = sp.b0.w6 ∧
        sm.readReg64 .x8 = sp.b5.w2 ∧ sm.readReg64 .x9 = s.readReg64 .x26 ∧
        sm.readReg64 .x10 = sp.b0.w1 ∧ sm.readReg64 .x11 = sp.b0.w8 ∧
        sm.readReg64 .x12 = sp.b0.w9 ∧ sm.readReg64 .x13 = s.readReg64 .x5 ∧
        sm.readReg64 .x14 = sp.b2.w3 ∧ sm.readReg64 .x15 = sp.b1.w3 ∧
        sm.readReg64 .x16 = s.readReg64 .x27 ∧ sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x18 = sp.b2.w4 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp.b0.w7 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp.b2.w1 ∧ sm.readReg64 .x23 = s.readReg64 .x1 ∧
        sm.readReg64 .x24 = sp.b0.w2 ∧ sm.readReg64 .x25 = sp.b0.w4 ∧
        sm.readReg64 .x26 = s.readReg64 .x23 ∧ sm.readReg64 .x27 = s.readReg64 .x12 ∧
        sm.readReg64 .x28 = sp.b1.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w5 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc hps ⊢
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpillsStill8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpillsStill8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 1200000 in
theorem nhr_step_15296_done_8984_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp w0 w58 w59 : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_ne_none : w0 ≠ noneCap)
    (hpc : s.pc = lsmpl.base 332 + 15296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hps : s.pstate = addsPState64 w0 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 8984#64) s
      (((fsp + 2320#64) ↦₆₄ w58) ∗ ((fsp + 2328#64) ↦₆₄ w59) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 2320#64) ↦₆₄ w58) ∗ ((fsp + 2328#64) ↦₆₄ w59) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ sendEkSpillsAt fsp (nhrSpillsDone8984 s sp w58 w59) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = sp.b0.w7 ∧ sm.readReg64 .x1 = sp.b4.w0 ∧
        sm.readReg64 .x2 = s.readReg64 .x21 ∧ sm.readReg64 .x3 = s.readReg64 .x17 ∧
        sm.readReg64 .x4 = sp.b2.w6 ∧ sm.readReg64 .x5 = sp.b2.w4 ∧
        sm.readReg64 .x6 = sp.b2.w2 ∧ sm.readReg64 .x7 = sp.b1.w2 ∧
        sm.readReg64 .x8 = 8#64 ∧ sm.readReg64 .x9 = s.readReg64 .x9 ∧
        sm.readReg64 .x10 = sp.b0.w8 ∧ sm.readReg64 .x11 = sp.b0.w9 ∧
        sm.readReg64 .x12 = sp.b0.w4 ∧ sm.readReg64 .x13 = sp.b2.w1 ∧
        sm.readReg64 .x14 = s.readReg64 .x13 ∧ sm.readReg64 .x15 = sp.b0.w1 ∧
        sm.readReg64 .x16 = sp.b5.w9 ∧ sm.readReg64 .x17 = s.readReg64 .x5 ∧
        sm.readReg64 .x18 = sp.b5.w1 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp.b1.w5 ∧ sm.readReg64 .x21 = s.readReg64 .x22 ∧
        sm.readReg64 .x22 = s.readReg64 .x6 ∧ sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = sp.b3.w8 ∧ sm.readReg64 .x25 = sp.b0.w2 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = sp.b3.w9 ∧
        sm.readReg64 .x28 = sp.b1.w3 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w6 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hz : (w0 + 1#64 == 0#64) = false := add_one_beq_zero_false_of_ne hw0_ne_none
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hps ⊢
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpillsDone8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpillsDone8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

end CryptoVerification.SpqrV1.States.Recv
