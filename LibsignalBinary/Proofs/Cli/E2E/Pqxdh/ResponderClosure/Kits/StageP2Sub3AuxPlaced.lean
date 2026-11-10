/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3Aux
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1

/-!
# Relocatable Stage P2 Substage P2.3 Helpers and Shared Tail

Provides placed `KyberPreKeyStoreKit` precondition helpers and proves the placed shared Substage
P2.3 tail (`+0x0d04 → +0x0d5c`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding sessionRecordEmptyHeaderAt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_kpkGetPoll_pre_intro_placed {A : RustAlloc}
    {kpkKit : KyberPreKeyStoreSpec A 0#64}
    {x : PreKeyPollCall} {st0 : kpkKit.KpkState} {s : State}
    (henv : kpkKit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : kpkKit.getIdOk x.id) :
    kpkKit.getBoxAt x.fut x.self x.id 0#8 ∗ kpkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool ∗ stackAt s.sp kpkKit.getPollStack ⊢
        (kitKpkGetPollSpecE kpkKit).pre (x, st0) s := by
  dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hid⟩ (Entails.refl _))

theorem p2_call_plain_nopanic_steps_frame_placed [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P F T : SepProp} {R_pure : Prop} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : spec.pre x s = ⌜R_pure⌝ ∗ T)
    (hpure : R_pure)
    (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hpre, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrl' : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 800000 in
theorem p2_seg3d2_alloc_cro_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (s0 s : State)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = 21#64)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0xd08#64) s
      (A.pool ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          A.live (s1.readReg64 .x0) 21 1 ∗
          memRegion (s1.readReg64 .x0) 21 ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 ≠ 0#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
      (PanicOomProp s0) := by
  have hbl := p2_seg3d2_bl_alloc_ext_placed_wp ext s hpc hrun
  refine p2_bind_sepWP_qp_frame_placed hCode hbl (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hlay : LayoutOk 21 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine p2_call_plain_nopanic_steps_frame_placed
    (x := (21, 1)) (T := A.pool ∗ stackAt s1.sp allocHookStack) (F := emp)
    hCode1 hH.alloc hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨by rw [hx0_1, hx0]; decide, by rw [hx1_1, hx1]; decide, hlay⟩ (by rw [hsp1]; sep_focus)
    fun s2 _ hpc2 hrun2 hsp2 _ hcs2 hCode2 => ?_
  dsimp only [rustAllocSpec]
  rcases hcs2 with ⟨hcs19, _, hcs21, hcs22, hcs23, _, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
  by_cases hoom : s2.readReg64 .x0 = 0
  · have hoom64 : s2.readReg64 .x0 = 0#64 := hoom
    simp only [hoom, ↓reduceIte, sepConj_emp]
    refine SepWPp.pure_left_frame
      (φ := s2.trace = s1.trace ++ [allocFailedEvent])
      (P_rest := A.pool ∗ stackAt s1.sp allocHookStack)
      (by ac_rfl) fun htr2 => ?_
    have hoom_step := p2_seg3d2_oom_branch_ext_placed_wp ext s2 hpc2 hrun2 hoom64
    refine p2_bind_sepWP_qp_frame_placed hCode2 hoom_step (by sep_focus)
      fun s3 _ hpc3 hrun3 _ htr3 => ?_
    refine SepWPp.panic hrun3 (by simpa only [hpc3] using hH.handleError) fun R hm => ?_
    have htr_s : (Rust.panicked s3).trace = s.trace ++ [allocFailedEvent] := by
      simp [Rust.panicked, htr3, htr2, htr1]
    have ⟨ha_s, hp_s⟩ := Initiator.allocFailedIn_of_eq htr_s
    exact allowPanic_panicked ⟨p2_allocFailedIn_of_trace_prefix htr ha_s, htr.trans hp_s⟩ hm
  · have hoom64 : s2.readReg64 .x0 ≠ 0#64 := hoom
    simp only [hoom, ↓reduceIte, sepConj_emp]
    refine SepWPp.pure_left_frame
      (φ := (s2.readReg64 .x0).toNat % 1 = 0 ∧ s2.trace = s1.trace)
      (P_rest := A.live (s2.readReg64 .x0) 21 1 ∗ memRegion (s2.readReg64 .x0) 21 ∗
        A.pool ∗ stackAt s1.sp allocHookStack)
      (by ac_rfl) fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2 ⟨?_, hsp2.trans hsp1, htr2.trans htr1, hoom64,
      hcs19.trans hx19_1, hcs21.trans hx21_1, hcs22.trans hx22_1,
      hcs23.trans hx23_1, hcs25.trans hx25_1,
      hcs26.trans hx26_1, hcs27.trans hx27_1,
      hcs28.trans hx28_1, hcs29.trans hx29_1,
      hcsv.trans hvregs1, hCode2⟩
    rw [hsp1]
    exact Entails.of_eq (by ac_rfl)

private abbrev missingKyberSym : String := "libsignal_cli_handshake:.rodata..Lanon.89"

private theorem lsroSliceCheck_missingKyber_0 :
    lsroSliceCheck missingKyberSym 0 (((lsroBytes missingKyberSym).drop 0).take 8) = true := by
  rfl_kernel

private theorem lsroSliceCheck_missingKyber_8 :
    lsroSliceCheck missingKyberSym 8 (((lsroBytes missingKyberSym).drop 8).take 8) = true := by
  rfl_kernel

private theorem lsroSliceCheck_missingKyber_13 :
    lsroSliceCheck missingKyberSym 13 (((lsroBytes missingKyberSym).drop 13).take 8) = true := by
  rfl_kernel

theorem p2_missingKyber_ro0_sepWPp_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro0 : BitVec 64,
      SepWPp prog ret s
        (((lsρ "libsignal_cli_handshake:.rodata..Lanon.89") ↦₆₄ᵣ ro0) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hRO := (lsro_slice_read hCode.2 lsroSliceCheck_missingKyber_0).1
  have hlen : (((lsroBytes missingKyberSym).drop 0).take 8).length = 8 := by rfl_kernel
  rw [hlen, BitVec.add_zero] at hRO
  refine h (s.mem.read64 (lsρ "libsignal_cli_handshake:.rodata..Lanon.89")) R ?_ hL
  rw [sepConj_assoc]
  exact Satisfies.rodata64_intro hRO rfl hm

theorem p2_missingKyber_ro8_sepWPp_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro8 : BitVec 64,
      SepWPp prog ret s
        (((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64) ↦₆₄ᵣ ro8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hRO := (lsro_slice_read hCode.2 lsroSliceCheck_missingKyber_8).1
  have hlen : (((lsroBytes missingKyberSym).drop 8).take 8).length = 8 := by rfl_kernel
  rw [hlen] at hRO
  refine h (s.mem.read64 (lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64)) R ?_ hL
  rw [sepConj_assoc]
  exact Satisfies.rodata64_intro hRO rfl hm

theorem p2_missingKyber_ro13_sepWPp_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro13 : BitVec 64,
      SepWPp prog ret s
        (((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64) ↦₆₄ᵣ ro13) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hRO := (lsro_slice_read hCode.2 lsroSliceCheck_missingKyber_13).1
  have hlen : (((lsroBytes missingKyberSym).drop 13).take 8).length = 8 := by rfl_kernel
  rw [hlen] at hRO
  refine h (s.mem.read64 (lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64)) R ?_ hL
  rw [sepConj_assoc]
  exact Satisfies.rodata64_intro hRO rfl hm

set_option maxHeartbeats 1200000 in
/-- Placed shared Substage P2.3 tail (`+0x0d04 -> +0x0d5c`): allocates the 21-byte
`"missing pq ciphertext"` error string, builds `SignalProtocolError::InvalidMessage`,
and drops it because `kyberCtCap ≠ 0#64`. -/
theorem stageP2_sub3_tail_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ sf : State,
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool ∗ stackAt sp stk ∗ Frame)
        Q (PanicOomProp s0)) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗
       memRegion (sp + 0x3e0#64) 88 ∗
       A.pool ∗ stackAt sp stk ∗ Frame)
      Q (PanicOomProp s0) := by
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hs_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp]; exact hsp_align
  have hstep8 := p2_seg3d2_alloc_cro_placed_ok ext hH s0 s hCode hpc hrun hs_align htr hx0 hx1
  rw [hsp] at hstep8
  refine p2_bind_sepWPp_steps_frame_oom hstep8 (by sep_focus)
    fun s8 hst08 hpc8 hrun8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8, htr8, herr_nz, hx19_8, hx21_8, hx22_8, hx23_8, hx25_8, hx26_8, hx27_8,
    hx28_8, hx29_8, hvregs8, hCode8⟩
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_sp_a90_5words_entails_memRegion (sp + 0xa90#64) 0xfffffffffffffffe#64 pkBuf 0x620#64 skBuf
      0xc60#64)
    (by rw [show (sp + 0xa90#64) + 8#64 = sp + 0xa98#64 by bv_omega,
            show (sp + 0xa90#64) + 16#64 = sp + 0xaa0#64 by bv_omega,
            show (sp + 0xa90#64) + 24#64 = sp + 0xaa8#64 by bv_omega,
            show (sp + 0xa90#64) + 32#64 = sp + 0xab0#64 by bv_omega,
            show (sp + 0xa90#64) + 40#64 = sp + 0xab8#64 by bv_omega]; sep_focus) ?_
  refine p2_missingKyber_ro0_sepWPp_placed hCode8 fun ro0 => ?_
  refine p2_missingKyber_ro8_sepWPp_placed hCode8 fun ro8 => ?_
  have hstep9 := p2_seg3d2a_ext_placed_wp ext s8 coroPtr (s8.readReg64 .x0) ro0 ro8
    herr_nz hpc8 hrun8 rfl (hx19_8.trans hx19)
  refine p2_bind_sepWP_qp_frame_placed hCode8 hstep9 (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx8_9, hx9_9, hq0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hvregs9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8.trans hsp8
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89") ↦₆₄ᵣ ro0) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64) ↦₆₄ᵣ ro8))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_errStr_21_split16_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_88_spe_split_eq sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u8_err => SepWPp.exists_elim fun u0_err =>
    SepWPp.exists_elim fun b_400_spe => SepWPp.exists_elim fun u_3f8_spe =>
    SepWPp.exists_elim fun u_3f0_spe => SepWPp.exists_elim fun u_3e8_spe =>
    SepWPp.exists_elim fun u_3e0_spe => ?_
  refine p2_missingKyber_ro13_sepWPp_placed hCode9 fun ro13 => ?_
  have hstep10 := p2_seg3d2b_ext_placed_wp ext s9 coroPtr (s8.readReg64 .x0)
    ro0 ro8 ro13 u0_err u8_err u_3f0_spe b_400_spe
    hpc9 hrun9 hsp9_align hx0_9 hx8_9 hx9_9 hq0_9 hx19_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_qp_frame_placed hCode9 hstep10 (by sep_focus)
    fun s10 hst9_10 hpc10 hrun10 hCode10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_9, htr10_9, hx0_10, hx8_10, hx9_10, hx19_10, hx21_10, hx22_10, hx23_10,
    hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hvregs10_9⟩
  have hsp10 : s10.sp = sp := hsp10_9
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64) ↦₆₄ᵣ ro13))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_errStr_overlap13_entails (s8.readReg64 .x0) ro8) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u13_err => ?_
  have hx22_10' : s10.readReg64 .x22 = kyberCtCap := by
    rw [hx22_10, hx22_9, hx22_8, hx22]
  have hstep11 := p2_seg3d2c_ext_placed_wp ext s10 coroPtr (s8.readReg64 .x0)
    kyberCtCap ro13 u13_err u_3e0_spe u_3e8_spe u_3f8_spe
    hkyber_nz hpc10 hrun10 hsp10_align hx0_10 hx8_10 hx9_10 hx19_10 hx22_10'
  rw [hsp10] at hstep11
  refine p2_bind_sepWP_qp_frame_placed hCode10 hstep11 (by sep_focus)
    fun s11 hst10_11 hpc11 hrun11 hCode11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, _, hx21_11, hx22_11, hx23_11, hx25_11,
    hx26_11, hx27_11, hx28_11, hx29_11, hx30_11, hvregs11_10⟩
  simp only [arm64_norm] at hpc11
  have hsp11 : s11.sp = sp := hsp11_10
  have hsp11_al : s11.spAligned = true := by simpa only [State.spAligned, hsp11] using hsp_align
  refine SepWPp.weaken_frame (p2_errStr_21_rejoin_entails (s8.readReg64 .x0) ro0 ro13)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_speAt_badCiphertext_preKey_intro A sp (s8.readReg64 .x0) herr_nz)
    (by sep_focus) ?_
  have hstk_spe := p2_stackAt_split_of_le sp stk dropSpeStack
    (Nat.le_trans p2_dropSpe_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_spe) (by sep_focus) ?_
  sep_norm
  refine p2_call_nopanic_rocl_steps_frame_placed
    (x := ⟨sp + 0x3e0#64, [], .invalidMessage .preKey .badCiphertext⟩)
    (R_pure := s11.readReg64 .x0 = sp + 0x3e0#64)
    (T := speAt A [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) ∗
      A.pool ∗ stackAt sp dropSpeStack)
    hCode11 (p2_rocl_of_lscl_ro hPure.dropSpe2) hpc11 hrun11 hsp11_al hx30_11
    (by dsimp only [dropSpeSpec]; rw [hsp11])
    hx0_11 (by sep_focus)
    (hnext := fun sf hst11_f hpcf hrunf hspf_11 _ hcsf hCodef => ?_)
  dsimp only [dropSpeSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, hcsf_22, hcsf_23, _, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_11⟩
  rw [hsp11]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htrf_11 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_spe.symm) (by sep_focus) ?_
  have hmr88_rejoin :
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 40 =
        memRegion (sp + 0x3e0#64) 88 :=
    (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 40)
      (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_rejoin) (by sep_focus) ?_
  have hsteps_all :=
    hst08.trans (hst89.trans (hst9_10.trans (hst10_11.trans hst11_f)))
  have hok := hOk sf hsteps_all hpcf hrunf (hspf_11.trans hsp11)
    (by rw [htrf_11, htr11_10, htr10_9, htr9_8, htr8])
    (hcsf_19.trans hx19_11)
    (by rw [hcsf_21, hx21_11, hx21_10, hx21_9, hx21_8])
    (hcsf_22.trans hx22_11)
    (by rw [hcsf_23, hx23_11, hx23_10, hx23_9, hx23_8])
    (by rw [hcsf_25, hx25_11, hx25_10, hx25_9, hx25_8])
    (by rw [hcsf_26, hx26_11, hx26_10, hx26_9, hx26_8])
    (by rw [hcsf_27, hx27_11, hx27_10, hx27_9, hx27_8])
    (by rw [hcsf_28, hx28_11, hx28_10, hx28_9, hx28_8])
    (by rw [hcsf_29, hx29_11, hx29_10, hx29_9, hx29_8])
    (by rw [hvregsf_11, hvregs11_10, hvregs10_9, hvregs9_8, hvregs8, hvregs])
    hCodef
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub3_tail_kits_4k_placed := @stageP2_sub3_tail_kits_ext_placed
abbrev stageP2_sub3_tail_kits_hooks_placed := @stageP2_sub3_tail_kits_ext_placed

theorem stageP2_sub3_tail_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} {stk : Nat}
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2PureCalleesPlaced P A F ext)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ sf : State,
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool ∗ stackAt sp stk ∗ Frame)
        Q (PanicOomProp s0)) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗ memRegion (sp + 0x3e0#64) 88 ∗
       A.pool ∗ stackAt sp stk ∗ Frame)
      Q (PanicOomProp s0) :=
  stageP2_sub3_tail_kits_ext_placed hH hPure.to_4K.toStageP2BaseCalleesPlaced4K hstk_pure hstk_lt
    s0 s ret sp coroPtr pkBuf skBuf kyberCtCap Frame Q hkyber_nz hCode hpc hrun hsp hsp_align
    htr hvregs hx0 hx1 hx19 hx22 hOk

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
