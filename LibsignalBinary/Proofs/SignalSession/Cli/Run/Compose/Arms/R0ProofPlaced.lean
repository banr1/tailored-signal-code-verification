/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.WP.Apply
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import all Init.Data.String.Defs

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

/-!
# Relocatable Arm `R0` Proof for `signal_session::run`

Proves `run_hop_pre_of_slots` and `run_hop_pre_placed_ok` on Block `579` under `[LibsignalPlacement]`
and `[LsCodeInv CodeOk]`.
-/

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi Arm64.Process
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Internal Helpers -/

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "r0_close_post_rp" : tactic =>
  `(tactic| (repeat' refine ⟨?_, ?_⟩; all_goals (try simp only [wp_norm, arm64_norm, runPcPlaced_eq, *]; try rfl)))

private abbrev r0_addrSym_rp : String := "libsignal_cli:.rodata..Lanon.54"
private theorem r0_utf8_address_rp : utf8 "address" = [0x61#8, 0x64#8, 0x64#8, 0x72#8, 0x65#8, 0x73#8, 0x73#8] := by rfl_kernel
private theorem r0_lsroCheck_address_rp : lsroCheck r0_addrSym_rp (utf8 "address") = true := by rfl_kernel
private theorem r0_sepWPp_intro_address_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem) (h : SepWPp prog ret s (((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL; have hm' := lsro_intro_chk (LsCodeInv.toRoCl hinv).2 r0_lsroCheck_address_rp hm
  exact h R (by simpa only [lsρ, sepConj_assoc] using hm') hL
private theorem r0_extractLsb_append_lo_rp (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
private theorem r0_extractLsb_append_hi_rp (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
private theorem r0_calleeSavedVRegs_q0_rp (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
private theorem r0_calleeSavedVRegs_writeReg64_rp (s : State) (r : Reg) (v : BitVec 64) : calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl
private theorem r0_calleeSavedVRegs_setPC_rp (s : State) (pc : BitVec 64) : calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
private theorem r0_calleeSavedVRegs_setMem_rp (s : State) (m : Memory) : calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
private theorem r0_calleeSavedVRegs_setPState_rp (s : State) (ps : PState) : calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl
private theorem r0_readReg64_setPState_rp (s : State) (ps : PState) (r : Reg) : (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
private theorem r0_sp_setPState_rp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl
private theorem r0_mem_setPState_rp (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by cases s; rfl
private theorem r0_status_setPState_rp (s : State) (ps : PState) : (s.setPState ps).status = s.status := by cases s; rfl
private theorem r0_trace_setPState_rp (s : State) (ps : PState) : (s.setPState ps).trace = s.trace := by cases s; rfl
private theorem r0_symtab_setPState_rp (s : State) (ps : PState) : (s.setPState ps).symtab = s.symtab := by cases s; rfl
private theorem r0_fs_setPState_rp (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
private theorem r0_fs_writeReg64_rp (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
private theorem r0_fs_writeVReg128_rp (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl
private theorem r0_fs_setPC_rp (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by cases s; rfl
private theorem r0_fs_setMem_rp (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem r0_sp_step1_rp (sp0 : BitVec 64) : (sp0 - 96#64) - 4096#64 = sp0 - 4192#64 := by rw [BitVec.sub_sub]; rfl
private theorem r0_sp_step2_rp (sp0 : BitVec 64) : (sp0 - 4192#64) - 4096#64 = sp0 - 8288#64 := by rw [BitVec.sub_sub]; rfl
private theorem r0_sp_step3_rp (sp0 : BitVec 64) : (sp0 - 8288#64) - 2544#64 = sp0 - 0x2a50#64 := by rw [BitVec.sub_sub]; rfl
attribute [local simp, local arm64_norm, local wp_norm]
  r0_extractLsb_append_lo_rp r0_extractLsb_append_hi_rp r0_calleeSavedVRegs_q0_rp r0_calleeSavedVRegs_writeReg64_rp
  r0_calleeSavedVRegs_setPC_rp r0_calleeSavedVRegs_setMem_rp r0_calleeSavedVRegs_setPState_rp
  r0_readReg64_setPState_rp r0_sp_setPState_rp r0_mem_setPState_rp r0_status_setPState_rp r0_trace_setPState_rp
  r0_symtab_setPState_rp r0_fs_setPState_rp r0_fs_writeReg64_rp r0_fs_writeVReg128_rp
  r0_fs_setPC_rp r0_fs_setMem_rp r0_sp_step1_rp r0_sp_step2_rp r0_sp_step3_rp
private theorem r0_spAligned_rp {s0 s : State} (h0 : s0.spAligned = true) (hsp : s.sp = runFsp s0) : s.spAligned = true := by
  have h1 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 0x2a50#64 h0
  show (s.sp &&& 15#64 == 0#64) = true; rwa [hsp]
private theorem r0_sepWPp_drop_left_rp {prog : Program} {ret : BitVec 64} {s : State} {Drop Keep : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : SepWPp prog ret s Keep Q Qp oom) : SepWPp prog ret s (Drop ∗ Keep) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc] at hm; exact h R (Satisfies.of_sep_right hm) hL
private theorem r0_sepWPp_exists_all_rp {α : Type} {prog : Program} {ret : BitVec 64} {s : State} {Φ : α → SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : ∀ x : α, SepWPp prog ret s (Φ x) Q Qp oom) : SepWPp prog ret s (∃∗ x : α, Φ x) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨x, hmx⟩; exact h x R hmx hL
private theorem r0_sepWPp_exists_left_rp {α : Type} {prog : Program} {ret : BitVec 64} {s : State} {Φ : α → SepProp} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : ∀ x : α, SepWPp prog ret s (Φ x ∗ F) Q Qp oom) : SepWPp prog ret s ((∃∗ x : α, Φ x) ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩; exact h x R (by simpa only [sepConj_assoc] using hmx) hL
private theorem r0_sepWPp_pure_left_rp {prog : Program} {ret : BitVec 64} {s : State} {φ : Prop} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : φ → SepWPp prog ret s F Q Qp oom) : SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact h hm.1 R hm.2 hL
private theorem r0_frame_seq_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P_in P P' F : SepProp} {post : State → Prop} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp} (hinv : CodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, CodeOk s1.mem → s1.pc = mid → s1.status = .Running → post s1 → SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) := by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ := hk s1 (LsCodeInv.of_keepsFrozen hinv hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
      (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim
private theorem r0_call_rocl_steps_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {α : Type}
    {H : LibsignalHooks} {entry ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} (x : α) (hcall : subroutine_ok (runProgPlaced H) entry (withLsRoCl lsmpl spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', Steps (runProgPlaced H) s sf → sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R := Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsRoCl]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨LsCodeInv.toRoCl hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsRoCl] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hsteps (LsCodeInv.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost.2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsRoCl] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F, by simpa only [sepConj_assoc] using hpost, hpanic sm (F ∗ R) hsteps hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsRoCl] at hpost; exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩
private theorem r0_call_lscro_steps_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {α : Type}
    {H : LibsignalHooks} {entry ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) entry (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', Steps (runProgPlaced H) s sf → sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) :=
  r0_call_rocl_steps_rp x (LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded hcall) hinv hpc hrun hsp hlr hP hpanic hexit hoom hnext
private theorem r0_files_eq_of_trace_eq_rp {prog : Program} {s sf : State} (hfs : TraceFsSound prog) (hsteps : Steps prog s sf) (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  files_eq_at_callback ((withFsInv_entry s).of_steps hfs hsteps) (by rw [htr, List.append_nil]) (fun _ h => by cases h)
private theorem r0_own_wrOk_rp : cliWrOk (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) := by
  apply cliWrOk_own
  · rw [r0_utf8_address_rp]; refine ⟨?_, ⟨0x61#8, List.Mem.head _, by decide⟩⟩
    rintro b hb; rcases hb with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hb⟩⟩⟩⟩⟩⟩⟩
    all_goals first | decide | cases hb
  · rw [r0_utf8_address_rp]; decide
private theorem r0_call_not_keygen_rp [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem} {g : RunCall}
    {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) : ∀ me n, g.c ≠ .keygen me n := by
  intro me n hkg; rcases he.rel.1 with ⟨_, cmd, _, hargv⟩; have hp := he.parse; rw [hargv, hkg] at hp
  have hb_i : bytesOfString "init" = [0x69#8, 0x6e#8, 0x69#8, 0x74#8] := by rfl_kernel
  have hb_s : bytesOfString "send" = [0x73#8, 0x65#8, 0x6e#8, 0x64#8] := by rfl_kernel
  have hb_r : bytesOfString "recv" = [0x72#8, 0x65#8, 0x63#8, 0x76#8] := by rfl_kernel
  have hu_i : utf8 "init" = [0x69#8, 0x6e#8, 0x69#8, 0x74#8] := by rfl_kernel
  have hu_s : utf8 "send" = [0x73#8, 0x65#8, 0x6e#8, 0x64#8] := by rfl_kernel
  have hu_r : utf8 "recv" = [0x72#8, 0x65#8, 0x63#8, 0x76#8] := by rfl_kernel
  have hu_k : utf8 "keygen" = [0x6b#8, 0x65#8, 0x79#8, 0x67#8, 0x65#8, 0x6e#8] := by rfl_kernel
  cases cmd <;> simp [Cmd.argv, parseArgs, hb_i, hb_s, hb_r, hu_i, hu_s, hu_r, hu_k] at hp
private theorem r0_sepProp_ext_rp {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q := Entails.antisymm h1 h2
private theorem r0_apply_head_rp {A B F P : SepProp} (h : A ⊢ B) (heq : P = A ∗ F) : P ⊢ B ∗ F := by rw [heq]; exact sepConj_mono_left h
private def r0_gaps_rp (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) (0x4d0 - 0x1e0) ∗
    memRegion (fsp + 0x500#64) (0x1750 - 0x500) ∗ memRegion (fsp + 0x1770#64) (runLocalBytes - 0x1770)
attribute [local irreducible] r0_gaps_rp

private def r0_storesRest_rp (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x28#64) g.identity.peers ∗ dirAt A (a + 0x50#64) g.signed ∗ dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗ dirAt A (a + 0xc8#64) g.oneTime ∗ dirAt A (a + 0xf0#64) g.sessions ∗ dirAt A (a + 0x118#64) g.pub
private theorem r0_storesAt_eq_rp (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : storesAt A a g = dirAt A a g.identity.own ∗ r0_storesRest_rp A a g := rfl
private theorem r0_memRegion_8_24_rp (a : BitVec 64) : memRegion a 32 = memRegion a 8 ∗ memRegion (a + 8#64) 24 :=
  ProofLib.memRegion_split a 8 24 (by decide)
private theorem r0_memRegion_two_words_rp (a : BitVec 64) :
    memRegion a 16 = (∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64, (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
private theorem r0_two_words_entails_memRegion_rp (a u0 u1 : BitVec 64) : (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ⊢ memRegion a 16 := by
  rw [r0_memRegion_two_words_rp a]; exact Entails.sepExists_right u1 (Entails.sepExists_right u0 (Entails.refl _))
private theorem r0_three_words_entails_24_rp (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  have h1 := ProofLib.memRegion_split a 8 16 (by decide); have ha : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h1, ← ha]; exact sepConj_mono (pointsTo64_entails_memRegion a w0) (r0_two_words_entails_memRegion_rp _ w1 w2)
private theorem r0_four_words_entails_32_rp (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢ memRegion a 32 := by
  have h1 := ProofLib.memRegion_split a 8 24 (by decide)
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  rw [h1, ← ha16, ← ha24]; exact sepConj_mono (pointsTo64_entails_memRegion a w0) (r0_three_words_entails_24_rp _ w1 w2 w3)
private theorem r0_memRegion_12_cells_rp (b : BitVec 64) :
    memRegion b 0x60 = (∃∗ v11 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v8 : BitVec 64,
      ∃∗ v7 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        (b ↦₆₄ v0) ∗ ((b + 0x08#64) ↦₆₄ v1) ∗ ((b + 0x10#64) ↦₆₄ v2) ∗ ((b + 0x18#64) ↦₆₄ v3) ∗ ((b + 0x20#64) ↦₆₄ v4) ∗ ((b + 0x28#64) ↦₆₄ v5) ∗
        ((b + 0x30#64) ↦₆₄ v6) ∗ ((b + 0x38#64) ↦₆₄ v7) ∗ ((b + 0x40#64) ↦₆₄ v8) ∗ ((b + 0x48#64) ↦₆₄ v9) ∗ ((b + 0x50#64) ↦₆₄ v10) ∗ ((b + 0x58#64) ↦₆₄ v11)) := by
  have step (a : BitVec 64) (k : Nat) (hk : 8 + k ≤ 2 ^ 64) : memRegion a (8 + k) = (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ memRegion (a + 8#64) k := by
    rw [ProofLib.memRegion_split a 8 k hk, ProofLib.memRegion_eight]
  rw [step b 88 (by decide), step _ 80 (by decide), step _ 72 (by decide), step _ 64 (by decide), step _ 56 (by decide), step _ 48 (by decide),
    step _ 40 (by decide), step _ 32 (by decide), step _ 24 (by decide), step _ 16 (by decide), step _ 8 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
private theorem r0_memRegion_saved_open_rp (s0 : State) :
    memRegion (s0.sp - 0x60#64) 0x60 = (∃∗ v11 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v8 : BitVec 64,
      ∃∗ v7 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        ((s0.sp - 0x60#64) ↦₆₄ v0) ∗ ((s0.sp - 0x58#64) ↦₆₄ v1) ∗ ((s0.sp - 0x50#64) ↦₆₄ v2) ∗ ((s0.sp - 0x48#64) ↦₆₄ v3) ∗
        ((s0.sp - 0x40#64) ↦₆₄ v4) ∗ ((s0.sp - 0x38#64) ↦₆₄ v5) ∗ ((s0.sp - 0x30#64) ↦₆₄ v6) ∗ ((s0.sp - 0x28#64) ↦₆₄ v7) ∗
        ((s0.sp - 0x20#64) ↦₆₄ v8) ∗ ((s0.sp - 0x18#64) ↦₆₄ v9) ∗ ((s0.sp - 0x10#64) ↦₆₄ v10) ∗ ((s0.sp - 0x08#64) ↦₆₄ v11)) := by
  rw [r0_memRegion_12_cells_rp (s0.sp - 0x60#64), ProofLib.bv_sub_add_lit s0.sp 0x60 0x08, ProofLib.bv_sub_add_lit s0.sp 0x60 0x10,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x18, ProofLib.bv_sub_add_lit s0.sp 0x60 0x20, ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x30, ProofLib.bv_sub_add_lit s0.sp 0x60 0x38, ProofLib.bv_sub_add_lit s0.sp 0x60 0x40,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x48, ProofLib.bv_sub_add_lit s0.sp 0x60 0x50, ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]
private theorem r0_subStack_split_rp (fsp : BitVec 64) {sub k : Nat} (hle : k ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt fsp sub = memRegion (fsp - BitVec.ofNat 64 sub) (sub - k) ∗ stackAt fsp k := by
  have h := ProofLib.stackAt_split_bottom fsp k (sub - k) (by omega); rwa [show k + (sub - k) = sub by omega] at h
private theorem r0_frame3_split_rp (fsp : BitVec 64) :
    memRegion fsp runLocalBytes = r0_gaps_rp fsp ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x1750#64) 32 := by
  unfold r0_gaps_rp
  have s1 := ProofLib.memRegion_split fsp 0x1d0 (runLocalBytes - 0x1d0) (by decide)
  have s2 := ProofLib.memRegion_split (fsp + 0x1d0#64) 16 (runLocalBytes - 0x1e0) (by decide)
  have s3 := ProofLib.memRegion_split (fsp + 0x1e0#64) (0x4d0 - 0x1e0) (runLocalBytes - 0x4d0) (by decide)
  have s4 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 (runLocalBytes - 0x500) (by decide)
  have s5 := ProofLib.memRegion_split (fsp + 0x500#64) (0x1750 - 0x500) (runLocalBytes - 0x1750) (by decide)
  have s6 := ProofLib.memRegion_split (fsp + 0x1750#64) 32 (runLocalBytes - 0x1770) (by decide)
  simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5 s6
  rw [show runLocalBytes = 0x1d0 + (runLocalBytes - 0x1d0) from rfl, s1, show runLocalBytes - 0x1d0 = 16 + (runLocalBytes - 0x1e0) from rfl, s2,
    show runLocalBytes - 0x1e0 = (0x4d0 - 0x1e0) + (runLocalBytes - 0x4d0) from rfl, s3, show runLocalBytes - 0x4d0 = 48 + (runLocalBytes - 0x500) from rfl, s4,
    show runLocalBytes - 0x500 = (0x1750 - 0x500) + (runLocalBytes - 0x1750) from rfl, s5, show runLocalBytes - 0x1750 = 32 + (runLocalBytes - 0x1770) from rfl, s6]
  ac_rfl
private theorem r0_frame3_rejoin_rp (fsp : BitVec 64) :
    r0_gaps_rp fsp ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x1750#64) 32 = runLocals fsp [] := by
  rw [runLocals_empty_eq, ← r0_frame3_split_rp fsp]
private theorem r0_probes_split_rp (s0 : State) :
    memRegion (runFsp s0) runLocalBytes = (∃∗ p2 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p0 : BitVec 64,
      ((s0.sp - 0x2a50#64) ↦₆₄ p0) ∗ ((s0.sp - 8288#64) ↦₆₄ p1) ∗ ((s0.sp - 4192#64) ↦₆₄ p2) ∗
      memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗ memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) := by
  have c1 := ProofLib.memRegion_split (runFsp s0) 8 (runLocalBytes - 8) (by decide)
  have c2 := ProofLib.memRegion_split (runFsp s0 + 0x08#64) (0x9f0 - 8) (runLocalBytes - 0x9f0) (by decide)
  have c3 := ProofLib.memRegion_split (runFsp s0 + 0x9f0#64) 8 (runLocalBytes - 0x9f8) (by decide)
  have c4 := ProofLib.memRegion_split (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) (runLocalBytes - 0x19f0) (by decide)
  have c5 := ProofLib.memRegion_split (runFsp s0 + 0x19f0#64) 8 (runLocalBytes - 0x19f8) (by decide)
  simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at c1 c2 c3 c4 c5
  rw [show runLocalBytes = 8 + (runLocalBytes - 8) from rfl, c1, show runLocalBytes - 8 = (0x9f0 - 8) + (runLocalBytes - 0x9f0) from rfl, c2,
    show runLocalBytes - 0x9f0 = 8 + (runLocalBytes - 0x9f8) from rfl, c3, show runLocalBytes - 0x9f8 = (0x19f0 - 0x9f8) + (runLocalBytes - 0x19f0) from rfl, c4,
    show runLocalBytes - 0x19f0 = 8 + (runLocalBytes - 0x19f8) from rfl, c5]
  have ha1 : runFsp s0 + 0x9f0#64 = s0.sp - 8288#64 := ProofLib.bv_sub_add_lit s0.sp 0x2a50 0x9f0
  have ha2 : runFsp s0 + 0x19f0#64 = s0.sp - 4192#64 := ProofLib.bv_sub_add_lit s0.sp 0x2a50 0x19f0
  rw [ha1, ha2, show runFsp s0 = s0.sp - 0x2a50#64 from rfl, ProofLib.memRegion_eight (s0.sp - 0x2a50#64),
    ProofLib.memRegion_eight (s0.sp - 8288#64), ProofLib.memRegion_eight (s0.sp - 4192#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; repeat (apply sepExists_congr; intro _)
  ac_rfl
private theorem r0_probes_rejoin_rp (s0 : State) :
    ((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
      memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗ memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8) ⊢
    memRegion (runFsp s0) runLocalBytes := by
  rw [r0_probes_split_rp s0]; exact Entails.sepExists_right 0#64 (Entails.sepExists_right 0#64 (Entails.sepExists_right 0#64 (Entails.refl _)))
private def r0_ownedRest_rp (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
private theorem r0_ownedBytes_split_rp (A : RustAlloc) (cap ptr len : BitVec 64) (bs : Bytes) :
    ownedBytes A cap ptr len bs ⊢ ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ (ptr ↦ₛ bs) ∗ r0_ownedRest_rp A cap ptr bs := by
  unfold ownedBytes r0_ownedRest_rp; apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  by_cases hcap : cap = 0
  · subst hcap; have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil; simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  · simp only [hcap, ↓reduceIte]
    exact Entails.pure_right hlen (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))))
private theorem r0_ownedBytes_free_rp (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) :
    (ptr ↦ₛ bs) ∗ r0_ownedRest_rp A cap ptr bs ⊢
      if cap = 0 then emp else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold r0_ownedRest_rp; rw [sepConj_left_comm (ptr ↦ₛ bs)]; apply Entails.pure_left; rintro ⟨hle, hlt, _⟩
  by_cases hcap : cap = 0
  · subst hcap; have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil; simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hpos : 0 < cap.toNat := by by_contra h0; exact hcap (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
    have hm : (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢ memRegion ptr cap.toNat := by
      have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
      rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
      rw [hsplit]; exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr bs)
    exact Entails.pure_right hlay (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hm))
private theorem r0_addrUpperAt_open_rp (a : BitVec 64) (meG : AddrGhost) :
    addrUpperAt a meG ⊢ ∃∗ w1 : BitVec 64, ⌜w1.setWidth 8 = meG.device⌝ ∗
      (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1) := by
  unfold addrUpperAt
  have step1 (p : BitVec 64) (k : Nat) (hk : 1 + k ≤ 2 ^ 64) : memRegion p (1 + k) = (∃∗ b : BitVec 8, p ↦₈ b) ∗ memRegion (p + 1#64) k := by
    rw [ProofLib.memRegion_split p 1 k hk, Path.Helpers.memRegion_1_eq_pointsTo8 p]
  rw [step1 (a + 9#64) 6 (by decide), step1 _ 5 (by decide), step1 _ 4 (by decide), step1 _ 3 (by decide),
    step1 _ 2 (by decide), step1 _ 1 (by decide), Path.Helpers.memRegion_1_eq_pointsTo8 _]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro b7; apply Entails.sepExists_elim; intro b6; apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4; apply Entails.sepExists_elim; intro b3; apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  let w1 : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ meG.device
  refine Entails.sepExists_right w1 ?_
  have hw_lo : w1.setWidth 8 = meG.device := by dsimp [w1]; bv_bits
  have hunpack : unpack64 w1 = [meG.device, b1, b2, b3, b4, b5, b6, b7] := ProofLib.unpack64_pack64 meG.device b1 b2 b3 b4 b5 b6 b7
  have hword : ((a + 8#64) ↦₆₄ w1) = ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦₈ b1) ∗ ((a + 10#64) ↦₈ b2) ∗
      ((a + 11#64) ↦₈ b3) ∗ ((a + 12#64) ↦₈ b4) ∗ ((a + 13#64) ↦₈ b5) ∗ ((a + 14#64) ↦₈ b6) ∗ ((a + 15#64) ↦₈ b7) := by
    rw [pointsTo64_eq_pointsToBytes, hunpack]; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hword]; exact Entails.pure_right hw_lo (Entails.of_eq (by ac_rfl))
private theorem r0_addrUpperAt_close_rp (b w1 : BitVec 64) (meG : AddrGhost) (hw1 : w1.setWidth 8 = meG.device) :
    (b ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((b + 8#64) ↦₆₄ w1) ⊢ addrUpperAt b meG := by
  unfold addrUpperAt
  have hcons : unpack64 w1 = meG.device :: (unpack64 w1).tail := by
    have h0 : w1.extractLsb' 0 8 = meG.device := by rw [← hw1]; bv_bits
    dsimp [unpack64]; rw [h0]
  have hword : ((b + 8#64) ↦₆₄ w1) ⊢ ((b + 8#64) ↦₈ meG.device) ∗ memRegion (b + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes, hcons, pointsToBytes_cons, show (b + 8#64) + 1#64 = b + 9#64 by bv_omega, show (7 : Nat) = (unpack64 w1).tail.length from rfl]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion _ _)
  exact sepConj_mono_right hword
set_option maxHeartbeats 800000 in
private theorem r0_frame3_rejoin_some_rp (fsp : BitVec 64) (meG : AddrGhost) :
    (memRegion (fsp + 0x1750#64) 32 ∗ addrUpperAt (fsp + 0x1d0#64) meG) ∗ r0_gaps_rp fsp ∗ memRegion (fsp + 0x4d0#64) 48 ⊢
    runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] := by
  unfold r0_gaps_rp
  have htail : memRegion (fsp + 0x1e0#64) (runLocalBytes - 0x1e0) =
      memRegion (fsp + 0x1e0#64) (0x4d0 - 0x1e0) ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) (0x1750 - 0x500) ∗
      memRegion (fsp + 0x1750#64) 32 ∗ memRegion (fsp + 0x1770#64) (runLocalBytes - 0x1770) := by
    have s3 := ProofLib.memRegion_split (fsp + 0x1e0#64) (0x4d0 - 0x1e0) (runLocalBytes - 0x4d0) (by decide)
    have s4 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 (runLocalBytes - 0x500) (by decide)
    have s5 := ProofLib.memRegion_split (fsp + 0x500#64) (0x1750 - 0x500) (runLocalBytes - 0x1750) (by decide)
    have s6 := ProofLib.memRegion_split (fsp + 0x1750#64) 32 (runLocalBytes - 0x1770) (by decide)
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at s3 s4 s5 s6
    rw [show runLocalBytes - 0x1e0 = (0x4d0 - 0x1e0) + (runLocalBytes - 0x4d0) from rfl, s3,
      show runLocalBytes - 0x4d0 = 48 + (runLocalBytes - 0x500) from rfl, s4,
      show runLocalBytes - 0x500 = (0x1750 - 0x500) + (runLocalBytes - 0x1750) from rfl, s5,
      show runLocalBytes - 0x1750 = 32 + (runLocalBytes - 0x1770) from rfl]
    exact s6 ▸ rfl
  dsimp only [runLocals, runLocalsFrom]
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero fsp, show BitVec.ofNat 64 (0x1d0 + 16) = 0x1e0#64 from rfl,
    show 0x1d0 - 0 = 0x1d0 from rfl, show runLocalBytes - (0x1d0 + 16) = runLocalBytes - 0x1e0 from rfl, htail]
  exact Entails.of_eq (by ac_rfl)
private theorem r0_vecU8_eq_rp (A : RustAlloc) (p : BitVec 64) (bs : Bytes) :
    vecU8 A p bs = ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
      (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecU8 vecU8At vecHeader ownedBytes; apply r0_sepProp_ext_rp
  · apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
    exact Entails.sepExists_right ptr (Entails.sepExists_right cap (Entails.of_eq (by simp only [true_and, sepConj_assoc])))
  · apply Entails.sepExists_elim; intro ptr; apply Entails.sepExists_elim; intro cap
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by simp only [true_and, sepConj_assoc])))
private theorem r0_speInvalidState_eq_words_rp (A : RustAlloc) (fnName : Bytes) (a : BitVec 64) :
    speAt A fnName a .invalidState = ∃∗ fnPtr : BitVec 64, ∃∗ bs : Bytes, ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
      (a ↦₆₄ speWord 1) ∗ ((a + 0x08#64) ↦₆₄ cap) ∗ ((a + 0x10#64) ↦₆₄ ptr) ∗ ((a + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((a + 0x20#64) ↦₆₄ fnPtr) ∗ ((a + 0x28#64) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗ (fnPtr ↦ᵣ fnName) ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold speAt strRefAt
  have ha16 : (a + 0x08#64) + 8#64 = a + 0x10#64 := by bv_omega
  have ha24 : (a + 0x08#64) + 16#64 = a + 0x18#64 := by bv_omega
  have ha40 : (a + 0x20#64) + asm64% boxSliceLenOff = a + 0x28#64 := by bv_omega
  rw [show a + asm64% spePayloadOff = a + 0x08#64 from rfl, show a + asm64% speInvalidStateFnOff = a + 0x20#64 from rfl]
  simp only [r0_vecU8_eq_rp, ha16, ha24, ha40, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply sepExists_congr; intro _)
  ac_rfl
private theorem r0_decResultOk_eq_words_rp (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecResultAt A a (.ok bs) = ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
      ((a ↦₆₄ okTagVec) ∗ ((a + 0x08#64) ↦₆₄ cap) ∗ ((a + 0x10#64) ↦₆₄ ptr) ∗ ((a + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      memRegion (a + 0x20#64) 16 ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecResultAt
  have ha16 : (a + 0x08#64) + 8#64 = a + 0x10#64 := by bv_omega
  have ha24 : (a + 0x08#64) + 16#64 = a + 0x18#64 := by bv_omega
  rw [show a + asm64% decResultVecOff = a + 0x08#64 from rfl, show a + asm64% (decResultVecOff + vecSize) = a + 0x20#64 from rfl,
    show asm% (speSize - (decResultVecOff + vecSize)) = 16 from rfl]
  simp only [r0_vecU8_eq_rp, ha16, ha24, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply sepExists_congr; intro _)
  ac_rfl
private abbrev r0_constFrame_rp [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (s0 : State) : SepProp :=
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0
private def r0_meRegs_rp (me : MeAtDispatch) (s : State) : Prop :=
  match me with
  | .none => s.readReg64 (.gpr 21#5) = noneCap
  | .some meV meG => s.readReg64 (.gpr 21#5) = meG.name.cap ∧ s.readReg64 (.gpr 28#5) = meG.name.ptr ∧
      meG.name.bytes = meV.name ∧ meG.name.cap = BitVec.ofNat 64 meV.name.length ∧ meG.device = meV.device
private def r0_ownSem_rp (g : RunCall) (me : MeAtDispatch) : Prop :=
  ∃ ownB : Bytes, StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    match me with | .none => addrParse uuidTryParse ownB = Option.none | .some meV _ => addrParse uuidTryParse ownB = Option.some meV
private def r0_tagRel_rp (w0 : BitVec 64) (tag : Nat) : Prop :=
  (w0.toNat < 2 ^ 63 ∧ tag = 1) ∨ (w0 = 0x8000000000000002#64 ∧ tag = 2) ∨ (w0 = 0x8000000000000003#64 ∧ tag = 3)
private theorem r0_cmn_some_eq_false_rp {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    ConditionHolds .EQ (AddWithCarry64 cap 1#64 false).2 = false ∧ (cap + 1#64 == 0#64) = false := by
  have hne : cap + 1#64 ≠ 0#64 := by
    intro h; have hmax : cap = 0xffffffffffffffff#64 := by bv_omega
    subst hmax; have htop : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := rfl; rw [htop] at hcap; omega
  have hbeq : (cap + 1#64 == 0#64) = false := beq_false_of_ne hne
  refine ⟨?_, hbeq⟩; dsimp [ConditionHolds, AddWithCarry64]
  have hbw : BitVec.setWidth 64 (0#65 + (1#65 + BitVec.setWidth 65 cap)) = cap + 1#64 := by bv_bits
  rw [hbw]; exact hbeq
private theorem r0_lift_pure_7_rp {φ : Prop} {H0 : SepProp} (a0 a1 a2 a3 a4 a5 a6 : SepProp) (h : H0 ⊢ ⌜φ⌝ ∗ H0) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ H0 ⊢ ⌜φ⌝ ∗ (a0 ∗ (a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ H0)) := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h))))))) ?_
  exact Entails.of_eq (by simp only [sepConj_left_comm _ ⌜φ⌝])
private theorem r0_callAt_peek_w0_rp [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) (A : RustAlloc) :
    callAt A g.call g.c ⊢ ∃∗ w : CallW, ⌜r0_tagRel_rp w.w0 g.c.tag⌝ ∗ (g.call ↦₆₄ w.w0) ∗
      (((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
        ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6) ∗ callHeap A w g.c) := by
  cases hgc : g.c with
  | keygen me0 n0 => exact (r0_call_not_keygen_rp he me0 n0 hgc).elim
  | init peer dir =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap, addrWords]
    have hob : ownedBytes A w.w0 w.w1 w.w2 peer.name ⊢ ⌜r0_tagRel_rp w.w0 (CallV.init peer dir).tag⌝ ∗ ownedBytes A w.w0 w.w1 w.w2 peer.name := by
      unfold ownedBytes; apply Entails.pure_left; rintro ⟨hw2, hle, hlt, hne⟩
      exact Entails.pure_right (Or.inl ⟨hlt, rfl⟩) (Entails.pure_right ⟨hw2, hle, hlt, hne⟩ (Entails.refl _))
    exact Entails.trans (sepConj_mono_left (sepConj_mono_left hob)) (Entails.of_eq (by simp only [sepConj_assoc]))
  | send peer =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap]; apply Entails.pure_left; intro hw0
    exact Entails.pure_right (Or.inr (Or.inl ⟨hw0, rfl⟩)) (Entails.pure_right hw0 (Entails.refl _))
  | recv peer =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap]; apply Entails.pure_left; intro hw0
    exact Entails.pure_right (Or.inr (Or.inr ⟨hw0, rfl⟩)) (Entails.pure_right hw0 (Entails.refl _))
/-! ## Straight-Line and Branching Segment Lemmas -/

private theorem r0_step_dispatch_tail_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal callPtr w0 : BitVec 64} {tag : Nat} (hpc : s.pc = runPcPlaced 504) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hx25 : s.readReg64 (.gpr 25#5) = callPtr) (htag : r0_tagRel_rp w0 tag) :
    SepWP (runProgPlaced H) (runPcPlaced 532) s (callPtr ↦₆₄ w0) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 (.gpr 8#5) = BitVec.ofNat 64 tag ∧ s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧ s1.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧ s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = callPtr ∧ s1.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
        s1.readReg64 (.gpr 27#5) = fsp + 0x1750#64 ∧ s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)) ∧ P1 = (callPtr ↦₆₄ w0))
      (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 504#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩, rfl⟩
  · rcases htag with ⟨hlt, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
      have hbw1 : BitVec.setWidth 64 (1#65 + (0xffffffffffffffff#65 + BitVec.setWidth 65 w0)) = w0 := by bv_bits
      have hbw2 : BitVec.setWidth 64 (BitVec.setWidth 65 w0 + 0xffffffffffffffff#65 + 1#65) = w0 := by bv_bits
      have hbw3 : BitVec.setWidth 64 (BitVec.setWidth 65 w0 + 0xffffffffffffffff#65 + 0x1#65) = w0 := hbw2
      simp only [hbw1, hbw2, hbw3, BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega : 2 * w0.toNat < 2 ^ 64), Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
  · r0_close_post_rp
private theorem r0_step_dealloc_pre_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr cap : BitVec 64} (hpc : s.pc = runPcPlaced 488) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap) :
    SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧
      s1.readReg64 .lr = runPcPlaced 504 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
      s1.readReg64 .x0 = ptr ∧ s1.readReg64 .x1 = cap ∧ s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      s1.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)) ∧ P1 = emp) (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 488#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp
private theorem r0_step_post_none_zero_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal : BitVec 64} (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64) :
    SepWP (runProgPlaced H) (runPcPlaced 504) s ((fsp + 0x1750#64) ↦₆₄ noneCap) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = noneCap ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)) ∧
        P1 = ((fsp + 0x1750#64) ↦₆₄ noneCap)) (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [noneCap]; rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp
private theorem r0_step_post_none_nz_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr cap : BitVec 64} (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap) (hcap0 : cap ≠ 0#64) :
    SepWP (runProgPlaced H) (runPcPlaced 488) s ((fsp + 0x1750#64) ↦₆₄ noneCap) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = noneCap ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧ P1 = ((fsp + 0x1750#64) ↦₆₄ noneCap)) (fun _ => ⌜False⌝) := by
  subst hsp; have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
  dsimp only [noneCap]; rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp
private theorem r0_step_post_some_zero_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal mCap mPtr mLen w1 u0 u1 : BitVec 64} (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64) (hlt : mCap.toNat < 2 ^ 63) :
    SepWP (runProgPlaced H) (runPcPlaced 504) s
      (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ mLen) ∗
        ((fsp + 0x1768#64) ↦₆₄ w1) ∗ ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = mCap ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧ s1.readReg64 (.gpr 28#5) = mPtr) ∧
        P1 = (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ mLen) ∗
          ((fsp + 0x1768#64) ↦₆₄ w1) ∗ ((fsp + 0x1d0#64) ↦₆₄ mLen) ∗ ((fsp + 0x1d8#64) ↦₆₄ w1))) (fun _ => ⌜False⌝) := by
  subst hsp; have hcmn_eq := (r0_cmn_some_eq_false_rp hlt).1; have hcmn_f := (r0_cmn_some_eq_false_rp hlt).2
  rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, by ac_rfl⟩; r0_close_post_rp
private theorem r0_step_post_some_nz_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal mCap mPtr mLen w1 u0 u1 ptr cap : BitVec 64} (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap) (hcap0 : cap ≠ 0#64) (hlt : mCap.toNat < 2 ^ 63) :
    SepWP (runProgPlaced H) (runPcPlaced 488) s
      (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ mLen) ∗
        ((fsp + 0x1768#64) ↦₆₄ w1) ∗ ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = mCap ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap ∧ s1.readReg64 (.gpr 28#5) = mPtr) ∧
        P1 = (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ mLen) ∗
          ((fsp + 0x1768#64) ↦₆₄ w1) ∗ ((fsp + 0x1d0#64) ↦₆₄ mLen) ∗ ((fsp + 0x1d8#64) ↦₆₄ w1))) (fun _ => ⌜False⌝) := by
  subst hsp; have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
  have hcmn_eq := (r0_cmn_some_eq_false_rp hlt).1; have hcmn_f := (r0_cmn_some_eq_false_rp hlt).2
  rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, by ac_rfl⟩; r0_close_post_rp

private theorem r0_step_ok_pre_utf8_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal cap ptr lenW : BitVec 64} (hpc : s.pc = runPcPlaced 96) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (runProgPlaced H) (lsρ lsFromUtf8Sym) s
      (((fsp + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 136 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = ptr ∧ s1.readReg64 .x1 = lenW ∧ s1.readReg64 (.gpr 8#5) = fsp + 0x4d0#64 ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = lenW ∧ s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧ s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧
        P1 = (((fsp + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW)))
      (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [okTagVec]; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 96#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp
private theorem r0_step_ok_pre_addr_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr lenW cap : BitVec 64} (hpc : s.pc = runPcPlaced 136) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 (.gpr 21#5) = lenW) (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap) :
    SepWP (runProgPlaced H) (lsmpl.base 580) s ((fsp + 0x4d0#64) ↦₆₄ 0#64) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 460 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = fsp + 0x1750#64 ∧ s1.readReg64 .x1 = ptr ∧ s1.readReg64 .x2 = lenW ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧ s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧ s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧
        P1 = ((fsp + 0x4d0#64) ↦₆₄ 0#64)) (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 136#64 at hpc
  rw [ProofLib.pointsTo64_split32 (s.sp + 0x4d0#64) 0#64]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp
private theorem r0_step_err_pre_drop_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal cap ptr lenW fnPtr fnLenW : BitVec 64} (hpc : s.pc = runPcPlaced 96) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (runProgPlaced H) (blkPl_553).base s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ lenW) ∗ ((fsp + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((fsp + 0x4f8#64) ↦₆₄ fnLenW))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 292 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧ s1.readReg64 .x0 = fsp + 0x4d0#64 ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)) ∧
        P1 = (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ lenW) ∗ ((fsp + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((fsp + 0x4f8#64) ↦₆₄ fnLenW))) (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [speWord]; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 96#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, by ac_rfl⟩; r0_close_post_rp
private theorem r0_mainSaved_eq_sub_rp (s0 : State) : runSaved s0 =
    ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  dsimp only [runSaved, MainHops.mainSaved]
  rw [BitVec.add_zero (s0.sp - 0x60#64), ProofLib.bv_sub_add_lit s0.sp 0x60 0x08, ProofLib.bv_sub_add_lit s0.sp 0x60 0x10,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x18, ProofLib.bv_sub_add_lit s0.sp 0x60 0x20, ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x30, ProofLib.bv_sub_add_lit s0.sp 0x60 0x38, ProofLib.bv_sub_add_lit s0.sp 0x60 0x40,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x48, ProofLib.bv_sub_add_lit s0.sp 0x60 0x50, ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]
set_option maxHeartbeats 800000 in
private theorem r0_step_prologue_rp [LibsignalPlacement] {H : LibsignalHooks} {s0 : State}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 p0 p1 p2 : BitVec 64}
    (hpc : s0.pc = (blkPl_579).base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    SepWP (runProgPlaced H) (lsmpl.base 589) s0
      (((s0.sp - 0x60#64) ↦₆₄ v0) ∗ ((s0.sp - 0x58#64) ↦₆₄ v1) ∗ ((s0.sp - 0x50#64) ↦₆₄ v2) ∗ ((s0.sp - 0x48#64) ↦₆₄ v3) ∗
        ((s0.sp - 0x40#64) ↦₆₄ v4) ∗ ((s0.sp - 0x38#64) ↦₆₄ v5) ∗ ((s0.sp - 0x30#64) ↦₆₄ v6) ∗ ((s0.sp - 0x28#64) ↦₆₄ v7) ∗
        ((s0.sp - 0x20#64) ↦₆₄ v8) ∗ ((s0.sp - 0x18#64) ↦₆₄ v9) ∗ ((s0.sp - 0x10#64) ↦₆₄ v10) ∗ ((s0.sp - 0x08#64) ↦₆₄ v11) ∗
        ((s0.sp - 0x2a50#64) ↦₆₄ p0) ∗ ((s0.sp - 8288#64) ↦₆₄ p1) ∗ ((s0.sp - 4192#64) ↦₆₄ p2))
      (fun s1 P1 => (s1.sp = runFsp s0 ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧ s1.readReg64 .lr = runPcPlaced 96 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s0.trace ∧ s1.fs = s0.fs ∧
        s1.readReg64 .x0 = runFsp s0 + 0x4d0#64 ∧ s1.readReg64 .x1 = s0.readReg64 .x2 ∧
        s1.readReg64 .x2 = lsρ r0_addrSym_rp ∧ s1.readReg64 .x3 = 7#64 ∧ s1.readReg64 (.gpr 19#5) = s0.readReg64 .x2 ∧
        s1.readReg64 (.gpr 20#5) = s0.readReg64 .x0 ∧ s1.readReg64 (.gpr 23#5) = s0.readReg64 .x3 ∧
        s1.readReg64 (.gpr 24#5) = s0.readReg64 .x4 ∧ s1.readReg64 (.gpr 25#5) = s0.readReg64 .x1) ∧
        P1 = (runSaved s0 ∗ ((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64)))
      (fun _ => ⌜False⌝) := by
  have hal_0 : (s0.sp &&& 15#64 == 0#64) = true := hsp0
  have hal_96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hal_1060 : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 4192#64 hsp0
  have hal_2060 : ((s0.sp - 8288#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 8288#64 hsp0
  have hal_2a50 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 0x2a50#64 hsp0
  rw [runProgPlaced_eq]; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨⟨by dsimp [runFsp]; simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, runPcPlaced_eq, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by dsimp [runFsp]; simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], ?_⟩, ?_⟩
  · r0_close_post_rp
  · rw [r0_mainSaved_eq_sub_rp s0]; ac_rfl
/-! ## Post-Address and Dispatch Composition Lemmas -/

private theorem r0_dispatch_tail_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {me : MeAtDispatch}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x1f8)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp) (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (hmeRegs : r0_meRegs_rp me s) (hownSem : r0_ownSem_rp g me)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (me' : MeAtDispatch), AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s' (dispatchMemPlaced A g me' s0 resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (dispatchMemPlaced A g me s0 resStack) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur; have hpeek := r0_callAt_peek_w0_rp he A
  dsimp only [dispatchMemPlaced]
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_right (sepConj_mono_left hpeek))
    (Entails.of_eq (by simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl))) ?_
  apply r0_sepWPp_exists_all_rp; intro w; apply r0_sepWPp_pure_left_rp; intro htag
  let callRest : SepProp := ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
      ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6) ∗ callHeap A w g.c
  let dispRest : SepProp := memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
      dispatchMeHeap A me ∗ runSaved s0 ∗ runLocals (runFsp s0) (dispatchCells (runFsp s0) me) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool
  refine r0_frame_seq_rp hbase.inv (F := callRest ∗ dispRest) (Entails.of_eq (by dsimp only [callRest, dispRest]; ac_rfl))
    (r0_step_dispatch_tail_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx25 htag) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  have hpack : (g.call ↦₆₄ w.w0) ∗ (callRest ∗ dispRest) ⊢ dispatchMemPlaced A g me s0 resStack := by
    dsimp only [dispatchMemPlaced, callAt, callRest, dispRest]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w (Entails.refl _))))
  refine SepWPp.weaken_pre hpack (hnext s1 me ?_); clear hpack callRest dispRest; rcases hownSem with ⟨ownB, hget_o, hp_o⟩
  exact { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩, x8 := hx8_1, x19 := hx19_1.trans hx19,
          x20 := hx20_1.trans hx20, x23 := hx23_1.trans hx23, x24 := hx24_1.trans hx24, x25 := hx25_1, x26 := hx26_1, x27 := hx27_1,
          meRegs := by clear hp_o; dsimp only [r0_meRegs_rp] at hmeRegs; cases me with
            | none => exact hx21_1.trans hmeRegs
            | some meV meG => exact ⟨hx21_1.trans hmeRegs.1, hx28_1.trans hmeRegs.2.1, hmeRegs.2.2⟩,
          ownSem := ⟨ownB, hget_o, by cases me <;> exact hp_o⟩,
          trace := htr1 ▸ htr, fs := (congrArg FsState.files hfs1).trans hfs, stdout := htr1 ▸ hout }
private theorem r0_dealloc_own_buf_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {me : MeAtDispatch} {cap ptr : BitVec 64}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H)
    (hsub_ext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x1e8)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp) (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hmeRegs : r0_meRegs_rp me s) (hownSem : r0_ownSem_rp g me) (htr : s0.trace <+: s.trace)
    (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) (hlay : LayoutOk cap.toNat 1)
    (hnext : ∀ (s' : State) (me' : MeAtDispatch), AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s' (dispatchMemPlaced A g me' s0 resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s ((A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ dispatchMemPlaced A g me s0 resStack) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  refine r0_frame_seq_rp hbase.inv (F := (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ dispatchMemPlaced A g me s0 resStack)
    (Entails.of_eq (by rw [emp_sepConj])) (r0_step_dealloc_pre_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx28_1⟩
  refine r0_call_rocl_steps_rp (Q := Q) (Qp := Qp) (ptr, cap.toNat, 1) (hh.allocFs.dealloc_rocl (prog := runProgPlaced H) (i := 579))
    hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := r0_constFrame_rp A g s0 ∗ dispatchMeHeap A me ∗ runLocals (runFsp s0) (dispatchCells (runFsp s0) me) ∗
      memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - extHookStack)) (hP := ?_) (hnext := ?_)
  · rw [emp_sepConj]; dsimp [dispatchMemPlaced, r0_constFrame_rp, Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [hsp1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]; conv => rhs; rw [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_1, hx1_1 ▸ rfl, by rw [hx2_1]; rfl, hlay⟩ (Entails.of_eq (by ac_rfl))
  intro s2 _ hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, _, hx28_2, hfp2, hv2⟩
  refine SepWPp.weaken_pre (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗ dispatchMemPlaced A g me s0 resStack)
    (by dsimp [dispatchMemPlaced, r0_constFrame_rp, Spec.keepsFs, rustDeallocExternSpecWithStack]
        rw [hsp1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]; simp only [← sepConj_assoc, pure_sepConj_pure]; exact Entails.of_eq (by ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨hfs2, htr2⟩
  exact r0_dispatch_tail_rp he ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, hbase.spAligned⟩
    (hx19_2.trans (hx19_1.trans hx19)) (hx20_2.trans (hx20_1.trans hx20)) (hx23_2.trans (hx23_1.trans hx23))
    (hx24_2.trans (hx24_1.trans hx24)) (hx25_2.trans (hx25_1.trans hx25))
    (by dsimp only [r0_meRegs_rp] at hmeRegs ⊢; cases me with
        | none => rwa [hx21_2, hx21_1] | some meV meG => rwa [hx21_2, hx21_1, hx28_2, hx28_1])
    hownSem ((htr2.trans htr1) ▸ htr) ((congrArg FsState.files (hfs2.trans hfs1)).trans hfs) ((htr2.trans htr1) ▸ hout) hnext
private theorem r0_pack_dispatch_none_rp [LibsignalPlacement] (A : RustAlloc) (g : RunCall)
    (s0 : State) (resStack : Nat) :
    (((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24) ∗
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0 ⊢
    dispatchMemPlaced A g .none s0 resStack := by
  have hslot32 : ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24 ⊢
      memRegion (runFsp s0 + 0x1750#64) 32 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, r0_memRegion_8_24_rp (runFsp s0 + 0x1750#64),
      show runFsp s0 + 0x1750#64 + 8#64 = runFsp s0 + 0x1758#64 by bv_omega]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  dsimp only [dispatchMemPlaced, r0_constFrame_rp, dispatchMeHeap, dispatchCells]
  rw [← r0_frame3_rejoin_rp (runFsp s0)]
  exact Entails.trans (sepConj_mono_left hslot32) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
private theorem r0_pack_dispatch_some_rp [LibsignalPlacement] (A : RustAlloc) (g : RunCall)
    (meV : AddrV) (meG : AddrGhost) (w1 : BitVec 64) (s0 : State) (resStack : Nat)
    (hw1 : w1.setWidth 8 = meG.device) :
    ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
      ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ∗
      ((runFsp s0 + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      ((runFsp s0 + 0x1d8#64) ↦₆₄ w1) ∗ addrNameHeap A meG ∗ r0_gaps_rp (runFsp s0) ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool ∗ r0_constFrame_rp A g s0 ⊢ dispatchMemPlaced A g (.some meV meG) s0 resStack := by
  have hslot32 :
      ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
        ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ⊢ memRegion (runFsp s0 + 0x1750#64) 32 := by
    rw [show runFsp s0 + 0x1758#64 = (runFsp s0 + 0x1750#64) + 8#64 by bv_omega,
      show runFsp s0 + 0x1760#64 = (runFsp s0 + 0x1750#64) + 16#64 by bv_omega,
      show runFsp s0 + 0x1768#64 = (runFsp s0 + 0x1750#64) + 24#64 by bv_omega]
    exact r0_four_words_entails_32_rp _ _ _ _ _
  have hup1d0 :
      ((runFsp s0 + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1d8#64) ↦₆₄ w1) ⊢ addrUpperAt (runFsp s0 + 0x1d0#64) meG := by
    rw [show runFsp s0 + 0x1d8#64 = (runFsp s0 + 0x1d0#64) + 8#64 by bv_omega]
    exact r0_addrUpperAt_close_rp _ w1 meG hw1
  dsimp only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
  refine Entails.trans (r0_apply_head_rp (sepConj_mono hslot32 hup1d0)
    (F := addrNameHeap A meG ∗ r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0) (by ac_rfl)) ?_
  refine Entails.trans (r0_apply_head_rp (r0_frame3_rejoin_some_rp (runFsp s0) meG)
    (F := addrNameHeap A meG ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      r0_constFrame_rp A g s0) (by ac_rfl)) ?_
  dsimp only [r0_constFrame_rp]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
private theorem r0_post_address_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {ownB : Bytes}
    {cap ptr : BitVec 64} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hsub_ext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64) (he : AtRunEntryPlaced CodeOk S g s0)
    (hbase : InRunPlaced CodeOk s0 s 0x1cc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (me' : MeAtDispatch), AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s' (dispatchMemPlaced A g me' s0 resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((match addrParse uuidTryParse ownB with
        | none => ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24
        | some a => ∃∗ meG : AddrGhost,
            ⌜meG.name.bytes = a.name ∧ meG.name.cap = BitVec.ofNat 64 a.name.length ∧ meG.device = a.device⌝ ∗
              protocolAddressAt A meG (runFsp s0 + 0x1750#64)) ∗
        ((ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A cap ptr ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  let tail4 : SepProp :=
    r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (r0_ownedBytes_free_rp A cap ptr ownB))) ?_
  cases hparse_own : addrParse uuidTryParse ownB with
  | none =>
    by_cases hcap0 : cap = 0
    · subst hcap0; simp only [↓reduceIte]
      refine r0_frame_seq_rp hbase.inv (F := memRegion (runFsp s0 + 0x1758#64) 24 ∗ tail4)
        (Entails.of_eq (by dsimp only [tail4]; simp only [emp_sepConj]; ac_rfl))
        (r0_step_post_none_zero_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx27) ?_
      rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tail4]; ac_rfl)) (r0_pack_dispatch_none_rp A g s0 resStack))
        (r0_dispatch_tail_rp he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx21_1 ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr)
          ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout) hnext)
    · simp only [hcap0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' := ⌜LayoutOk cap.toNat 1⌝ ∗ (((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗
          (memRegion (runFsp s0 + 0x1758#64) 24 ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tail4)))
        (Entails.of_eq (by dsimp only [tail4]; ac_rfl)) ?_
      apply r0_sepWPp_pure_left_rp; intro hlay
      refine r0_frame_seq_rp hbase.inv
        (F := memRegion (runFsp s0 + 0x1758#64) 24 ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tail4)
        (Entails.refl _)
        (r0_step_post_none_nz_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27 hcap0) ?_
      rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tail4]; ac_rfl))
          (sepConj_mono_right (r0_pack_dispatch_none_rp A g s0 resStack)))
        (r0_dealloc_own_buf_rp hh hsub_ext hsub64 he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx26_1 hx27_1 hx21_1 ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr)
          ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout) hlay hnext)
  | some meV =>
    let freeOpt : SepProp :=
      if cap = 0 then emp else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat
    let tailSome : SepProp :=
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0
    apply r0_sepWPp_exists_left_rp; intro meG
    refine SepWPp.weaken_pre
      (P' := ⌜meG.name.bytes = meV.name ∧ meG.name.cap = BitVec.ofNat 64 meV.name.length ∧ meG.device = meV.device⌝ ∗
        (protocolAddressAt A meG (runFsp s0 + 0x1750#64) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ freeOpt ∗ tailSome))
      (Entails.of_eq (by dsimp only [freeOpt, tailSome]; ac_rfl)) ?_
    apply r0_sepWPp_pure_left_rp; rintro ⟨hme_bytes, hme_cap, hme_dev⟩
    have hheap_pure : addrNameHeap A meG ⊢
        ⌜meG.name.bytes.length ≤ meG.name.cap.toNat ∧ meG.name.cap.toNat < 2 ^ 63 ∧ meG.name.ptr ≠ 0⌝ ∗
          addrNameHeap A meG := by
      unfold addrNameHeap; apply Entails.pure_left; intro hp
      exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
    rw [protocolAddressAt_eq_parts A meG (runFsp s0 + 0x1750#64),
      show (runFsp s0 + 0x1750#64) + 8#64 = runFsp s0 + 0x1758#64 by bv_omega,
      show (runFsp s0 + 0x1750#64) + 16#64 = runFsp s0 + 0x1760#64 by bv_omega,
      r0_memRegion_two_words_rp (runFsp s0 + 0x1d0#64)]
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (r0_addrUpperAt_open_rp (runFsp s0 + 0x1760#64) meG) hheap_pure))))
        (Entails.of_eq (by
          simp only [sepExists_sepConj_left, sepExists_sepConj_right,
            show (runFsp s0 + 0x1760#64) + 8#64 = runFsp s0 + 0x1768#64 by bv_omega,
            show (runFsp s0 + 0x1d0#64) + 8#64 = runFsp s0 + 0x1d8#64 by bv_omega]; ac_rfl))) ?_
    apply r0_sepWPp_exists_all_rp; intro u1; apply r0_sepWPp_exists_all_rp; intro u0
    apply r0_sepWPp_exists_all_rp; intro w1
    let words6 (x0 x1 : BitVec 64) : SepProp :=
      ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
        ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ∗ ((runFsp s0 + 0x1d0#64) ↦₆₄ x0) ∗ ((runFsp s0 + 0x1d8#64) ↦₆₄ x1)
    refine SepWPp.weaken_pre (P' := ⌜w1.setWidth 8 = meG.device⌝ ∗
        (⌜meG.name.bytes.length ≤ meG.name.cap.toNat ∧ meG.name.cap.toNat < 2 ^ 63 ∧ meG.name.ptr ≠ 0⌝ ∗
          (words6 u0 u1 ∗ addrNameHeap A meG ∗ freeOpt ∗ tailSome)))
      (Entails.of_eq (by dsimp only [words6]; ac_rfl)) ?_
    apply r0_sepWPp_pure_left_rp; intro hw1_dev; apply r0_sepWPp_pure_left_rp; rintro ⟨_, hme_lt, _⟩
    dsimp only [freeOpt, tailSome, words6]
    by_cases hcap0 : cap = 0
    · subst hcap0; simp only [↓reduceIte]
      refine r0_frame_seq_rp hbase.inv (F := addrNameHeap A meG ∗ tailSome)
        (Entails.of_eq (by dsimp only [tailSome]; simp only [emp_sepConj]; ac_rfl))
        (r0_step_post_some_zero_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx27 hme_lt) ?_
      rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx28_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tailSome]; ac_rfl))
          (r0_pack_dispatch_some_rp A g meV meG w1 s0 resStack hw1_dev))
        (r0_dispatch_tail_rp he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) ⟨hx21_1, hx28_1, hme_bytes, hme_cap, hme_dev⟩ ⟨ownB, hget, hparse_own⟩
          (htr1 ▸ htr) ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout) hnext)
    · simp only [hcap0, ↓reduceIte]
      refine SepWPp.weaken_pre
        (P' := ⌜LayoutOk cap.toNat 1⌝ ∗
          (words6 u0 u1 ∗ (addrNameHeap A meG ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tailSome)))
        (Entails.of_eq (by dsimp only [words6, tailSome]; ac_rfl)) ?_
      apply r0_sepWPp_pure_left_rp; intro hlay
      refine r0_frame_seq_rp hbase.inv
        (F := addrNameHeap A meG ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tailSome)
        (Entails.refl _)
        (r0_step_post_some_nz_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27 hcap0 hme_lt) ?_
      rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [words6, tailSome]; ac_rfl))
          (sepConj_mono_right (r0_pack_dispatch_some_rp A g meV meG w1 s0 resStack hw1_dev)))
        (r0_dealloc_own_buf_rp hh hsub_ext hsub64 he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx26_1 hx27_1 ⟨hx21_1, hx28_1, hme_bytes, hme_cap, hme_dev⟩
          ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr) ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout)
          hlay hnext)
/-! ## Top-Level `run_hop_pre_placed_ok` -/

set_option maxHeartbeats 800000 in
private theorem r0_ok_utf8_address_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {ownB : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hsub_ext : extHookStack ≤ resStack - runFrame)
    (hsub_addr : 0xB0 + extHookStack ≤ resStack - runFrame)
    (hsub63 : resStack - runFrame ≤ 2 ^ 63) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x60)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) (hpanic : PanicK g s0 Qp)
    (hnext : ∀ (s' : State) (me' : MeAtDispatch), AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s' (dispatchMemPlaced A g me' s0 resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (vecResultAt A (runFsp s0 + 0x4d0#64) (.ok ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  have hascii : ∀ b ∈ ownB, b.toNat < 128 := he.bounds_pre.2 ownB hget
  have hutf8 := RunSkeleton.fromUtf8_placed_ok (callerProg := runProgPlaced H) (i := 579) hh extHookStack
  have haddr := RunSkeleton.runAddress_placed_ok (callerProg := runProgPlaced H) (i := 579)
    hh (resStack - runFrame) hsub_addr hsub63
  let slotsNoStack : SepProp :=
    r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ A.pool ∗ r0_constFrame_rp A g s0
  let restTail : SepProp := stackAt (runFsp s0) (resStack - runFrame) ∗ slotsNoStack
  rw [r0_decResultOk_eq_words_rp A (runFsp s0 + 0x4d0#64) ownB]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply r0_sepWPp_exists_left_rp; intro ptr; apply r0_sepWPp_exists_left_rp; intro cap
  refine SepWPp.weaken_pre
    (P' := ⌜BitVec.ofNat 64 ownB.length = BitVec.ofNat 64 ownB.length⌝ ∗
      ((((runFsp s0 + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length)) ∗
        (memRegion (runFsp s0 + 0x4f0#64) 16 ∗ (ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A cap ptr ownB ∗ restTail)))
    (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (r0_ownedBytes_split_rp A cap ptr (BitVec.ofNat 64 ownB.length) ownB))))
      (Entails.of_eq (by dsimp only [restTail, slotsNoStack]; ac_rfl))) ?_
  apply r0_sepWPp_pure_left_rp; intro _
  refine r0_frame_seq_rp hbase.inv
    (F := memRegion (runFsp s0 + 0x4f0#64) 16 ∗ (ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A cap ptr ownB ∗ restTail)
    (Entails.refl _) (r0_step_ok_pre_utf8_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1⟩
  refine r0_call_lscro_steps_rp (Q := Q) (Qp := Qp) (runFsp s0 + 0x4d0#64, ptr, ownB)
    hutf8 hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
      r0_ownedRest_rp A cap ptr ownB ∗
      memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - extHookStack) ∗
      slotsNoStack)
    (hP := ?_) (hnext := ?_)
  · have h24 : ((runFsp s0 + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ⊢ memRegion (runFsp s0 + 0x4d0#64) 24 := by
      rw [show runFsp s0 + 0x4d8#64 = (runFsp s0 + 0x4d0#64) + 8#64 by bv_omega,
        show runFsp s0 + 0x4e0#64 = (runFsp s0 + 0x4d0#64) + 16#64 by bv_omega]
      exact r0_three_words_entails_24_rp _ _ _ _
    dsimp only [restTail, fromUtf8AsciiSpec]; rw [hsp1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_1, hx1_1, hx8_1, hascii⟩ ?_
    refine Entails.trans (r0_apply_head_rp h24
      (F := (ptr ↦ₛ ownB) ∗ stackAt (runFsp s0) extHookStack ∗
        (((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
          r0_ownedRest_rp A cap ptr ownB ∗
          memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
          slotsNoStack)) (by ac_rfl)) ?_
    exact Entails.of_eq (by ac_rfl)
  intro s2 _ hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, _, hfp2, hv2⟩
  let postUtf8Rest : SepProp :=
    ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
      ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
      (ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A cap ptr ownB ∗ restTail
  refine SepWPp.weaken_pre
    (P' := ⌜s2.trace = s1.trace ∧ s2.fs = s1.fs⌝ ∗ (((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ postUtf8Rest))
    (by dsimp only [postUtf8Rest, restTail, fromUtf8AsciiSpec]
        rw [hsp1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨htr2, hfs2⟩
  have hsp2' : s2.sp = runFsp s0 := hsp2.trans hsp1
  refine r0_frame_seq_rp hinv2 (F := postUtf8Rest) (Entails.refl _)
    (r0_step_ok_pre_addr_rp hpc2 hrun2 hsp2' (r0_spAligned_rp hbase.spAligned hsp2')
      (hfp2.trans hfp1) (hv2.trans hv1) (hx21_2.trans hx21_1) (hx26_2.trans hx26_1) (hx27_2.trans hx27_1)) ?_
  rintro s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3⟩
  have htr_s3 : s0.trace <+: s3.trace := (htr3.trans (htr2.trans htr1)) ▸ htr
  refine r0_call_lscro_steps_rp (Q := Q) (Qp := Qp) ⟨runFsp s0 + 0x1750#64, ptr, ownB⟩
    haddr hinv3 hpc3 hrun3 (r0_spAligned_rp hbase.spAligned hsp3) hlr3
    (F := r0_ownedRest_rp A cap ptr ownB ∗ r0_gaps_rp (runFsp s0) ∗
      memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r0_constFrame_rp A g s0)
    (hP := ?_)
    (hpanic := by
      intro sf R' _ _ hp; dsimp only [addressSpec] at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_s3 hp.1)))
    (hnext := ?_)
  · have h48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
        ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ⊢
        memRegion (runFsp s0 + 0x4d0#64) 48 := by
      have h32 : ((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗
          ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
          ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ⊢ memRegion (runFsp s0 + 0x4d0#64) 32 := by
        rw [show runFsp s0 + 0x4d8#64 = (runFsp s0 + 0x4d0#64) + 8#64 by bv_omega,
          show runFsp s0 + 0x4e0#64 = (runFsp s0 + 0x4d0#64) + 16#64 by bv_omega,
          show runFsp s0 + 0x4e8#64 = (runFsp s0 + 0x4d0#64) + 24#64 by bv_omega]
        exact r0_four_words_entails_32_rp _ _ _ _ _
      rw [show (48 : Nat) = 32 + 16 from rfl, ProofLib.memRegion_split (runFsp s0 + 0x4d0#64) 32 16 (by decide),
        show (runFsp s0 + 0x4d0#64) + 32#64 = runFsp s0 + 0x4f0#64 by bv_omega]
      exact r0_apply_head_rp h32 (by ac_rfl)
    dsimp only [postUtf8Rest, restTail, slotsNoStack, addressSpec]; rw [hsp3]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_3, hx1_3, hx2_3⟩ ?_
    refine Entails.trans (r0_apply_head_rp h48
      (F := (ptr ↦ₛ ownB) ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗ A.pool ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ r0_ownedRest_rp A cap ptr ownB ∗
        r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ r0_constFrame_rp A g s0) (by ac_rfl)) ?_
    exact Entails.of_eq (by ac_rfl)
  intro s4 _ hinv4 hpc4 hrun4 hsp4 hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hfp4, hv4⟩
  refine SepWPp.weaken_pre (P' := ⌜s4.trace = s3.trace ∧ s4.fs = s3.fs⌝ ∗
      ((match addrParse uuidTryParse ownB with
        | none => ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24
        | some a => ∃∗ meG : AddrGhost,
            ⌜meG.name.bytes = a.name ∧ meG.name.cap = BitVec.ofNat 64 a.name.length ∧ meG.device = a.device⌝ ∗
              protocolAddressAt A meG (runFsp s0 + 0x1750#64)) ∗
        ((ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A cap ptr ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0))
    (by dsimp only [addressSpec]; rw [hsp3]
        have ha58 : (runFsp s0 + 0x1750#64) + 8#64 = runFsp s0 + 0x1758#64 := by bv_omega
        cases addrParse uuidTryParse ownB with
        | none => rw [ha58]; exact Entails.of_eq (by dsimp [noneCap]; ac_rfl)
        | some a => dsimp only; exact Entails.of_eq (by ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨htr4, hfs4⟩
  exact r0_post_address_rp hh hsub_ext hsub64 he
    ⟨hpc4, hrun4, hsp4.trans hsp3, hfp4.trans hfp3, hinv4, hv4.trans hv3, hbase.spAligned⟩
    (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
    (hx20_4.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20))))
    (hx23_4.trans (hx23_3.trans (hx23_2.trans (hx23_1.trans hx23))))
    (hx24_4.trans (hx24_3.trans (hx24_2.trans (hx24_1.trans hx24))))
    (hx25_4.trans (hx25_3.trans (hx25_2.trans (hx25_1.trans hx25))))
    (hx26_4.trans hx26_3) (hx27_4.trans hx27_3) hget (htr4 ▸ htr_s3)
    ((congrArg FsState.files (hfs4.trans (hfs3.trans (hfs2.trans hfs1)))).trans hfs)
    ((htr4.trans (htr3.trans (htr2.trans htr1))) ▸ hout) hnext


set_option maxHeartbeats 800000 in
private theorem r0_err_to_reject_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hsub_drop : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced CodeOk s0 s 0x60) (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speAt A (utf8 "read") (runFsp s0 + 0x4d0#64) .invalidState ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  have hdrop_call : subroutine_ok (runProgPlaced H) (blkPl_553).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeOwnedSpec A (resStack - runFrame))) :=
    hdrop (resStack - runFrame) hsub_drop hsub64
  rw [r0_speInvalidState_eq_words_rp A (utf8 "read") (runFsp s0 + 0x4d0#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply r0_sepWPp_exists_left_rp; intro fnPtr; apply r0_sepWPp_exists_left_rp; intro bs
  apply r0_sepWPp_exists_left_rp; intro ptr; apply r0_sepWPp_exists_left_rp; intro cap
  refine r0_frame_seq_rp hbase.inv
    (F := (fnPtr ↦ᵣ utf8 "read") ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs ∗
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0)
    (Entails.of_eq (by ac_rfl)) (r0_step_err_pre_drop_rp hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx19_1, hx20_1, hx25_1⟩
  refine r0_call_lscro_steps_rp (Q := Q) (Qp := Qp)
    ⟨runFsp s0 + 0x4d0#64, .proto (utf8 "read") .invalidState⟩
    hdrop_call hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ r0_constFrame_rp A g s0) (hP := ?_) (hnext := ?_)
  · have hspe : ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((runFsp s0 + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs ⊢
        speOwnedAt A (runFsp s0 + 0x4d0#64) (.proto (utf8 "read") .invalidState) := by
      dsimp only [speOwnedAt]; rw [r0_speInvalidState_eq_words_rp A (utf8 "read") (runFsp s0 + 0x4d0#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.sepExists_right fnPtr (Entails.sepExists_right bs
        (Entails.sepExists_right ptr (Entails.sepExists_right cap (Entails.refl _))))
    dsimp only [dropSpeOwnedSpec]; rw [hsp1]; conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right hx0_1 (Entails.trans (r0_apply_head_rp hspe
      (F := A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        r0_constFrame_rp A g s0) (by ac_rfl)) (Entails.of_eq (by ac_rfl)))
  intro s2 hsteps2 hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, hx25_2, _, _, _, hfp2, hv2⟩
  refine SepWPp.weaken_pre (P' := ⌜s2.trace = s1.trace⌝ ∗ rejectMem A g StoresGhost.opened .preDispatch s0 resStack)
    (by dsimp only [dropSpeOwnedSpec, rejectMem, r0_constFrame_rp]; rw [hsp1, ← r0_frame3_rejoin_rp (runFsp s0)]
        have hany : coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
            SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ⊢ anyHeap := entails_anyHeap _
        exact Entails.trans (r0_apply_head_rp hany (F := ⌜s2.trace = s1.trace⌝ ∗ memRegion g.res runResSize ∗
          callAt A g.call g.c ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) (by ac_rfl)) (Entails.of_eq (by ac_rfl))) ?_
  apply r0_sepWPp_pure_left_rp; intro htr2
  have hfs2_eq : s2.fs.files = s.fs.files :=
    (r0_files_eq_of_trace_eq_rp (hh.fs (lsProg_579 H) 579) hsteps2 htr2).trans (congrArg FsState.files hfs1)
  have htr2_eq : s2.trace = s.trace := htr2.trans htr1
  exact hrej s2 StoresGhost.opened .preDispatch
    { base := ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, hbase.spAligned⟩
      x19 := hx19_2.trans (hx19_1.trans hx19)
      preRegs := fun _ => ⟨hx20_2.trans (hx20_1.trans hx20), hx25_2.trans (hx25_1.trans hx25)⟩
      trace := htr2_eq ▸ htr, hist := ⟨hfs2_eq.trans hhist.1, htr2_eq ▸ hhist.2⟩, ans := hans }

set_option maxHeartbeats 800000 in
theorem run_hop_pre_of_slots [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs)) :
    RunHopPrePlacedOf CodeOk A H B S slots resStack := by
  intro g s0 Q Qp hh hc hdrop hres hres64 he hpanic hrej hnext
  rw [hneed_eq] at hres
  obtain ⟨hrf, hsub63, hsub64, hsub_addr, _, _, _, hsub_get, _, _, _, _, _, _, hsub_drop, _, hsub_ext, _⟩ :=
    runNeed_bounds_placed hres hres64
  apply r0_sepWPp_intro_address_rp he.inv
  unfold runEntryMemPlaced
  rw [stackAt_run_split s0 hrf (by omega : resStack ≤ 2 ^ 64), r0_memRegion_saved_open_rp s0, r0_probes_split_rp s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r0_sepWPp_exists_all_rp; intro p2; apply r0_sepWPp_exists_all_rp; intro p1
  apply r0_sepWPp_exists_all_rp; intro p0; apply r0_sepWPp_exists_all_rp; intro v11
  apply r0_sepWPp_exists_all_rp; intro v10; apply r0_sepWPp_exists_all_rp; intro v9
  apply r0_sepWPp_exists_all_rp; intro v8; apply r0_sepWPp_exists_all_rp; intro v7
  apply r0_sepWPp_exists_all_rp; intro v6; apply r0_sepWPp_exists_all_rp; intro v5
  apply r0_sepWPp_exists_all_rp; intro v4; apply r0_sepWPp_exists_all_rp; intro v3
  apply r0_sepWPp_exists_all_rp; intro v2; apply r0_sepWPp_exists_all_rp; intro v1
  apply r0_sepWPp_exists_all_rp; intro v0
  have hpc0 : s0.pc = (blkPl_579).base := he.pc.trans runPcPlaced_zero
  refine r0_frame_seq_rp he.inv (F := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      (memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ memRegion g.res runResSize ∗ callAt A g.call g.c ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff)
    (Entails.of_eq (by ac_rfl)) (r0_step_prologue_rp hpc0 he.run he.spAligned) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx3_1, hx19_1, hx20_1, hx23_1, hx24_1, hx25_1⟩
  have hget_call := hc.dirGet hsub_get; unfold dirGetSpecPlaced at hget_call
  refine r0_call_lscro_steps_rp (Q := Q) (Qp := Qp)
    ({ ret := runFsp s0 + 0x4d0#64, self := g.stores, dir := StoresGhost.opened.identity.own,
       nameA := lsρ r0_addrSym_rp, name := utf8 "address", nameRo := true } : DirGetGhost)
    hget_call hinv1 hpc1 hrun1 (r0_spAligned_rp he.spAligned hsp1) hlr1
    (F := r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ memRegion g.res runResSize ∗ callAt A g.call g.c ∗
      r0_storesRest_rp A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      FromRecordCallees.lsLogOff ∗ runSaved s0) (hP := ?_)
    (hpanic := by
      intro sf R' _ _ hp; dsimp only at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix (htr1 ▸ List.prefix_refl s0.trace) hp.1.1)))
    (hnext := ?_)
  · have hrejoin : (((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗ memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗
        memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ⊢
        r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 32 := by
      rw [← r0_frame3_split_rp (runFsp s0)]; exact r0_probes_rejoin_rp s0
    simp only [SpqrV1.ChainProofs.bytesAt, ↓reduceIte]; rw [hsp1, r0_storesAt_eq_rp A g.stores StoresGhost.opened]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_1, hx1_1.trans he.x2, hx2_1,
      by rw [hx3_1, r0_utf8_address_rp]; rfl, by rw [r0_utf8_address_rp]; decide, by decide, r0_own_wrOk_rp⟩ ?_
    exact Entails.trans (r0_apply_head_rp hrejoin (F := runSaved s0 ∗ ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ memRegion g.res runResSize ∗ callAt A g.call g.c ∗
      (dirAt A g.stores StoresGhost.opened.identity.own ∗ r0_storesRest_rp A g.stores StoresGhost.opened) ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) (by ac_rfl)) (Entails.of_eq (by ac_rfl))
  intro s2 hsteps2 hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, hx23_2, hx24_2, hx25_2, _, _, _, hfp2, hv2⟩
  refine SepWPp.weaken_pre (P' := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      ((∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = StoresGhost.opened.identity.own.get cliIo.rd s1.fs.files (utf8 "address") ∧ s2.trace = s1.trace⌝ ∗
            getResultAt A (runFsp s0 + 0x4d0#64) r) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ r0_constFrame_rp A g s0))
    (by simp only [r0_constFrame_rp, SpqrV1.ChainProofs.bytesAt, ↓reduceIte]
        rw [hsp1, r0_storesAt_eq_rp A g.stores StoresGhost.opened]; exact Entails.of_eq (by ac_rfl)) ?_
  apply r0_sepWPp_drop_left_rp; apply r0_sepWPp_exists_left_rp; intro r
  refine SepWPp.weaken_pre (Entails.of_eq (sepConj_assoc _ _ _)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨hr_eq, htr2⟩
  have hbase2 : InRunPlaced CodeOk s0 s2 0x60 :=
    ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, he.spAligned⟩
  have hfs1_run : s1.fs.files = runFiles g.i := (congrArg FsState.files hfs1).trans he.fs
  have hfs2 : s2.fs.files = runFiles g.i :=
    (r0_files_eq_of_trace_eq_rp (hh.fs (lsProg_579 H) 579) hsteps2 htr2).trans hfs1_run
  have htr2_s0 : s2.trace = s0.trace := htr2.trans htr1
  cases r with
  | error u =>
    cases u; dsimp only [getResultAt]
    exact r0_err_to_reject_rp hh hdrop hsub_drop hsub64 hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx25_2.trans (hx25_1.trans he.x1)) (htr2_s0 ▸ List.prefix_refl _)
      ⟨hfs2, htr2_s0 ▸ he.stdout⟩ (he.reject_of_own_err (hfs1_run ▸ hr_eq.symm)) hrej
  | ok ownB =>
    dsimp only [getResultAt]
    exact r0_ok_utf8_address_rp hh hsub_ext hsub_addr hsub63 hsub64 he hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx23_2.trans (hx23_1.trans he.x3)) (hx24_2.trans (hx24_1.trans he.x4))
      (hx25_2.trans (hx25_1.trans he.x1)) (hfs1_run ▸ hr_eq.symm)
      (htr2_s0 ▸ List.prefix_refl _) hfs2 (htr2_s0 ▸ he.stdout) hpanic hnext

theorem run_hop_pre_placed_ok [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {resStack : Nat} : RunHopPrePlaced CodeOk A H B S needs resStack :=
  run_hop_pre_of_slots (needs := needs) rfl

end CryptoVerification.SignalSession.Cli.RunCompose
