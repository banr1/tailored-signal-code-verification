/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Frame
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Wrapper Prologue Symbolic Execution for `decrypt_prekey`

Steps the `signal_session_handshake::decrypt_prekey` wrapper prologue from function entry up to the
call to the `message_decrypt_prekey` poll closure.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm

gen_decodes CryptoVerification.libsignalSessionCode_tree dpWrapBin
  [(ls_off% "libsignal_cli_handshake::decrypt_prekey") →
     (ls_off% "libsignal_cli_handshake::decrypt_prekey" + 112),
   (ls_off% "libsignal_cli_handshake::decrypt_prekey" + 156) →
     (ls_off% "libsignal_cli_handshake::decrypt_prekey" + 212),
   (ls_off% "libsignal_cli_handshake::decrypt_prekey" + 464) →
     (ls_off% "libsignal_cli_handshake::decrypt_prekey" + 484)]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (v : BitVec 5) :
    (s.setPC pc).readVReg128 v = s.readVReg128 v := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (v : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 v = s.readVReg128 v := by cases s; rfl

theorem cliDecryptPrekey_fnOff :
    libsignalSessionCode.fnOff cliDecryptPrekeyName =
      ls_off% "libsignal_cli_handshake::decrypt_prekey" :=
  ls_lemma% fnOff "libsignal_cli_handshake::decrypt_prekey"

theorem cliDpPoll_fnOff :
    libsignalSessionCode.fnOff cliDpPollName =
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" :=
  ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"

theorem sep_rearrange {P P' : SepProp} (hf : P = P' ∗ emp) : P = P' := by
  rw [hf, sepConj_emp]

@[scoped arm64_norm] theorem bv128_lo_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
@[scoped arm64_norm] theorem bv128_hi_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
@[scoped arm64_norm] theorem bv_add_16_8 (x : BitVec 64) : x + 16#64 + 8#64 = x + 24#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_add_32_8 (x : BitVec 64) : x + 32#64 + 8#64 = x + 40#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_01 (x : BitVec 64) : x - 48#64 + 8#64 = x - 40#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_02 (x : BitVec 64) : x - 48#64 + 16#64 = x - 32#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_03 (x : BitVec 64) : x - 32#64 + 8#64 = x - 24#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_04 (x : BitVec 64) : x - 48#64 + 32#64 = x - 16#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_05 (x : BitVec 64) : x - 16#64 + 8#64 = x - 8#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_06 (x : BitVec 64) : x - 48#64 + 48#64 = x := by bv_kernel
@[scoped arm64_norm] theorem bv_off_07 (x : BitVec 64) : x - 48#64 + 80#64 = x + 32#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_08 (x : BitVec 64) : x - 48#64 - 1#64 = x - 49#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_09 (x : BitVec 64) : x - 48#64 - 2096#64 = x - 2144#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_10 (x : BitVec 64) : x - 48#64 - 56#64 = x - 104#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_11 (x : BitVec 64) : x - 48#64 - 88#64 = x - 136#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_12 (x : BitVec 64) : x - 48#64 - 72#64 = x - 120#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_13 (x : BitVec 64) : x - 136#64 + 8#64 = x - 128#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_14 (x : BitVec 64) : x - 104#64 + 8#64 = x - 96#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_15 (x : BitVec 64) : x - 104#64 + 16#64 = x - 88#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_15b (x : BitVec 64) : x - 104#64 + 24#64 = x - 80#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_16 (x : BitVec 64) : x - 88#64 + 8#64 = x - 80#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_17 (x : BitVec 64) : x - 104#64 + 32#64 = x - 72#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_17b (x : BitVec 64) : x - 104#64 + 40#64 = x - 64#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_18 (x : BitVec 64) : x - 72#64 + 8#64 = x - 64#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_19 (x : BitVec 64) : x - 2144#64 + 8#64 = x - 2136#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_20 (x : BitVec 64) : x - 2144#64 + 16#64 = x - 2128#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_21 (x : BitVec 64) : x - 2128#64 + 8#64 = x - 2120#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_22 (x : BitVec 64) : x - 2144#64 + 32#64 = x - 2112#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_23 (x : BitVec 64) : x - 2112#64 + 8#64 = x - 2104#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_24 (x : BitVec 64) : x - 2144#64 + 48#64 = x - 2096#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_25 (x : BitVec 64) : x - 2096#64 + 8#64 = x - 2088#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_26 (x : BitVec 64) : x - 2144#64 + 64#64 = x - 2080#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_27 (x : BitVec 64) : x - 2080#64 + 8#64 = x - 2072#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_28 (x : BitVec 64) : x - 2080#64 + 16#64 = x - 2064#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_29 (x : BitVec 64) : x - 2064#64 + 8#64 = x - 2056#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_30 (x : BitVec 64) : x - 2144#64 + 96#64 = x - 2048#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_31 (x : BitVec 64) : x - 2048#64 + 8#64 = x - 2040#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_32 (x : BitVec 64) : x - 2144#64 + 704#64 = x - 1440#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_33 (x : BitVec 64) : x - 2144#64 + 2096#64 = x - 48#64 := by bv_kernel

private theorem dp_sp_sub_2144_aligned (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    (sp - 2144#64 &&& 15#64 == 0#64) = true := by bv_kernel

structure DpPrologueMid1 (img : Obj.Image) (entry : BitVec 64)
    (s0 : State) (ret a8 a9 a10 a11 a12 : BitVec 64) (sa : State) : Prop where
  sym : sa.symtab = img.symtab
  pc : sa.pc = entry + bv% (36)
  run : sa.status = .Running
  sp : sa.sp = s0.sp - 2144#64
  sp_align : sa.spAligned = true
  fp : sa.readReg64 .fp = s0.sp - 48#64
  x0 : sa.readReg64 (.gpr 0#5) = s0.readReg64 (.gpr 0#5)
  x1 : sa.readReg64 (.gpr 1#5) = s0.readReg64 (.gpr 1#5)
  x2 : sa.readReg64 (.gpr 2#5) = s0.readReg64 (.gpr 2#5)
  x3 : sa.readReg64 (.gpr 3#5) = s0.readReg64 (.gpr 3#5)
  x4 : sa.readReg64 (.gpr 4#5) = s0.readReg64 (.gpr 4#5)
  x5 : sa.readReg64 (.gpr 5#5) = s0.readReg64 (.gpr 5#5)
  x6 : sa.readReg64 (.gpr 6#5) = s0.readReg64 (.gpr 6#5)
  x7 : sa.readReg64 (.gpr 7#5) = s0.readReg64 (.gpr 7#5)
  x8 : sa.readReg64 (.gpr 8#5) = a12
  x9 : sa.readReg64 (.gpr 9#5) = s0.sp - 49#64
  q0 : sa.readVReg128 0#5 = a9 ++ a8
  q1 : sa.readVReg128 1#5 = a11 ++ a10
  x19 : sa.readReg64 (.gpr 19#5) = ret
  x22 : sa.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : sa.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : sa.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : sa.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : sa.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : sa.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs sa = calleeSavedVRegs s0
  fs : sa.fs = s0.fs
  trace : sa.trace = s0.trace

structure DpPrologueMid2 (img : Obj.Image) (entry : BitVec 64)
    (s0 : State) (ret a8 a9 a10 a11 : BitVec 64) (sb : State) : Prop where
  sym : sb.symtab = img.symtab
  pc : sb.pc = entry + bv% (64)
  run : sb.status = .Running
  sp : sb.sp = s0.sp - 2144#64
  sp_align : sb.spAligned = true
  fp : sb.readReg64 .fp = s0.sp - 48#64
  x0 : sb.readReg64 .x0 = s0.sp - 104#64
  x1 : sb.readReg64 .x1 = s0.sp - 2144#64
  x2 : sb.readReg64 .x2 = s0.sp - 136#64
  x4 : sb.readReg64 (.gpr 4#5) = s0.readReg64 (.gpr 4#5)
  x5 : sb.readReg64 (.gpr 5#5) = s0.readReg64 (.gpr 5#5)
  x6 : sb.readReg64 (.gpr 6#5) = s0.readReg64 (.gpr 6#5)
  x7 : sb.readReg64 (.gpr 7#5) = s0.readReg64 (.gpr 7#5)
  q0 : sb.readVReg128 0#5 = a9 ++ a8
  q1 : sb.readVReg128 1#5 = a11 ++ a10
  x19 : sb.readReg64 (.gpr 19#5) = ret
  x22 : sb.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : sb.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : sb.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : sb.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : sb.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : sb.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs sb = calleeSavedVRegs s0
  fs : sb.fs = s0.fs
  trace : sb.trace = s0.trace

structure DpProloguePost (img : Obj.Image) (entry : BitVec 64) (s0 : State) (ret : BitVec 64) (s1 : State) : Prop where
  sym : s1.symtab = img.symtab
  pc : s1.pc = entry +
    (BitVec.ofNat 64 (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") -
     BitVec.ofNat 64 (ls_off% "libsignal_cli_handshake::decrypt_prekey"))
  run : s1.status = .Running
  sp : s1.sp = s0.sp - 2144#64
  sp_align : s1.spAligned = true
  x0 : s1.readReg64 .x0 = s0.sp - 104#64
  x1 : s1.readReg64 .x1 = s0.sp - 2144#64
  x2 : s1.readReg64 .x2 = s0.sp - 136#64
  lr : s1.readReg64 .lr = entry + bv% (100)
  fp : s1.readReg64 .fp = s0.sp - 48#64
  x19 : s1.readReg64 (.gpr 19#5) = ret
  x22 : s1.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs s1 = calleeSavedVRegs s0
  fs : s1.fs = s0.fs
  trace : s1.trace = s0.trace

abbrev dpPrologueMid2Prop (stk : Nat) (s0 : State) (ret : BitVec 64) {K : DpPollK} (g : K.Ghost)
    (a12 f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64) (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64) : SepProp :=
  stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    ((s0.sp - 2144#64) ↦₆₄ s0.readReg64 (Reg.gpr 0#5)) ∗ ((s0.sp - 2136#64) ↦₆₄ s0.readReg64 (Reg.gpr 1#5)) ∗
    ((s0.sp - 2128#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗ ((s0.sp - 2120#64) ↦₆₄ s0.readReg64 (Reg.gpr 3#5)) ∗
    ((s0.sp - 2112#64) ↦₆₄ f4) ∗ ((s0.sp - 2104#64) ↦₆₄ f5) ∗ ((s0.sp - 2096#64) ↦₆₄ f6) ∗ ((s0.sp - 2088#64) ↦₆₄ f7) ∗
    ((s0.sp - 2080#64) ↦₆₄ f8) ∗ ((s0.sp - 2072#64) ↦₆₄ f9) ∗ ((s0.sp - 2064#64) ↦₆₄ f10) ∗ ((s0.sp - 2056#64) ↦₆₄ f11) ∗
    ((s0.sp - 2048#64) ↦₆₄ a12) ∗ ((s0.sp - 2040#64) ↦₆₄ (s0.sp - 49#64)) ∗
    memRegion (s0.sp - 2032#64) 592 ∗ ((s0.sp - 1440#64) ↦₈ fstate) ∗ memRegion (s0.sp - 1439#64) 1303 ∗
    ((s0.sp - 136#64) ↦₆₄ cx0) ∗ ((s0.sp - 128#64) ↦₆₄ cx1) ∗ ((s0.sp - 120#64) ↦₆₄ cx2) ∗
    memRegion (s0.sp - 112#64) 8 ∗ memRegion (s0.sp - 104#64) 48 ∗
    K.inv g ∗ dpCallerFrame s0 ret ((K.args g).drop 8)

set_option maxHeartbeats 400000 in
theorem dpWrapper_prologue_a1 {img : Obj.Image} {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 : State} {ret : BitVec 64} {g : K.Ghost} {a8 a9 a10 a11 a12 : BitVec 64}
    {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName)
    (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true)
    (hx8 : s0.readReg64 (Reg.gpr 8#5) = ret) (hsym0 : s0.symtab = img.symtab)
    (hdrop_eq : (K.args g).drop 8 = [a8, a9, a10, a11, a12])
    (hk : ∀ sa Pa,
      DpPrologueMid1 img ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName)
        s0 ret a8 a9 a10 a11 a12 sa →
      Pa = memRegion (s0.sp - 2144#64) 2088 ∗
             (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗ dpCallerFrame s0 ret ((K.args g).drop 8)) →
      Q sa Pa) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName + bv% (36))
      s0 (dpWordsAt s0.sp ((K.args g).drop 8) ∗ memRegion ret 48 ∗ K.inv g ∗ stackAt s0.sp stk) Q oom := by
  have hfn : libsignalSessionCode.fnOff cliDecryptPrekeyName = ls_off% "libsignal_cli_handshake::decrypt_prekey" :=
    cliDecryptPrekey_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dpWrapBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "libsignal_cli_handshake::decrypt_prekey")) 0 36
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rw [← BitVec.add_zero entry] at hpc
  rw [← sepConj_assoc, ← sepConj_assoc]
  refine sepWP_with_dp_saved hge_wrap hle_wrap fun sfp slr sx28 sx21 sx20 sx19 => ?_
  rw [hdrop_eq, dpWords5_eq s0.sp a8 a9 a10 a11 a12]
  wp_steps
  apply SepWP.fold (Entails.of_eq (dpWords5_eq s0.sp a8 a9 a10 a11 a12).symm) (by sep_focus)
  rw [← hdrop_eq]
  apply SepWP.fold (dpCallerFrame_pack s0 ret ((K.args g).drop 8)) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine hk _ _ ?_ (sep_rearrange (by sep_focus))
  exact
    { sym := by simp only [wp_norm, arm64_norm, hsym0]
      pc := by simp only [wp_norm, arm64_norm]
      run := by simp only [wp_norm, arm64_norm, *]
      sp := by simp only [wp_norm, arm64_norm]
      sp_align := by simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢; exact hsp_align
      fp := by simp only [wp_norm, arm64_norm]
      x0 := by simp only [wp_norm, arm64_norm]
      x1 := by simp only [wp_norm, arm64_norm]
      x2 := by simp only [wp_norm, arm64_norm]
      x3 := by simp only [wp_norm, arm64_norm]
      x4 := by simp only [wp_norm, arm64_norm]
      x5 := by simp only [wp_norm, arm64_norm]
      x6 := by simp only [wp_norm, arm64_norm]
      x7 := by simp only [wp_norm, arm64_norm]
      x8 := by simp only [wp_norm, arm64_norm]
      x9 := by simp only [wp_norm, arm64_norm]
      q0 := by simp only [wp_norm, arm64_norm]
      q1 := by simp only [wp_norm, arm64_norm]
      x19 := by simp only [wp_norm, arm64_norm]
      x22 := by simp only [wp_norm, arm64_norm]
      x23 := by simp only [wp_norm, arm64_norm]
      x24 := by simp only [wp_norm, arm64_norm]
      x25 := by simp only [wp_norm, arm64_norm]
      x26 := by simp only [wp_norm, arm64_norm]
      x27 := by simp only [wp_norm, arm64_norm]
      vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm]
      fs := by simp only [wp_norm, arm64_norm]
      trace := by simp only [wp_norm, arm64_norm] }

set_option maxHeartbeats 400000 in
theorem dpWrapper_prologue_a2 {img : Obj.Image} {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sa : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 : BitVec 64} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (ha : DpPrologueMid1 img ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName)
      s0 ret a8 a9 a10 a11 a12 sa)
    (hk : ∀ sb Pb (f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64) (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64),
      DpPrologueMid2 img ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName)
        s0 ret a8 a9 a10 a11 sb →
      Pb = dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 →
      Q sb Pb) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName + bv% (64)) sa
      (memRegion (s0.sp - 2144#64) 2088 ∗
        (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗ dpCallerFrame s0 ret ((K.args g).drop 8)))
      Q oom := by
  rcases ha with ⟨hsym_a, hpc_a, hrun_a, hsp_a, hsp_align_a, hfp_a, hx0_a, hx1_a,
    hx2_a, hx3_a, hx4_a, hx5_a, hx6_a, hx7_a, hx8_a, hx9_a, hq0_a, hq1_a, hx19_a,
    hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hvregs_a, hfs_a, htr_a⟩
  have hfn : libsignalSessionCode.fnOff cliDecryptPrekeyName = ls_off% "libsignal_cli_handshake::decrypt_prekey" :=
    cliDecryptPrekey_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dpWrapBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "libsignal_cli_handshake::decrypt_prekey")) 36 28
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  refine sepWP_with_dp_locals s0.sp fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 fcoins fstate cx0 cx1 cx2 => ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine hk _ _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 ?_ (sep_rearrange (by dsimp only [dpPrologueMid2Prop]; sep_focus))
  exact
    { sym := by simp only [wp_norm, arm64_norm, hsym_a]
      pc := by simp only [wp_norm, arm64_norm]
      run := by simp only [wp_norm, arm64_norm, *]
      sp := by simp only [wp_norm, arm64_norm, *]
      sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_a ⊢; exact hsp_align_a
      fp := by simp only [wp_norm, arm64_norm, *]
      x0 := by simp only [wp_norm, arm64_norm, *]
      x1 := by simp only [wp_norm, arm64_norm, *]
      x2 := by simp only [wp_norm, arm64_norm, *]
      x4 := by simp only [wp_norm, arm64_norm, *]
      x5 := by simp only [wp_norm, arm64_norm, *]
      x6 := by simp only [wp_norm, arm64_norm, *]
      x7 := by simp only [wp_norm, arm64_norm, *]
      q0 := by simp only [wp_norm, arm64_norm, *]
      q1 := by simp only [wp_norm, arm64_norm, *]
      x19 := by simp only [wp_norm, arm64_norm, *]
      x22 := by simp only [wp_norm, arm64_norm, *]
      x23 := by simp only [wp_norm, arm64_norm, *]
      x24 := by simp only [wp_norm, arm64_norm, *]
      x25 := by simp only [wp_norm, arm64_norm, *]
      x26 := by simp only [wp_norm, arm64_norm, *]
      x27 := by simp only [wp_norm, arm64_norm, *]
      vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
      fs := by simp only [wp_norm, arm64_norm, *]
      trace := by simp only [wp_norm, arm64_norm, *] }

set_option maxHeartbeats 400000 in
theorem dpWrapper_prologue_b {img : Obj.Image} {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sb : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64}
    {fstate : BitVec 8} {cx0 cx1 cx2 : BitVec 64} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hb : DpPrologueMid2 img ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName)
      s0 ret a8 a9 a10 a11 sb)
    (hargs_eq : K.args g =
      [s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5), s0.readReg64 (Reg.gpr 2#5), s0.readReg64 (Reg.gpr 3#5),
       s0.readReg64 (Reg.gpr 4#5), s0.readReg64 (Reg.gpr 5#5), s0.readReg64 (Reg.gpr 6#5), s0.readReg64 (Reg.gpr 7#5),
       a8, a9, a10, a11, a12])
    (hk : ∀ s1 P1,
      DpProloguePost img ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName) s0 ret s1 →
      P1 = (memRegion (s0.sp - 104#64) 48 ∗ dpFutStartAt (s0.sp - 2144#64) (K.args g) ∗
              dpCxAt (s0.sp - 136#64) ∗ K.inv g ∗ stackAt (s0.sp - 2144#64) (stk - dpWrapFrame)) ∗
           dpCallerFrame s0 ret ((K.args g).drop 8) →
      Q s1 P1) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName +
        (BitVec.ofNat 64 (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") -
         BitVec.ofNat 64 (ls_off% "libsignal_cli_handshake::decrypt_prekey")))
      sb (dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2) Q oom := by
  rcases hb with ⟨hsym_b, hpc_b, hrun_b, hsp_b, hsp_align_b, hfp_b, hx0_b, hx1_b,
    hx2_b, hx4_b, hx5_b, hx6_b, hx7_b, hq0_b, hq1_b, hx19_b,
    hx22_b, hx23_b, hx24_b, hx25_b, hx26_b, hx27_b, hvregs_b, hfs_b, htr_b⟩
  have hfn : libsignalSessionCode.fnOff cliDecryptPrekeyName = ls_off% "libsignal_cli_handshake::decrypt_prekey" :=
    cliDecryptPrekey_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dpWrapBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "libsignal_cli_handshake::decrypt_prekey")) 64 36
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDecryptPrekeyName = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  dsimp only [dpPrologueMid2Prop]
  wp_steps
  apply SepWP.fold (dpFutStartAt_pack s0.sp _ _ _ _ _ _ _ _ a8 a9 a10 a11 a12 _) (by sep_focus)
  rw [← hargs_eq]
  apply SepWP.fold (dpCxAt_pack s0.sp _) (by sep_focus)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  refine hk _ _ ?_ (sep_rearrange (by sep_focus))
  exact
    { sym := by simp only [wp_norm, arm64_norm, hsym_b]
      pc := by simp only [wp_norm, arm64_norm]
      run := by simp only [wp_norm, arm64_norm, *]
      sp := by simp only [wp_norm, arm64_norm, *]
      sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_b ⊢; exact hsp_align_b
      x0 := by simp only [wp_norm, arm64_norm, *]
      x1 := by simp only [wp_norm, arm64_norm, *]
      x2 := by simp only [wp_norm, arm64_norm, *]
      lr := by simp only [wp_norm, arm64_norm, *]
      fp := by simp only [wp_norm, arm64_norm, *]
      x19 := by simp only [wp_norm, arm64_norm, *]
      x22 := by simp only [wp_norm, arm64_norm, *]
      x23 := by simp only [wp_norm, arm64_norm, *]
      x24 := by simp only [wp_norm, arm64_norm, *]
      x25 := by simp only [wp_norm, arm64_norm, *]
      x26 := by simp only [wp_norm, arm64_norm, *]
      x27 := by simp only [wp_norm, arm64_norm, *]
      vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
      fs := by simp only [wp_norm, arm64_norm, *]
      trace := by simp only [wp_norm, arm64_norm, *] }

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
