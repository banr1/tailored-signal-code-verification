/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Constant-Time Loop and Raw Subroutine Proof for `promote_matching_session`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem externAt?_black_box_promote (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName +
        bv% (ls_off% "subtle::black_box::<u8>" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) =
      some blackBoxHook := by
  dsimp only [tripleRatchetProgAtExt, promoteMatchingSessionName]
  have hnp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by simp [Rust.isPanicSymbol]
  have h_bb' : (Rust.withPanics ext) "subtle::black_box::<u8>" = some blackBoxHook := by
    simp [Rust.withPanics, hnp, h_bb]
  rw [Program.externAt?_fnAddr_add
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
    (k := num% (ls_off% "subtle::black_box::<u8>" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
    (stub := num% (ls_off% "subtle::black_box::<u8>")) (by decide +kernel) (by decide +kernel),
    (ls_hook% "subtle::black_box::<u8>"), h_bb']

private theorem blackBox_ok_at_promote (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName +
        bv% (ls_off% "subtle::black_box::<u8>" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
      CryptoVerification.SignalSession.CliExt.blackBoxSpec := by
  dsimp only [tripleRatchetProgAtExt, promoteMatchingSessionName]
  exact hook_ok_at
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
    (k := num% (ls_off% "subtle::black_box::<u8>" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
    (stub := num% (ls_off% "subtle::black_box::<u8>"))
    (by decide +kernel) (by decide +kernel)
    (ls_hook% "subtle::black_box::<u8>")
    (by simp [Rust.isPanicSymbol]) h_bb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem cond_ne_subs64_one {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  omega

structure PromoteRawGhost where
  recPtr : BitVec 64
  locCap : BitVec 64
  alicePtr : BitVec 64
  sessVer : BitVec 32
  msgVer : BitVec 8
  serPtr : BitVec 64
  serBytes : List (BitVec 8)
  outPtr : BitVec 64

def promoteMatchingSessionRawSpec : Spec PromoteRawGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.locCap.toNat < 2 ^ 63 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    (∃∗ w4a0 : BitVec 64, (st.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (st.sp - 1136#64) ↦₆₄ w470) ∗
    cells (st.sp - 96#64) 12
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
    cells (s0.sp - 96#64) 12

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_self (a : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 a) = false :=
  bne_self_eq_false _

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0 (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0 (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 1#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

private theorem reaches_pc_extern_m1 {prog : Program} {target_pc : BitVec 64} {s : State}
    {f : State → State} {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_pc prog target_pc (f s) post oom)
    (h_symtab : (f s).symtab = s.symtab := by rfl) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

private theorem step_blackBox_m1 {prog : Program} {target_pc entry_bb : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    (hext : prog.externAt? entry_bb = some blackBoxHook)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hs' : (s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  refine reaches_pc_extern_m1 hrun (hpc ▸ hext) (Memory.KeepsFrozen.refl _) ?_ rfl
  change reaches_pc prog target_pc
    ((s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr)) _ _
  rw [hs']
  have hmem : s'.mem = s.mem := by rw [← hs']; rfl
  exact hnext R (hmem ▸ hm)

local macro "wp_black_box" hext:ident : tactic =>
  `(tactic| (
    apply step_blackBox_m1 $hext
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
  ))

private theorem ofNat64_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_last_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (b0 : BitVec 8) (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.vregs = s.vregs) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hext := externAt?_black_box_promote b h_bb
  dsimp only [tripleRatchetProgAtExt] at hext hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  wp_black_box hext
  wp_steps
  wp_black_box hext
  refine SepWP.done (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm], by simp only [hx23', wp_norm, arm64_norm],
     rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_step_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (b0 : BitVec 8) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧
        s1.vregs = s.vregs) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one m
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hext := externAt?_black_box_promote b h_bb
  dsimp only [tripleRatchetProgAtExt] at hext hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  wp_black_box hext
  wp_steps
  refine SepWP.done (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx19', wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21', hsub1],
     by simp only [hx22', wp_norm, arm64_norm],
     by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm],
     rfl⟩

private theorem promote_ct_eq_loop_prog_wp
    (prog : Program) (loopPc exitPc outPtr : BitVec 64)
    (hlast : ∀ (b0 : BitVec 8) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog exitPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun sf Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs))
    (hstep : ∀ (b0 : BitVec 8) (m : Nat), 0 < m → m + 1 < 2 ^ 64 →
      ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog loopPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun s1 Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧ s1.readReg64 .x25 = 1#64 ∧ s1.vregs = s.vregs))
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loopPc) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP prog exitPc s ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0])) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact hlast b0 serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (hstep b0 (b1 :: rest').length hm_pos hm_lt serPtr alicePtr s
          hpc hrun hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      refine SepWP.bind_seq_readOnly
        (ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
          hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1)
        (by sep_focus)
        fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      ac_rfl

private theorem promote_ct_eq_loop_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.vregs = s.vregs) :=
  promote_ct_eq_loop_prog_wp (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64)
    outPtr
    (fun b0 serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_last_wp h_bb b0 serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25)
    (fun b0 m hm_pos hm_lt serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_step_wp h_bb b0 m hm_pos hm_lt serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25)
    bs hne hlt serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
theorem promote_matching_session_raw_ok {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionRawSpec := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, locCap, alicePtr, sessVer, msgVer, serPtr, serBytes, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionRawSpec] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver, hlen⟩ := hpure
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_prologue_wp s0 recPtr locCap alicePtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcap hver)
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hne : serBytes ≠ [] := by intro he; rw [he] at hlen; contradiction
    have hlt : serBytes.length < 2 ^ 64 := by omega
    have hx21_len : s1.readReg64 .x21 = BitVec.ofNat 64 serBytes.length := by
      rw [hlen]; exact hx21_1
    refine SepWP.bind_seq_readOnly
      (promote_ct_eq_loop_wp h_bb serBytes hne hlt serPtr alicePtr outPtr s1
        hpc1 hrun1 hx19_1 hx21_len hx22_1 hx23_1 hx25_1)
      (by sep_focus) fun s2 hpc2 hrun2 ⟨htr2, hsp2, hx0_2, hx23_2, hvregs2⟩ => ?_
    apply SepWP.mono
    · exact SepWP.frame_auto (promote_epilogue_wp s0 s2 outPtr hpc2 hrun2 hsp_align'
        (htr2.trans htr1) (hsp2.trans hsp1) hx0_2 hx23_2 (hvregs2.trans hvregs1))
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

/-! ## 32-bit stacked `CliExt.blackBoxSpec` generalization -/

def promoteMatchingSessionRawSpecExt32 : Spec PromoteRawGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.locCap.toNat < 2 ^ 63 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    (∃∗ w4a0 : BitVec 64, (st.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (st.sp - 1136#64) ↦₆₄ w470) ∗
    cells (st.sp - 96#64) 12 ∗
    stackAt (st.sp - 1184#64) extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
    cells (s0.sp - 96#64) 12 ∗
    stackAt (s0.sp - 1184#64) extHookStack

private theorem sp_sub_1184_aligned_m1 {sp : BitVec 64}
    (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 1184#64) &&& 15#64 == 0#64) = true := by
  have heq : ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
  rw [heq]; exact h

private theorem sp_sub_96_align_m1 (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

private theorem sp_add_1088_align_m1 (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

private theorem extractLsb32_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    v.extractLsb' 0 32 = 1#32 := by
  bv_slice

private theorem and64_mask8_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    (v &&& 255#64) = 1#64 := by
  bv_slice

private theorem step_blackBox_ext32_m1 {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      (sf.readReg64 .x0).setWidth 32 = 1#32 →
      sf.trace = s.trace →
      SepWP prog target_pc sf (stackAt sf.sp extHookStack ∗ F) post) :
    SepWP prog target_pc s (stackAt s.sp extHookStack ∗ F) post := by
  refine SepWP.call_subroutine_frame_auto (x := 1#64) (F := F) hbb hpc hrun hsp_align hlr
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcf hrunf hspf hcsf => ?_)
    (fun R hm => ?_)
  · dsimp only [CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    rw [sepConj_assoc, ← hspf]
    refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
    exact hnext sf hpcf hrunf hspf hcsf hpure.1 hpure.2
  · dsimp only [CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩

private theorem cells_96_12_eq_m1 (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗
      ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
      ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗
      ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
      ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗
      ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
      ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗
      ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
      ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗
      ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
      ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗
      ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promote_epilogue_ext32_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 s2 : State) (outPtr : BitVec 64)
    (hpc : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : (s2.readReg64 .x0).setWidth 32 = 1#32)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      ((∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
       (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢
          (outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 8#64) ↦₈ 1#8) ∗
          cells (s0.sp - 96#64) 12) ∧
        sf.trace = s0.trace ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) := by
  unfold promoteSavedRegs
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xb4 28
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x2e4 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx0_set : (s2.readReg64 (Reg.gpr 0#5)).setWidth 32 = 1#32 := hx0
  have hx0_ext : (s2.readReg64 (Reg.gpr 0#5)).extractLsb' 0 32 = 1#32 :=
    extractLsb32_of_setWidth32_eq_one hx0
  have hx0_m8 : (s2.readReg64 (Reg.gpr 0#5) &&& 255#64) = 1#64 :=
    and64_mask8_of_setWidth32_eq_one hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hal1 : (((s0.sp - 1184#64) + 1088#64) &&& 15#64) = (s0.sp &&& 15#64) := by bv_robdd
  have hal2 : ((s0.sp - 96#64) &&& 15#64) = (s0.sp &&& 15#64) := sp_sub_96_align_m1 s0.sp
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [hpc, hsp, hx0_set, hx0_ext, hx0_m8, hal1, hal2, hsp_align, wp_norm, arm64_norm])
    (by simp only [hrun, hsp, hx0_set, hx0_ext, hx0_m8, hal1, hal2, hsp_align, wp_norm, arm64_norm])
    ⟨?_, by simp only [htr, wp_norm, arm64_norm],
     by simp only [hsp, wp_norm, arm64_norm],
     ⟨by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm],
      by
        simpa only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm] using hvregs⟩⟩
  rw [cells_96_12_eq_m1 s0.sp]
  sep_frame

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_last_ext32_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (b0 : BitVec 8) (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
      (fun sf Pf =>
        Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = 1#32 ∧
        sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hbb := blackBox_ok_at_promote b h_bb
  dsimp only [tripleRatchetProgAtExt] at hbb hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  refine step_blackBox_ext32_m1 hbb
    (by simp only [hpc, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (ret_pc := entry + 0x94#64)
    (by simp only [hpc, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    fun sf1 hpc1 hrun1 hsp1 hcs1 hw0_1 htr1 => ?_
  have hsp1_s : sf1.sp = s.sp := by simpa only [wp_norm, arm64_norm] using hsp1
  have hsp1_al : sf1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
  rcases hcs1 with ⟨_, _, hx21_cs1, _, hx23_cs1, _, hx25_cs1, _, _, _, _, hvregs_cs1⟩
  have hx21_1 : sf1.readReg64 (Reg.gpr 21#5) = 1#64 := by
    simpa only [hx21', wp_norm, arm64_norm] using hx21_cs1
  have hx23_1 : sf1.readReg64 (Reg.gpr 23#5) = outPtr := by
    simpa only [hx23', wp_norm, arm64_norm] using hx23_cs1
  have hx25_1 : sf1.readReg64 (Reg.gpr 25#5) = 1#64 := by
    simpa only [hx25', wp_norm, arm64_norm] using hx25_cs1
  have hw0_1_set : (sf1.readReg64 (Reg.gpr 0#5)).setWidth 32 = 1#32 := hw0_1
  have hw0_1_ext : (sf1.readReg64 (Reg.gpr 0#5)).extractLsb' 0 32 = 1#32 :=
    extractLsb32_of_setWidth32_eq_one hw0_1
  have htr1_s : sf1.trace = s.trace := by simpa only [wp_norm, arm64_norm] using htr1
  have hvregs1_s : calleeSavedVRegs sf1 = calleeSavedVRegs s := by
    simpa only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm] using hvregs_cs1
  wp_steps
  refine step_blackBox_ext32_m1 hbb
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm])
    (by simp only [hrun1, hx21_1, wp_norm, arm64_norm])
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
    (ret_pc := entry + 0xb4#64)
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm])
    (by simp only [hx21_1, hx25_1, hw0_1_set, hw0_1_ext, wp_norm, arm64_norm])
    fun sf2 hpc2 hrun2 hsp2 hcs2 hw0_2 htr2 => ?_
  rcases hcs2 with ⟨_, _, _, _, hx23_cs2, _, _, _, _, _, _, hvregs_cs2⟩
  have hsp2_1 : sf2.sp = sf1.sp := by simpa only [wp_norm, arm64_norm] using hsp2
  have htr2_1 : sf2.trace = sf1.trace := by simpa only [wp_norm, arm64_norm] using htr2
  have hx23_2 : sf2.readReg64 .x23 = outPtr := by
    simpa only [hx23_1, wp_norm, arm64_norm] using hx23_cs2
  have hvregs2_1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf1 := by
    simpa only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm] using hvregs_cs2
  refine SepWP.done hpc2 hrun2
    ⟨by rw [hsp2_1, hsp1_s],
     htr2_1.trans htr1_s,
     hsp2_1.trans hsp1_s,
     hw0_2,
     hx23_2,
     hvregs2_1.trans hvregs1_s⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_step_ext32_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (b0 : BitVec 8) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s
      (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
      (fun s1 Pf =>
        Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one m
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hbb := blackBox_ok_at_promote b h_bb
  dsimp only [tripleRatchetProgAtExt] at hbb hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  refine step_blackBox_ext32_m1 hbb
    (by simp only [hpc, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (ret_pc := entry + 0x94#64)
    (by simp only [hpc, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    fun sf1 hpc1 hrun1 hsp1 hcs1 hw0_1 htr1 => ?_
  rcases hcs1 with ⟨hx19_cs1, _, hx21_cs1, hx22_cs1, hx23_cs1, _, hx25_cs1, _, _, _, _, hvregs_cs1⟩
  have hsp1_s : sf1.sp = s.sp := by simpa only [wp_norm, arm64_norm] using hsp1
  have hx19_1 : sf1.readReg64 (Reg.gpr 19#5) = alicePtr + 1#64 := by
    simpa only [hx19', wp_norm, arm64_norm] using hx19_cs1
  have hx21_1 : sf1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := by
    simpa only [hx21', wp_norm, arm64_norm] using hx21_cs1
  have hx22_1 : sf1.readReg64 (Reg.gpr 22#5) = serPtr + 1#64 := by
    simpa only [hx22', wp_norm, arm64_norm] using hx22_cs1
  have hx23_1 : sf1.readReg64 (Reg.gpr 23#5) = outPtr := by
    simpa only [hx23', wp_norm, arm64_norm] using hx23_cs1
  have hx25_1 : sf1.readReg64 (Reg.gpr 25#5) = 1#64 := by
    simpa only [hx25', wp_norm, arm64_norm] using hx25_cs1
  have hw0_1_set : (sf1.readReg64 (Reg.gpr 0#5)).setWidth 32 = 1#32 := hw0_1
  have hw0_1_ext : (sf1.readReg64 (Reg.gpr 0#5)).extractLsb' 0 32 = 1#32 :=
    extractLsb32_of_setWidth32_eq_one hw0_1
  have htr1_s : sf1.trace = s.trace := by simpa only [wp_norm, arm64_norm] using htr1
  have hvregs1_s : calleeSavedVRegs sf1 = calleeSavedVRegs s := by
    simpa only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm] using hvregs_cs1
  wp_steps
  refine SepWP.done (by simp only [hpc1, hx21_1, hbr, wp_norm, arm64_norm])
    (by simp only [hrun1, wp_norm, arm64_norm])
    ⟨by simp only [hsp1_s, wp_norm, arm64_norm],
     by simp only [htr1_s, wp_norm, arm64_norm],
     by simp only [hsp1_s, wp_norm, arm64_norm],
     by simp only [hx19_1, wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21_1, hsub1],
     by simp only [hx22_1, wp_norm, arm64_norm],
     by simp only [hx23_1, wp_norm, arm64_norm],
     by simp only [hx25_1, hw0_1_set, hw0_1_ext, wp_norm, arm64_norm],
     by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hvregs1_s⟩

private theorem promote_ct_eq_loop_prog_ext32_wp
    (prog : Program) (loopPc exitPc outPtr : BitVec 64)
    (hlast : ∀ (b0 : BitVec 8) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog exitPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
        (fun sf Pf =>
          Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          (sf.readReg64 .x0).setWidth 32 = 1#32 ∧ sf.readReg64 .x23 = outPtr ∧
          calleeSavedVRegs sf = calleeSavedVRegs s))
    (hstep : ∀ (b0 : BitVec 8) (m : Nat), 0 < m → m + 1 < 2 ^ 64 →
      ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog loopPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
        (fun s1 Pf =>
          Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧ s1.readReg64 .x25 = 1#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s))
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loopPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP prog exitPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)))
      (fun sf Pf =>
        Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = 1#32 ∧ sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0])) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact hlast b0 serPtr alicePtr s hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (hstep b0 (b1 :: rest').length hm_pos hm_lt serPtr alicePtr s
          hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_al
      have hstk1 : stackAt s.sp extHookStack = stackAt s1.sp extHookStack := by rw [hsp1]
      conv => arg 4; rw [hstk1]
      refine SepWP.bind_seq_readOnly
        (ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
          hpc1 hrun1 hsp1_al hx19_1 hx21_1 hx22_1 hx23_1 hx25_1)
        (by sep_focus)
        fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [← hstk1, pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      ac_rfl

private theorem promote_ct_eq_loop_ext32_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)))
      (fun sf Pf =>
        Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = 1#32 ∧
        sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) :=
  promote_ct_eq_loop_prog_ext32_wp (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64)
    outPtr
    (fun b0 serPtr alicePtr s hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_last_ext32_wp h_bb b0 serPtr alicePtr outPtr s
        hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25)
    (fun b0 m hm_pos hm_lt serPtr alicePtr s hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_step_ext32_wp h_bb b0 m hm_pos hm_lt serPtr alicePtr outPtr s
        hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25)
    bs hne hlt serPtr alicePtr s hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
theorem promote_matching_session_raw_ok_ext32 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionRawSpecExt32 := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, locCap, alicePtr, sessVer, msgVer, serPtr, serBytes, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionRawSpecExt32] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver, hlen⟩ := hpure
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_prologue_wp s0 recPtr locCap alicePtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcap hver)
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hne : serBytes ≠ [] := by intro he; rw [he] at hlen; contradiction
    have hlt : serBytes.length < 2 ^ 64 := by omega
    have hx21_len : s1.readReg64 .x21 = BitVec.ofNat 64 serBytes.length := by
      rw [hlen]; exact hx21_1
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1] using sp_sub_1184_aligned_m1 hsp_align'
    have hstk1 : stackAt (s0.sp - 1184#64) extHookStack = stackAt s1.sp extHookStack := by
      rw [hsp1]
    conv => arg 4; rw [hstk1]
    refine SepWP.bind_seq_readOnly
      (promote_ct_eq_loop_ext32_wp h_bb serBytes hne hlt serPtr alicePtr outPtr s1
        hpc1 hrun1 hsp1_al hx19_1 hx21_len hx22_1 hx23_1 hx25_1)
      (by sep_focus) fun s2 hpc2 hrun2 ⟨htr2, hsp2, hx0_2, hx23_2, hvregs2⟩ => ?_
    have hvregs02 : calleeSavedVRegs s2 = calleeSavedVRegs s0 :=
      hvregs2.trans (congrArg VRegFile.calleeSaved hvregs1)
    apply SepWP.mono
    · exact SepWP.frame_auto (promote_epilogue_ext32_wp s0 s2 outPtr hpc2 hrun2 hsp_align'
        (htr2.trans htr1) (hsp2.trans hsp1) hx0_2 hx23_2 hvregs02)
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf, ← hstk1]
      sep_frame
    · intro _ _ _ hf; exact hf

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
