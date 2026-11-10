/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainHeap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Callees
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Tag-6 (`sender_chain`) Arm of Inlined `SessionStructure::decode`

Verifies the tag-6 (`sender_chain`, `+0x2214 → +0x2160`) arm of the CLI inlined
`SessionStructure::decode` loop (`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`),
initializing `Chain::default()` at `q + 0x9c0`, calling `message::merge<Chain> [local#5]`, and
branching back to the loop head `+0x2160`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField ChainMergeGenGhost)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ExtraGQ)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓] decryptPrekeyClosure_fnOff
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

private theorem SepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem SepWPp_bind_sepWP_frame {prog : Program} {img : Obj.Image} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_ret_sepWP_frame {prog : Program} {img : Obj.Image} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      img.FrozenLoaded sf → sf.symtab = img.symtab → Q_regs sf →
      Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp_bind_sepWP_frame hF hsym hstep hP fun sf hpc hrun hF' hsym' hregs =>
    SepWPp.done hpc hrun (hret sf hpc hrun hF' hsym' hregs)

private theorem SepWPp_call_frame_frozen_oom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  exact SepWPp.call_wpp_frozen hcall hF hsym hpc hrun hsp hlr (x := x) (F := F)
    (fun R hm => by
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sf code _ _ hpost => by
      rw [hexit_false] at hpost
      exact allowPanic_not_exited hpost)
    (fun sf _ _ => by
      rw [hpan_eq]
      exact allowPanic_oom_of_trace_eq htr)
    (fun sf hpcm hrunm hspm hcsm hF' hsym' =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hF' hsym')
    (fun sf _ _ hpost => by
      rw [hoom_false] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

/-! ## 1. The `bl merge<Chain> [local#5]` target -/

/-- `merge<Chain> [local#5]` relative to `decryptPrekeyClosureName`. -/
theorem overDecChain_fnAddr_chainMerge5 (b : BitVec 64) (ext : String → Option (State → State)) :
    (contractProg b ext).fnAddr chainMerge5Name =
      (contractProg b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]") -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2 ^ 64) := by
  dsimp only [contractProg]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, decryptPrekeyClosure_fnOff,
    (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")]
  bv_omega

/-! ## 2. Segment A (`+0x2214 → merge<Chain> [local#5]`): `Chain::default()` and the call -/

set_option maxHeartbeats 400000 in
theorem overDecChain_segA (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (q : BitVec 64) (u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2214#64)
    (hrun : s.status = .Running) (hsp : s.sp = q) (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx29 : s.readReg64 .x29 = q + 0xc70#64) :
    SepWP (contractProg b ext) ((contractProg b ext).fnAddr chainMerge5Name) s
      (((q + 0x9c0#64) ↦₆₄ noneCap) ∗
        ((q + 0x9c8#64) ↦₆₄ u1) ∗ ((q + 0x9d0#64) ↦₆₄ u2) ∗ ((q + 0x9d8#64) ↦₆₄ u3) ∗
        ((q + 0x9e0#64) ↦₆₄ u4) ∗ ((q + 0x9e8#64) ↦₆₄ u5) ∗ ((q + 0x9f0#64) ↦₆₄ u6) ∗
        ((q + 0x9f8#64) ↦₆₄ u7) ∗ ((q + 0xa00#64) ↦₆₄ u8) ∗ ((q + 0xa08#64) ↦₆₄ u9))
      (fun s1 P_f =>
        (P_f ⊢
          ((q + 0x9c0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗ ((q + 0x9d8#64) ↦₆₄ 0#64) ∗
          ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗ ((q + 0x9f0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
          ((q + 0xa08#64) ↦₆₄ noneCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = q + 0x9c0#64 ∧
        s1.readReg64 .x2 = q + 0xbe8#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2250#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  rw [overDecChain_fnAddr_chainMerge5]
  subst hsp
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2214 0x224c
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx29' : s.readReg64 (Reg.gpr 29#5) = s.sp + 0xc70#64 := hx29
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  try simp only [hx24', hx25']
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Segment B (`+0x2250`): `cbz x0` back to the loop head -/

set_option maxHeartbeats 400000 in
theorem overDecChain_segB (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (q r19 r20 r26 prevPtr : BitVec 64)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2250#64)
    (hrun : s.status = .Running) (hsp : s.sp = q)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = r19) (hx20 : s.readReg64 .x20 = r20)
    (hx21 : s.readReg64 .x21 = q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = r26) (hx27 : s.readReg64 .x27 = prevPtr)
    (hx28 : s.readReg64 .x28 = q + 0xa90#64) (hx29 : s.readReg64 .x29 = q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (fun sf P_f =>
        (P_f ⊢ emp) ∧ sf.sp = q ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = r19 ∧ sf.readReg64 .x20 = r20 ∧
        sf.readReg64 .x21 = q + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = r26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x28 = q + 0xa90#64 ∧
        sf.readReg64 .x29 = q + 0xc70#64 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2250 0x2250
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## 4. Composition -/

theorem overDecChain_payload_suffix {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    ∃ pfx : List (BitVec 8), enc = pfx ++ (fl.payload ++ rest) ∧
      (fl.payload ++ rest).length < 2 ^ 62 := by
  have hs : (fl.payload ++ rest) <:+ enc := by
    refine List.IsSuffix.trans ?_ hsuf
    unfold GenFieldQ.enc
    rw [List.append_assoc]
    exact List.suffix_append _ _
  rcases hs with ⟨t, ht⟩
  refine ⟨t, ht.symm, ?_⟩
  have hle : (fl.payload ++ rest).length ≤ enc.length := by
    simp only [← ht, List.length_append]; omega
  omega

set_option maxHeartbeats 400000 in
/-- Tag 6 (`sender_chain`), `+0x2214 → +0x2160`, from `hC5 : Chain5OkAtWExt A img ext`. -/
theorem overDecArmSender_core_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC5 : Chain5OkAtWExt A img ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest ⟨v.base.apply (.sender c), v.ext⟩))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDecChain_payload_suffix hsuf hlen
  rw [overDecChain_heap_pre_ext A g v pfx _ rest hpfx hnone, overDecChain_mem96 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u7 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 => ?_
  have hstepA := overDecChain_segA img.base ext s g.q u1 u2 u3 u4 u5 u6 u7 u8 u9
    hpc hrun hsp hal hx0 hx21 hx24 hx25 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstepA (by sep_frame)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  refine SepWPp_weaken_frame (overDecChain_bridge_ext A g.q) (by sep_frame) ?_
  have hsp1q : s1.sp = g.q := hsp1.trans hsp
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, hal]
  have hcall : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr chainMerge5Name) (chainMerge5SpecAtWExt A img) := hC5
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  refine SepWPp_call_frame_frozen_oom
    (x := (⟨g.q + 0x9c0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
      g.encPtr + BitVec.ofNat 64 pfx.length, rest⟩ : ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0x9c0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      img.FrozenLoaded s1 ∧ s1.symtab = img.symtab)
    (T := chain3GAt A (g.q + 0x9c0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (c.payload ++ rest) ∗
      A.pool ∗ stackAt g.q chainMerge3StackX)
    hF1 hsym1 (htr1.trans htr) hcall hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [chainMerge5SpecAtWExt, chainMerge3SpecAtWExt]; rw [hsp1q])
    ⟨hx0_w8, hx1_1, hx2_1, hcok, hpay_len, hF1, hsym1⟩
    (by sep_frame)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [chainMerge5SpecAtWExt, chainMerge3SpecAtWExt]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hpost2 => ?_
  obtain ⟨htr2_1, hx0_2⟩ := hpost2
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1q
  have htr2 : s2.trace = s0.trace := htr2_1.trans (htr1.trans htr)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hstepB := overDecChain_segB img.base ext s2 g.q g.r19 g.r20 g.r26 g.prevPtr
    hpc2 hrun2 hsp2 hx0_2
    ((hx19_cs.trans hx19_1).trans hx19) ((hx20_cs.trans hx20_1).trans hx20)
    ((hx21_cs.trans hx21_1).trans hx21) ((hx24_cs.trans hx24_1).trans hx24)
    ((hx25_cs.trans hx25_1).trans hx25) ((hx26_cs.trans hx26_1).trans hx26)
    ((hx27_cs.trans hx27_1).trans hx27) ((hx28_cs.trans hx28_1).trans hx28)
    ((hx29_cs.trans hx29_1).trans hx29)
  refine SepWPp_ret_sepWP_frame hF2 hsym2 hstepB (by rw [emp_sepConj])
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hFf, hsymf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    ((hvregs_f.trans hvregs_cs).trans hvregs_1).trans hvregs⟩, ?_⟩
  dsimp only [GenFieldQ.payload, GenField.payload] at hpfx ⊢
  rw [← overDecChain_heap_post_ext A g v c pfx c.payload rest hpfx, hsp1q, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem overDecArmSender_core (img : Obj.Image) (ext : String → Option (State → State))
    (hC5 : Chain5OkAtW img ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeap g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩))
      (PanicOomProp s0) := by
  unfold Chain5OkAtW at hC5
  rw [← Chain3OkAtWExt_A0] at hC5
  exact overDecArmSender_core_ext img ext hC5 s0 s g v c rest hcok hnone hsuf hlen hregs hx0

/-- Tag 6 (`sender_chain`) at `LibsignalTripleRatchet.AllocContractsX` from `kit : Chain3CalleeKitExt A`. -/
theorem overDecArmSender_tr_of_kit_ext {A : RustAlloc} (kit : Chain3CalleeKitExt A)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hAllocTR : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecSenderField fl) (hok : fl.Ok) (hfresh : fl.Fresh v)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0) := by
  have hC5 : Chain5OkAtWExt A img ext := chainMerge5_ok_ext kit img ext himg hAllocTR
  cases fl
  case base f =>
    cases f
    case sender c =>
      have hok' : c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = [] := hok
      have hfresh' : v.ext = ExtraGQ.empty ∧ v.base.sender = none := hfresh
      have hregs' : OverDecRegs img ext s0 g 0x2214#64 s := hregs
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      exact overDecArmSender_core_ext img ext hC5 s0 s g v c rest
        hok'.1 hfresh'.2 hsuf hlen hregs' hx0'
    all_goals exact False.elim hP
  all_goals exact False.elim hP

theorem overDecArmSender_tr_of_kit (kit : Chain3CalleeKit)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hAllocTR : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img
      CryptoVerification.E2E.Record.A0 ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecSenderField fl) (hok : fl.Ok) (hfresh : fl.Fresh v)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeap g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0) :=
  overDecArmSender_tr_of_kit_ext kit img ext himg hAllocTR s0 s g v fl rest hP hok hfresh hsuf hlen hregs hx0

/-- Tag-6 (`sender_chain`) arm contract `OverDecArmStmtTRExt A OverDecSenderField` for the CLI
inlined `SessionStructure::decode` loop, parameterized by `kit : Chain3CalleeKitExt A`. -/
theorem overDecArmSender_cli_of_kit_ext {A : RustAlloc} (kit : Chain3CalleeKitExt A) :
    OverDecArmStmtTRExt A OverDecSenderField :=
  fun img ext himg hAC s0 s g v fl rest hP hok hfresh hsuf hlen hregs hx0 _hx22 =>
    overDecArmSender_tr_of_kit_ext kit img ext himg hAC s0 s g v fl rest hP hok hfresh hsuf hlen hregs hx0

theorem overDecArmSender_cli_of_kit (kit : Chain3CalleeKit) :
    OverDecArmStmtTR OverDecSenderField :=
  overDecArmSender_cli_of_kit_ext kit

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
