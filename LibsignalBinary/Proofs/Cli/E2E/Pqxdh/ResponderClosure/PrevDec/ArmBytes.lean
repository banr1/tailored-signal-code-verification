/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Bytes Arms (Tags 2, 3, 4, 13, 15) of Inlined `SessionStructure::decode`

Proves per-tag and combined `OverDecBytesField` decode-arm theorems (`+0x22cc`, `+0x22b8`, `+0x2290`,
`+0x21d4`, `+0x2200 → +0x2160`) in `message_decrypt_prekey::<Coins>::{closure#0}`, invoking
`bytes::merge [local#6]` (`BytesMerge6OkExtW`) on `local_identity_public`, `remote_identity_public`,
`root_key`, `alice_base_key`, and `pq_ratchet_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.LibsignalTripleRatchet.Prost

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  decryptPrekeyClosure_fnOff bytesMerge6_fnOff

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
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  ProofLib.SepWPp.call_frame_frozen hcall hF hsym hpc hrun hsp hlr hspec hφ hP
    (fun sf code R' _ hex => by rw [hexit_false] at hex; exact not_satisfies_false_sepConj hex)
    (fun sf _ => by rw [hpan_eq sf]; exact allowPanic_oom_of_trace_eq htr)
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    (fun sf R' _ hoom => by rw [hoom_false] at hoom; exact (not_satisfies_false_sepConj hoom).elim)

/-! ## Stack Split and `prostSSGQAt` Field Splits -/

theorem stackAt_overDec_to_bytesMerge3 (sp : BitVec 64) :
    stackAt sp overDecStackX =
      memRegion (sp - 65536#64) (65536 - bytesMerge3Stack) ∗ stackAt sp bytesMerge3Stack := by
  have hN : overDecStackX = bytesMerge3Stack + (65536 - bytesMerge3Stack) := by decide
  have hb : BitVec.ofNat 64 (bytesMerge3Stack + (65536 - bytesMerge3Stack)) = 65536#64 := by decide
  rw [hN, ProofLib.stackAt_split_bottom sp bytesMerge3Stack (65536 - bytesMerge3Stack) (by decide), hb]

/-- `prostSSGQAt` without `local_identity_public` (`ss`). -/
def prostSSGQRest2 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_lik_sep_rest2 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A ss v.base.lik ∗ prostSSGQRest2 A ss v := by
  unfold prostSSGQAt prostSSGQRest2
  cases v.base.sender <;> cases v.base.pending <;> dsimp only

/-- `prostSSGQAt` without `remote_identity_public` (`ss + 0x18`). -/
def prostSSGQRest3 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_rik_sep_rest3 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x18#64) v.base.rik ∗ prostSSGQRest3 A ss v := by
  unfold prostSSGQAt prostSSGQRest3
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `root_key` (`ss + 0x30`). -/
def prostSSGQRest4 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_root_sep_rest4 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x30#64) v.base.root ∗ prostSSGQRest4 A ss v := by
  unfold prostSSGQAt prostSSGQRest4
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `alice_base_key` (`ss + 0x60`). -/
def prostSSGQRest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_abk_sep_rest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x60#64) v.ext.abk ∗ prostSSGQRest13 A ss v := by
  unfold prostSSGQAt prostSSGQRest13
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `pq_ratchet_state` (`ss + 0x78`). -/
def prostSSGQRest15 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_pq_sep_rest15 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x78#64) v.ext.pq ∗ prostSSGQRest15 A ss v := by
  unfold prostSSGQAt prostSSGQRest15
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-! ## Slice Cursor Split and Recombination -/

theorem sliceCursorAfter_split_sub (slot ptr : BitVec 64) (pfx sfx : List (BitVec 8)) :
    Prost.sliceCursorAfter slot ptr (pfx ++ sfx) sfx =
      (ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 pfx.length) sfx :=
  sliceCursorAfter_append_eq_seedChain slot ptr pfx sfx

theorem sliceCursorAfter_unsplit_sub (slot ptr : BitVec 64) (pfx payload rest : List (BitVec 8)) :
    (ptr ↦ₛ pfx) ∗
        Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 pfx.length) (payload ++ rest) rest =
      Prost.sliceCursorAfter slot ptr (pfx ++ (payload ++ rest)) rest := by
  unfold Prost.sliceCursorAfter
  have hlen : (pfx ++ (payload ++ rest)).length - rest.length = pfx.length + payload.length := by
    simp only [List.length_append]; omega
  have hlen2 : (payload ++ rest).length - rest.length = payload.length := by
    simp only [List.length_append]; omega
  rw [hlen, hlen2, BitVec.ofNat_add, ← BitVec.add_assoc, pointsToBytes_append ptr pfx (payload ++ rest)]
  ac_rfl

/-! ## Call Offset for `bytes::merge [local#6]` -/

theorem overDec_bytesMerge6_addr_eq (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr decryptPrekeyClosureName +
      bv% ((2 ^ 64 + ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64) =
    (libsignalSessionCode.rebase b H).fnAddr bytesMerge6Name :=
  fnAddr_rel64 decryptPrekeyClosure_fnOff bytesMerge6_fnOff (by decide)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Shared Call and Post-Call `cbz` Helpers -/

theorem overDec_payload_suffix_and_len {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    ∃ pfx : List (BitVec 8),
      enc = pfx ++ (fl.payload ++ rest) ∧ (fl.payload ++ rest).length < 2 ^ 62 := by
  rcases hsuf with ⟨t, ht⟩
  unfold GenFieldQ.enc at ht
  refine ⟨t ++ encodeKey fl.tag fl.wt, ?_, ?_⟩
  · rw [← ht, List.append_assoc, List.append_assoc]
  · have hle : (fl.payload ++ rest).length ≤ enc.length := by
      simp only [← ht, List.length_append]
      omega
    omega

theorem overDec_mergeBytes_eq (b rest : List (BitVec 8)) (hb : b.length < 2 ^ 64) :
    mergeBytes .lengthDelimited ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ rest) =
      some (b, rest) := by
  rw [List.append_assoc]
  exact mergeBytes_encode b rest hb

theorem bytesMerge3SpecW_pre_eq {A : RustAlloc} (img : Obj.Image) (x : Prost.BytesMergeGhost) (s : State) :
    (bytesMerge3SpecW A img).pre x s =
      ⌜(img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧
        (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
        s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62⌝ ∗
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ Prost.sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool ∗ stackAt s.sp bytesMerge3Stack) := by
  dsimp only [bytesMerge3SpecW, Spec.inImage, bytesMerge3RawSpecW]
  rw [← sepConj_assoc, pure_sepConj_pure]

abbrev OverDecCbzPost (s : State) (g : OverDecG) (sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ emp) ∧
  sf.sp = g.q ∧
  sf.trace = s.trace ∧
  sf.readReg64 .x19 = g.r19 ∧
  sf.readReg64 .x20 = g.r20 ∧
  sf.readReg64 .x21 = g.q + 0x930#64 ∧
  sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧
  sf.readReg64 .x26 = g.r26 ∧
  sf.readReg64 .x27 = g.prevPtr ∧
  sf.readReg64 .x28 = g.q + 0xa90#64 ∧
  sf.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_22d8_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22d8#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8920 8920
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  dsimp only [OverDecCbzPost, State.setPC, State.readReg64]
  exact ⟨Entails.refl _, hsp, rfl, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hx28, hx29,
    Arm64.calleeSavedVRegs_setPC s _⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_22c4_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22c4#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8900 8900
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  dsimp only [OverDecCbzPost, State.setPC, State.readReg64]
  exact ⟨Entails.refl _, hsp, rfl, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hx28, hx29,
    Arm64.calleeSavedVRegs_setPC s _⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_229c_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x229c#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8860 8860
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  dsimp only [OverDecCbzPost, State.setPC, State.readReg64]
  exact ⟨Entails.refl _, hsp, rfl, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hx28, hx29,
    Arm64.calleeSavedVRegs_setPC s _⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_21e0_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x21e0#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8672 8672
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  dsimp only [OverDecCbzPost, State.setPC, State.readReg64]
  exact ⟨Entails.refl _, hsp, rfl, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hx28, hx29,
    Arm64.calleeSavedVRegs_setPC s _⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_220c_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x220c#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8716 8716
  dsimp only [contractProg] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  dsimp only [OverDecCbzPost, State.setPC, State.readReg64]
  exact ⟨Entails.refl _, hsp, rfl, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hx28, hx29,
    Arm64.calleeSavedVRegs_setPC s _⟩

/-- Single-instruction `SepWP` for `cbz x0, +0x2160` at the five bytes-arm return offsets. -/
theorem overDec_cbz_wp (b : BitVec 64) (ext : String → Option (State → State))
    (retOff : BitVec 64) (s : State) (g : OverDecG)
    (hret : retOff = 0x22d8#64 ∨ retOff = 0x22c4#64 ∨ retOff = 0x229c#64 ∨
            retOff = 0x21e0#64 ∨ retOff = 0x220c#64)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + retOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s emp
      (OverDecCbzPost s g) := by
  rcases hret with rfl | rfl | rfl | rfl | rfl
  · exact overDec_cbz_22d8_wp b ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_22c4_wp b ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_229c_wp b ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_21e0_wp b ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_220c_wp b ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29

/-- Shared `bytes::merge [local#6]` call and `cbz x0, +0x2160` step for all five bytes arms. -/
theorem overDec_bytesMerge6_call_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (retOff valPtr : BitVec 64)
    (oldBs b rest : List (BitVec 8))
    (restSS : SepProp)
    (s0 s1 : State) (g : OverDecG) (v v' : SSGQ) (fl : GenFieldQ)
    (hret : retOff = 0x22d8#64 ∨ retOff = 0x22c4#64 ∨ retOff = 0x229c#64 ∨
            retOff = 0x21e0#64 ∨ retOff = 0x220c#64)
    (hpay : fl.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b)
    (hb : b.length < 2 ^ 64)
    (hsuf : (fl.enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hsplit : prostSSGQAt A (g.q + 0x930#64) v = vecU8 A valPtr oldBs ∗ restSS)
    (hunsplit : vecU8 A valPtr b ∗ restSS = prostSSGQAt A (g.q + 0x930#64) v')
    (hpc1 : s1.pc = (contractProg img.base ext).fnAddr bytesMerge6Name)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = g.q)
    (hal1 : (s1.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hF1 : img.FrozenLoaded s1)
    (hsym1 : s1.symtab = img.symtab)
    (hx0_1 : s1.readReg64 .x0 = 2#64)
    (hx1_1 : s1.readReg64 .x1 = valPtr)
    (hx2_1 : s1.readReg64 .x2 = g.q + 0xbe8#64)
    (hx19_1 : s1.readReg64 .x19 = g.r19)
    (hx20_1 : s1.readReg64 .x20 = g.r20)
    (hx21_1 : s1.readReg64 .x21 = g.q + 0x930#64)
    (hx24_1 : s1.readReg64 .x24 = 1#64)
    (hx25_1 : s1.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26_1 : s1.readReg64 .x26 = g.r26)
    (hx27_1 : s1.readReg64 .x27 = g.prevPtr)
    (hx28_1 : s1.readReg64 .x28 = g.q + 0xa90#64)
    (hx29_1 : s1.readReg64 .x29 = g.q + 0xc70#64)
    (hx30_1 : s1.readReg64 .x30 = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + retOff)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs g.sv) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s1
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest v'))
      (PanicOomProp s0) := by
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDec_payload_suffix_and_len hsuf hlen
  have hmerge : mergeBytes .lengthDelimited (fl.payload ++ rest) = some (b, rest) := by
    rw [hpay]
    exact overDec_mergeBytes_eq b rest hb
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned] using hal1
  have hcur_split :
      Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.payload ++ rest) =
        (g.encPtr ↦ₛ pfx) ∗
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.payload ++ rest) := by
    conv_lhs => arg 3; rw [hpfx]
    exact sliceCursorAfter_split_sub (g.q + 0x920#64) g.encPtr pfx (fl.payload ++ rest)
  unfold overDecHeapExt
  rw [hcur_split, hsplit, stackAt_overDec_to_bytesMerge3 g.q]
  unfold vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  let xbm : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, oldBs, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 pfx.length, fl.payload ++ rest⟩
  have hcall : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr bytesMerge6Name) (bytesMerge3SpecW A img) := hBM6W
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 xbm.wt.toNat := by
    rw [hx0_1]; rfl
  have hφ : (img.FrozenLoaded s1 ∧ s1.symtab = img.symtab) ∧
      (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 xbm.wt.toNat ∧
      s1.readReg64 .x1 = xbm.valPtr ∧ s1.readReg64 .x2 = xbm.bufRef ∧ xbm.bs.length < 2 ^ 62 :=
    ⟨⟨hF1, hsym1⟩, hx0_w8, hx1_1, hx2_1, hpay_len⟩
  refine SepWPp_call_frame_frozen_oom (x := xbm)
    (T := vecU8At A valPtr cap0 ptr0 oldBs ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.payload ++ rest) ∗
      A.pool ∗ stackAt g.q bytesMerge3Stack)
    hF1 hsym1 htr1 hcall hpc1 hrun1 hsp1_al hx30_1
    (by rw [bytesMerge3SpecW_pre_eq, hsp1])
    hφ
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [bytesMerge3SpecW, Spec.inImage, bytesMerge3RawSpecW, xbm]
  rw [hmerge]
  dsimp only
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp_weaken_frame
    (P₁ := ⌜s2.readReg64 .x0 = 0#64⌝) (P₂ := ⌜s2.readReg64 .x0 = 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hx0_2 => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs,
    hx29_cs, hvregs_cs⟩
  have hx19_2 : s2.readReg64 .x19 = g.r19 := hx19_cs.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = g.r20 := hx20_cs.trans hx20_1
  have hx21_2 : s2.readReg64 .x21 = g.q + 0x930#64 := hx21_cs.trans hx21_1
  have hx24_2 : s2.readReg64 .x24 = 1#64 := hx24_cs.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 0xffffffffffffffff#64 := hx25_cs.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = g.r26 := hx26_cs.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = g.prevPtr := hx27_cs.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = g.q + 0xa90#64 := hx28_cs.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = g.q + 0xc70#64 := hx29_cs.trans hx29_1
  have hstep_cbz := overDec_cbz_wp img.base ext retOff s2 g hret
    hpc2 hrun2 hsp2 hx0_2 hx19_2 hx20_2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  refine SepWPp_ret_sepWP_frame hF2 hsym2 hstep_cbz
    (by rw [emp_sepConj]) fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp1]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hFf, hsymf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    hvregs_f.trans (hvregs_cs.trans hvregs_1)⟩, ?_⟩
  have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A valPtr cap' ptr' b) =
      vecU8 A valPtr b := rfl
  have hcur_unsplit :
      (g.encPtr ↦ₛ pfx) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.payload ++ rest) rest =
      Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest := by
    rw [sliceCursorAfter_unsplit_sub (g.q + 0x920#64) g.encPtr pfx fl.payload rest, ← hpfx]
  refine Entails.of_eq ?_
  rw [emp_sepConj, hvec, ← hcur_unsplit, ← hunsplit]
  ac_rfl
abbrev overDec_bytesMerge6_call := @overDec_bytesMerge6_call_ext A0

/-! ## Tag 2 (`local_identity_public`, `+0x22cc → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag2_pre_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22cc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr bytesMerge6Name)
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧
        s1.readReg64 .x1 = g.q + 0x930#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22d8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8908 8916
  dsimp only [contractProg] at hpc ⊢
  rw [← overDec_bytesMerge6_addr_eq b (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm], by simp only [arm64_norm],
    by simp only [hx0', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm], by simp only [hx21', arm64_norm],
    by simp only [hx24', arm64_norm], by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm], by simp only [hx29', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Tag 2 arm (`+0x22cc → +0x2160`) decoding `local_identity_public` at `g.q + 0x930`. -/
theorem overDecArm_tag2_lik_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (b rest : List (BitVec 8))
    (hok : (GenFieldQ.base (.lik b)).Ok)
    (hsuf : ((GenFieldQ.base (.lik b)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff (.base (.lik b))) s)
    (hx0 : s.readReg64 .x0 = overDecWt (.base (.lik b))) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.base (.lik b)).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.base (.lik b)))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  dsimp only [overDecArmOff] at hpc
  have hx0' : s.readReg64 .x0 = 2#64 := hx0
  have hstep_pre := overDec_arm_tag2_pre_wp img.base ext s g
    hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstep_pre (by rw [emp_sepConj])
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rw [emp_sepConj]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  have hal1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1, ← hsp]
  have hb_lt : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok, GenField.Ok] at hok
    omega
  exact overDec_bytesMerge6_call_ext img ext hBM6W 0x22d8#64 (g.q + 0x930#64)
    v.base.lik b rest (prostSSGQRest2 A (g.q + 0x930#64) v)
    s0 s1 g v (v.apply (.base (.lik b))) (.base (.lik b))
    (Or.inl rfl) rfl hb_lt hsuf hlen
    (prostSSGQAt_eq_lik_sep_rest2 A (g.q + 0x930#64) v)
    (prostSSGQAt_eq_lik_sep_rest2 A (g.q + 0x930#64) (v.apply (.base (.lik b)))).symm
    hpc1 hrun1 hsp1 hal1 (htr1.trans htr) hF1 hsym1
    hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
    (hvregs_1.trans hvregs)
abbrev overDecArm_tag2_lik_ok := @overDecArm_tag2_lik_ok_ext A0

/-! ## Tag 3 (`remote_identity_public`, `+0x22b8 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag3_pre_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22b8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr bytesMerge6Name)
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧
        s1.readReg64 .x1 = g.q + 0x930#64 + 0x18#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x22c4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8888 8896
  dsimp only [contractProg] at hpc ⊢
  rw [← overDec_bytesMerge6_addr_eq b (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm], by simp only [arm64_norm],
    by simp only [hx0', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm], by simp only [hx21', arm64_norm],
    by simp only [hx24', arm64_norm], by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm], by simp only [hx29', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Tag 3 arm (`+0x22b8 → +0x2160`) decoding `remote_identity_public` at `g.q + 0x948`. -/
theorem overDecArm_tag3_rik_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (b rest : List (BitVec 8))
    (hok : (GenFieldQ.base (.rik b)).Ok)
    (hsuf : ((GenFieldQ.base (.rik b)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff (.base (.rik b))) s)
    (hx0 : s.readReg64 .x0 = overDecWt (.base (.rik b))) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.base (.rik b)).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.base (.rik b)))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  dsimp only [overDecArmOff] at hpc
  have hx0' : s.readReg64 .x0 = 2#64 := hx0
  have hstep_pre := overDec_arm_tag3_pre_wp img.base ext s g
    hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstep_pre (by rw [emp_sepConj])
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rw [emp_sepConj]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  have hal1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1, ← hsp]
  have hb_lt : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok, GenField.Ok] at hok
    omega
  exact overDec_bytesMerge6_call_ext img ext hBM6W 0x22c4#64 (g.q + 0x930#64 + 0x18#64)
    v.base.rik b rest (prostSSGQRest3 A (g.q + 0x930#64) v)
    s0 s1 g v (v.apply (.base (.rik b))) (.base (.rik b))
    (Or.inr (Or.inl rfl)) rfl hb_lt hsuf hlen
    (prostSSGQAt_eq_rik_sep_rest3 A (g.q + 0x930#64) v)
    (prostSSGQAt_eq_rik_sep_rest3 A (g.q + 0x930#64) (v.apply (.base (.rik b)))).symm
    hpc1 hrun1 hsp1 hal1 (htr1.trans htr) hF1 hsym1
    hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
    (hvregs_1.trans hvregs)
abbrev overDecArm_tag3_rik_ok := @overDecArm_tag3_rik_ok_ext A0

/-! ## Tag 4 (`root_key`, `+0x2290 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag4_pre_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2290#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr bytesMerge6Name)
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧
        s1.readReg64 .x1 = g.q + 0x930#64 + 0x30#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x229c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8848 8856
  dsimp only [contractProg] at hpc ⊢
  rw [← overDec_bytesMerge6_addr_eq b (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm], by simp only [arm64_norm],
    by simp only [hx0', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm], by simp only [hx21', arm64_norm],
    by simp only [hx24', arm64_norm], by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm], by simp only [hx29', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Tag 4 arm (`+0x2290 → +0x2160`) decoding `root_key` at `g.q + 0x960`. -/
theorem overDecArm_tag4_root_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (b rest : List (BitVec 8))
    (hok : (GenFieldQ.base (.root b)).Ok)
    (hsuf : ((GenFieldQ.base (.root b)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff (.base (.root b))) s)
    (hx0 : s.readReg64 .x0 = overDecWt (.base (.root b))) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.base (.root b)).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.base (.root b)))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  dsimp only [overDecArmOff] at hpc
  have hx0' : s.readReg64 .x0 = 2#64 := hx0
  have hstep_pre := overDec_arm_tag4_pre_wp img.base ext s g
    hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstep_pre (by rw [emp_sepConj])
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rw [emp_sepConj]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  have hal1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1, ← hsp]
  have hb_lt : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok, GenField.Ok] at hok
    omega
  exact overDec_bytesMerge6_call_ext img ext hBM6W 0x229c#64 (g.q + 0x930#64 + 0x30#64)
    v.base.root b rest (prostSSGQRest4 A (g.q + 0x930#64) v)
    s0 s1 g v (v.apply (.base (.root b))) (.base (.root b))
    (Or.inr (Or.inr (Or.inl rfl))) rfl hb_lt hsuf hlen
    (prostSSGQAt_eq_root_sep_rest4 A (g.q + 0x930#64) v)
    (prostSSGQAt_eq_root_sep_rest4 A (g.q + 0x930#64) (v.apply (.base (.root b)))).symm
    hpc1 hrun1 hsp1 hal1 (htr1.trans htr) hF1 hsym1
    hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
    (hvregs_1.trans hvregs)
abbrev overDecArm_tag4_root_ok := @overDecArm_tag4_root_ok_ext A0

/-! ## Tag 13 (`alice_base_key`, `+0x21d4 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag13_pre_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x21d4#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr bytesMerge6Name)
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧
        s1.readReg64 .x1 = g.q + 0x930#64 + 0x60#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x21e0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8660 8668
  dsimp only [contractProg] at hpc ⊢
  rw [← overDec_bytesMerge6_addr_eq b (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm], by simp only [arm64_norm],
    by simp only [hx0', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm], by simp only [hx21', arm64_norm],
    by simp only [hx24', arm64_norm], by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm], by simp only [hx29', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Tag 13 arm (`+0x21d4 → +0x2160`) decoding `alice_base_key` at `g.q + 0x990`. -/
theorem overDecArm_tag13_abk_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (b rest : List (BitVec 8))
    (hok : (GenFieldQ.abk b).Ok)
    (hsuf : ((GenFieldQ.abk b).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff (.abk b)) s)
    (hx0 : s.readReg64 .x0 = overDecWt (.abk b)) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.abk b).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.abk b))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  dsimp only [overDecArmOff] at hpc
  have hx0' : s.readReg64 .x0 = 2#64 := hx0
  have hstep_pre := overDec_arm_tag13_pre_wp img.base ext s g
    hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstep_pre (by rw [emp_sepConj])
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rw [emp_sepConj]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  have hal1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1, ← hsp]
  have hb_lt : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok] at hok
    omega
  exact overDec_bytesMerge6_call_ext img ext hBM6W 0x21e0#64 (g.q + 0x930#64 + 0x60#64)
    v.ext.abk b rest (prostSSGQRest13 A (g.q + 0x930#64) v)
    s0 s1 g v (v.apply (.abk b)) (.abk b)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl hb_lt hsuf hlen
    (prostSSGQAt_eq_abk_sep_rest13 A (g.q + 0x930#64) v)
    (prostSSGQAt_eq_abk_sep_rest13 A (g.q + 0x930#64) (v.apply (.abk b))).symm
    hpc1 hrun1 hsp1 hal1 (htr1.trans htr) hF1 hsym1
    hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
    (hvregs_1.trans hvregs)
abbrev overDecArm_tag13_abk_ok := @overDecArm_tag13_abk_ok_ext A0

/-! ## Tag 15 (`pq_ratchet_state`, `+0x2200 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag15_pre_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2200#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr bytesMerge6Name)
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧
        s1.readReg64 .x1 = g.q + 0x930#64 + 0x78#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x220c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 8704 8712
  dsimp only [contractProg] at hpc ⊢
  rw [← overDec_bytesMerge6_addr_eq b (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm], by simp only [arm64_norm],
    by simp only [hx0', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm], by simp only [hx21', arm64_norm],
    by simp only [hx24', arm64_norm], by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm], by simp only [hx29', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Tag 15 arm (`+0x2200 → +0x2160`) decoding `pq_ratchet_state` at `g.q + 0x9a8`. -/
theorem overDecArm_tag15_pq_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (b rest : List (BitVec 8))
    (hok : (GenFieldQ.pq b).Ok)
    (hsuf : ((GenFieldQ.pq b).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff (.pq b)) s)
    (hx0 : s.readReg64 .x0 = overDecWt (.pq b)) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g ((GenFieldQ.pq b).payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.pq b))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  dsimp only [overDecArmOff] at hpc
  have hx0' : s.readReg64 .x0 = 2#64 := hx0
  have hstep_pre := overDec_arm_tag15_pre_wp img.base ext s g
    hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hF hsym hstep_pre (by rw [emp_sepConj])
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rw [emp_sepConj]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  have hal1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1, ← hsp]
  have hb_lt : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok] at hok
    omega
  exact overDec_bytesMerge6_call_ext img ext hBM6W 0x220c#64 (g.q + 0x930#64 + 0x78#64)
    v.ext.pq b rest (prostSSGQRest15 A (g.q + 0x930#64) v)
    s0 s1 g v (v.apply (.pq b)) (.pq b)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl hb_lt hsuf hlen
    (prostSSGQAt_eq_pq_sep_rest15 A (g.q + 0x930#64) v)
    (prostSSGQAt_eq_pq_sep_rest15 A (g.q + 0x930#64) (v.apply (.pq b))).symm
    hpc1 hrun1 hsp1 hal1 (htr1.trans htr) hF1 hsym1
    hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
    (hvregs_1.trans hvregs)
abbrev overDecArm_tag15_pq_ok := @overDecArm_tag15_pq_ok_ext A0

/-! ## Combined Bytes-Arm Theorem -/

/-- Combined `OverDecBytesField` decode-arm specification from `BytesMerge6OkExtW`. -/
theorem overDecArm_bytes_of_bm6w_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hBM6W : BytesMerge6OkExtW img A ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecBytesField fl) (hok : fl.Ok)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0) := by
  cases fl with
  | base f =>
    cases f with
    | lik b => exact overDecArm_tag2_lik_ok_ext img ext hBM6W s0 s g v b rest hok hsuf hlen hregs hx0
    | rik b => exact overDecArm_tag3_rik_ok_ext img ext hBM6W s0 s g v b rest hok hsuf hlen hregs hx0
    | root b => exact overDecArm_tag4_root_ok_ext img ext hBM6W s0 s g v b rest hok hsuf hlen hregs hx0
    | version _ | prevCounter _ | sender _ | recv _ | pending _ => cases hP
  | abk b => exact overDecArm_tag13_abk_ok_ext img ext hBM6W s0 s g v b rest hok hsuf hlen hregs hx0
  | pq b => exact overDecArm_tag15_pq_ok_ext img ext hBM6W s0 s g v b rest hok hsuf hlen hregs hx0
  | pendingId _ _ | pendingSpk _ _ _ | remReg _ | locReg _ | kyber _ _ => cases hP
abbrev overDecArm_bytes_of_bm6w := @overDecArm_bytes_of_bm6w_ext A0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
