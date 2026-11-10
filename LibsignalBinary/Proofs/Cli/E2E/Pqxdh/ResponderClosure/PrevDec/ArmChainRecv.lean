/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Tag 7 (`receiver_chains`) Arm of Inlined `SessionStructure::decode`

Proves the tag-7 (`receiver_chains`, `+0x22e0 → +0x2160`) decode arm in
`message_decrypt_prekey::<Coins>::{closure#0}`, invoking `message::merge<Chain> [local#5]` on
`q + 0xbf0` and composing with Segment B (`OverDecRecvSegBStmt`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField ChainMergeGenGhost)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ExtraGQ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
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
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF hsym hpc hrun hsp hlr
    (fun R hm => by
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sf code R' _ hpost => by rw [hexit_false] at hpost; exact allowPanic_not_exited hpost)
    (fun sf _ _ => by rw [hpan_eq]; exact allowPanic_oom_of_trace_eq htr)
    (fun sm hpcm hrunm hspm hcsm hF' hsym' =>
      hnext sm hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hF' hsym')
    (fun sf R' _ _hoom_post => by
      rw [hoom_false] at _hoom_post
      exact (not_satisfies_false_sepConj _hoom_post).elim)

/-! ## Pre-Call Step (`+0x22e0 → merge<Chain> [local#5]`) -/

theorem chainMerge3_call_addr_eq (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr decryptPrekeyClosureName +
      bv% ((2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]") -
           (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2 ^ 64) =
      (libsignalSessionCode.rebase b H).fnAddr chainMerge3Name := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, decryptPrekeyClosure_fnOff,
    (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")]
  bv_omega

/-! ## Stack, Cursor, and `memRegion` Split Helpers -/

set_option maxHeartbeats 400000 in
theorem stackAt_overDecStackX_eq_chainMerge3StackX (q : BitVec 64) :
    stackAt q overDecStackX =
      memRegion (q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX) ∗
        stackAt q chainMerge3StackX :=
  ProofLib.stackAt_split_bottom q chainMerge3StackX
    (overDecStackX - chainMerge3StackX) (by decide)

set_option maxHeartbeats 400000 in
theorem suffix_payload_of_suffix_enc_recv {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) :
    (fl.payload ++ rest) <:+ enc := by
  rcases hsuf with ⟨pre, hpre⟩
  refine ⟨pre ++ encodeKey fl.tag fl.wt, ?_⟩
  rw [List.append_assoc, ← List.append_assoc (encodeKey fl.tag fl.wt), ← GenFieldQ.enc, hpre]

set_option maxHeartbeats 400000 in
theorem payload_append_length_lt62_of_suffix {pfx rest enc : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    (pfx ++ rest).length < 2 ^ 62 := by
  rcases hsuf with ⟨pre, hpre⟩
  have hle : (pfx ++ rest).length ≤ enc.length := by
    simp only [← hpre, List.length_append]; omega
  omega

set_option maxHeartbeats 400000 in
theorem sliceCursorAfter_split_of_suffix_recv (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ bs) :
    sliceCursorAfter slot ptr bs (pfx ++ rest) =
      sliceCursorAt slot (ptr + BitVec.ofNat 64 (bs.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
        (ptr ↦ₛ bs.take (bs.length - (pfx ++ rest).length)) := by
  rcases hsuf with ⟨pre, hpre⟩
  have hsub : bs.length - (pfx ++ rest).length = pre.length := by
    rw [← hpre, List.length_append]; omega
  have htake : bs.take (bs.length - (pfx ++ rest).length) = pre := by
    rw [hsub, ← hpre, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 pre.length) ↦ₛ (pfx ++ rest)) := by
    conv_lhs => rw [← hpre]
    exact pointsToBytes_append ptr pre (pfx ++ rest)
  unfold sliceCursorAfter sliceCursorAt
  rw [htake, hsub, hpts]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem sliceCursorAfter_unsplit_of_suffix_recv (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ bs) :
    sliceCursorAfter slot (ptr + BitVec.ofNat 64 (bs.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      (ptr ↦ₛ bs.take (bs.length - (pfx ++ rest).length)) =
      sliceCursorAfter slot ptr bs rest := by
  rcases hsuf with ⟨pre, hpre⟩
  have hsub : bs.length - (pfx ++ rest).length = pre.length := by
    rw [← hpre, List.length_append]; omega
  have htake : bs.take (bs.length - (pfx ++ rest).length) = pre := by
    rw [hsub, ← hpre, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hpay_sub : (pfx ++ rest).length - rest.length = pfx.length := by
    rw [List.length_append]; omega
  have hbs_sub : bs.length - rest.length = pre.length + pfx.length := by
    rw [← hpre, List.length_append, List.length_append]; omega
  have hptr : ptr + BitVec.ofNat 64 pre.length + BitVec.ofNat 64 pfx.length =
      ptr + BitVec.ofNat 64 (pre.length + pfx.length) := by
    rw [BitVec.ofNat_add]; bv_omega
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 pre.length) ↦ₛ (pfx ++ rest)) := by
    conv_lhs => rw [← hpre]
    exact pointsToBytes_append ptr pre (pfx ++ rest)
  unfold sliceCursorAfter
  rw [htake, hsub, hpay_sub, hbs_sub, hptr, hpts]
  ac_rfl

set_option maxHeartbeats 400000 in
private theorem memRegion_succ8_recv (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (8 + n) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [ProofLib.memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

set_option maxHeartbeats 400000 in
theorem memRegion128_bf0_split_80_24_24 (q : BitVec 64) :
    memRegion (q + 0xbf0#64) 128 =
      memRegion (q + 0xbf0#64) 80 ∗
      memRegion (q + 0xc40#64) 24 ∗
      memRegion (q + 0xc58#64) 24 := by
  have s1 := ProofLib.memRegion_split (q + 0xbf0#64) 80 48 (by omega)
  have s2 := ProofLib.memRegion_split (q + 0xc40#64) 24 24 (by omega)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at s1 s2
  rw [s1, s2]

set_option maxHeartbeats 400000 in
theorem memRegion80_bf0_eq_cells10 (q : BitVec 64) :
    memRegion (q + 0xbf0#64) 80 =
      ∃∗ u9 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64,
      ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((q + 0xbf0#64) ↦₆₄ u0) ∗
        ((q + 0xbf8#64) ↦₆₄ u1) ∗ ((q + 0xc00#64) ↦₆₄ u2) ∗ ((q + 0xc08#64) ↦₆₄ u3) ∗
        ((q + 0xc10#64) ↦₆₄ u4) ∗ ((q + 0xc18#64) ↦₆₄ u5) ∗ ((q + 0xc20#64) ↦₆₄ u6) ∗
        ((q + 0xc28#64) ↦₆₄ u7) ∗ ((q + 0xc30#64) ↦₆₄ u8) ∗ ((q + 0xc38#64) ↦₆₄ u9) := by
  have s0 := memRegion_succ8_recv (q + 0xbf0#64) 72 (by omega)
  have s1 := memRegion_succ8_recv (q + 0xbf8#64) 64 (by omega)
  have s2 := memRegion_succ8_recv (q + 0xc00#64) 56 (by omega)
  have s3 := memRegion_succ8_recv (q + 0xc08#64) 48 (by omega)
  have s4 := memRegion_succ8_recv (q + 0xc10#64) 40 (by omega)
  have s5 := memRegion_succ8_recv (q + 0xc18#64) 32 (by omega)
  have s6 := memRegion_succ8_recv (q + 0xc20#64) 24 (by omega)
  have s7 := memRegion_succ8_recv (q + 0xc28#64) 16 (by omega)
  have s8 := memRegion_succ8_recv (q + 0xc30#64) 8 (by omega)
  have s9 := ProofLib.memRegion_eight (q + 0xc38#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at s0 s1 s2 s3 s4 s5 s6 s7 s8
  rw [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

set_option maxHeartbeats 400000 in
theorem default_cells_bf0_entail_chain3GAt_ext (A : RustAlloc) (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      chain3GAt A (q + 0xbf0#64) ChainG.empty := by
  have h := default_cells_entail_chain3GAt A (q + 0xbf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h ⊢
  exact h

theorem default_cells_bf0_entail_chain3GAt (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      chain3GAt CryptoVerification.E2E.Record.A0 (q + 0xbf0#64) ChainG.empty :=
  default_cells_bf0_entail_chain3GAt_ext CryptoVerification.E2E.Record.A0 q

def OverDecSavedRegs (g : OverDecG) (s : State) : Prop :=
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

set_option maxHeartbeats 400000 in
theorem overDecSavedRegs_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegs g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegs g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

set_option maxHeartbeats 400000 in
theorem overDecRecv_pre_step {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG} (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    (hregs : OverDecRegs img ext s0 g 0x22e0#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr chainMerge3Name) s
      (((g.q + 0xbf0#64) ↦₆₄ u0) ∗
        ((g.q + 0xbf8#64) ↦₆₄ u1) ∗ ((g.q + 0xc00#64) ↦₆₄ u2) ∗ ((g.q + 0xc08#64) ↦₆₄ u3) ∗
        ((g.q + 0xc10#64) ↦₆₄ u4) ∗ ((g.q + 0xc18#64) ↦₆₄ u5) ∗ ((g.q + 0xc20#64) ↦₆₄ u6) ∗
        ((g.q + 0xc28#64) ↦₆₄ u7) ∗ ((g.q + 0xc30#64) ↦₆₄ u8) ∗ ((g.q + 0xc38#64) ↦₆₄ u9))
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap)) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr =
          (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2310#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _, _,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have h24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := h24
  have h25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := h25
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 0x22e0 0x230c
  dsimp only [contractProg] at hpc ⊢
  rw [← chainMerge3_call_addr_eq img.base (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem overDecRecv_pre_step_80 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegs img ext s0 g 0x22e0#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr chainMerge3Name) s
      (memRegion (g.q + 0xbf0#64) 80)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap)) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr =
          (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2310#64 ∧
        OverDecSavedRegs g s1) := by
  rw [memRegion80_bf0_eq_cells10 g.q]
  refine SepWP.exists_elim fun u9 => SepWP.exists_elim fun u8 =>
    SepWP.exists_elim fun u7 => SepWP.exists_elim fun u6 =>
    SepWP.exists_elim fun u5 => SepWP.exists_elim fun u4 =>
    SepWP.exists_elim fun u3 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  exact overDecRecv_pre_step u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 hregs hx0

/-! ## Arm Assembly (`+0x22e0 → +0x2160`) -/

def overDecRecvFrameRest (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRest g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQAt CryptoVerification.E2E.Record.A0 (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX) ∗
    CryptoVerification.E2E.Record.A0.pool

set_option maxHeartbeats 400000 in
theorem overDecHeap_eq_recv_split (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    overDecHeap g (c.payload ++ rest) v =
      memRegion (g.q + 0xbf0#64) 80 ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRest g v (c.payload ++ rest).length) := by
  unfold overDecHeap overDecHeapExt overDecRecvFrameRest
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecRecvPostMergeHeap_eq_unsplit (g : OverDecG) (v : SSGQ) {c : ChainG}
    {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt CryptoVerification.E2E.Record.A0 (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      stackAt g.q chainMerge3StackX ∗
      overDecRecvFrameRest g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeap g rest v c := by
  unfold overDecRecvPostMergeHeap overDecRecvPostMergeHeapExt overDecRecvFrameRest
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecArm_recv (hsegB : OverDecRecvSegBStmt)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img CryptoVerification.E2E.Record.A0 ext)
    (hChain3 : Chain3OkAtW img ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hfl : OverDecRecvField fl) (hok : fl.Ok) (hfresh : fl.Fresh v)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl)
    (_hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat)) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeap g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0) := by
  have hfl_eq : ∃ c : ChainG, fl = .base (.recv c) := by
    cases fl with
    | base bf =>
      cases bf <;> try contradiction
      exact ⟨_, rfl⟩
    | _ => contradiction
  rcases hfl_eq with ⟨c, rfl⟩
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  change OverDecRegs img ext s0 g 0x22e0#64 s at hregs
  change s.readReg64 .x0 = 2#64 at hx0
  rw [hpay_eq, overDecHeap_eq_recv_split g v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, hF, hsym, hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hregs' : OverDecRegs img ext s0 g 0x22e0#64 s :=
    ⟨hpc, hrun, hsp, hsp_align, htr, hF, hsym, hsaved⟩
  refine SepWPp_bind_sepWP_frame hF hsym (overDecRecv_pre_step_80 hregs' hx0)
    rfl
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  rw [← sepConj_assoc]
  refine SepWPp_weaken_frame (default_cells_bf0_entail_chain3GAt g.q) rfl ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length)
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by simp [hx0_1]
  refine SepWPp_call_frame_frozen_oom
    (x := (⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64, curPtr, rest⟩ : ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      img.FrozenLoaded s1 ∧ s1.symtab = img.symtab)
    (T := chain3GAt CryptoVerification.E2E.Record.A0 (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (c.payload ++ rest) ∗
      stackAt g.q chainMerge3StackX)
    (F := overDecRecvFrameRest g v (c.payload ++ rest).length)
    hF1 hsym1 htr1 hChain3 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [chainMerge3SpecAtW]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay, hF1, hsym1⟩
    (by dsimp only [curPtr]; ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [chainMerge3SpecAtW]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs g s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  have hregs2 : OverDecRegs img ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hF2, hsym2, hsaved2⟩
  have hpost_eq :
      prostChainGAt CryptoVerification.E2E.Record.A0 (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64) curPtr (c.payload ++ rest) rest ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRest g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeap g rest v c := by
    dsimp only [curPtr]
    exact overDecRecvPostMergeHeap_eq_unsplit g v hsuf_pay
  rw [hpost_eq]
  exact hsegB img ext hLoads hAC s0 s2 g v c rest hok hfresh hsuf hlen hregs2 hx0_2

/-- Tag 7 (`receiver_chains`) decode arm under `AllocContractsX`, parameterized by
`OverDecRecvSegBStmt` and `Chain3OkAtW`. -/
theorem overDecArm_recv_of_chain3
    (hsegB : OverDecRecvSegBStmt)
    (hChain3 : ∀ img ext, Obj.Loads libsignalSessionImage img →
      CryptoVerification.LibsignalTripleRatchet.AllocContractsX img
        CryptoVerification.E2E.Record.A0 ext →
      Chain3OkAtW img ext) :
    OverDecArmStmtTR OverDecRecvField :=
  fun img ext hLoads hAC s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 hx22 =>
    overDecArm_recv hsegB img ext hLoads (c3_stage1Alloc_of_allocContractsX hAC)
      (hChain3 img ext hLoads hAC) s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 hx22

/-! ## Allocator-Polymorphic Tag 7 Arm (`+0x22e0 → +0x2160`) -/

def overDecRecvFrameRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX)

set_option maxHeartbeats 400000 in
theorem overDecHeap_eq_recv_split_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ) {c : ChainG}
    {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    overDecHeapExt A g (c.payload ++ rest) v =
      memRegion (g.q + 0xbf0#64) 80 ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        A.pool ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRestExt A g v (c.payload ++ rest).length) := by
  unfold overDecHeapExt overDecRecvFrameRestExt
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecRecvPostMergeHeap_eq_unsplit_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ)
    {c : ChainG} {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt A (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      A.pool ∗
      stackAt g.q chainMerge3StackX ∗
      overDecRecvFrameRestExt A g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapExt A g rest v c := by
  unfold overDecRecvPostMergeHeapExt overDecRecvFrameRestExt
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecArm_recv_ext {A : RustAlloc} (hsegB : OverDecRecvSegBStmtExt A)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hChain3 : Chain3OkAtWExt A img ext)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hfl : OverDecRecvField fl) (hok : fl.Ok) (hfresh : fl.Fresh v)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl)
    (_hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat)) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0) := by
  have hfl_eq : ∃ c : ChainG, fl = .base (.recv c) := by
    cases fl with
    | base bf =>
      cases bf <;> try contradiction
      exact ⟨_, rfl⟩
    | _ => contradiction
  rcases hfl_eq with ⟨c, rfl⟩
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  change OverDecRegs img ext s0 g 0x22e0#64 s at hregs
  change s.readReg64 .x0 = 2#64 at hx0
  rw [hpay_eq, overDecHeap_eq_recv_split_ext A g v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, hF, hsym, hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hregs' : OverDecRegs img ext s0 g 0x22e0#64 s :=
    ⟨hpc, hrun, hsp, hsp_align, htr, hF, hsym, hsaved⟩
  refine SepWPp_bind_sepWP_frame hF hsym (overDecRecv_pre_step_80 hregs' hx0)
    rfl
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  rw [← sepConj_assoc]
  refine SepWPp_weaken_frame (default_cells_bf0_entail_chain3GAt_ext A g.q) rfl ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length)
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by simp [hx0_1]
  refine SepWPp_call_frame_frozen_oom
    (x := (⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64, curPtr, rest⟩ : ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      img.FrozenLoaded s1 ∧ s1.symtab = img.symtab)
    (T := chain3GAt A (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (c.payload ++ rest) ∗
      A.pool ∗
      stackAt g.q chainMerge3StackX)
    (F := overDecRecvFrameRestExt A g v (c.payload ++ rest).length)
    hF1 hsym1 htr1 hChain3 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [chainMerge3SpecAtWExt]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay, hF1, hsym1⟩
    (by dsimp only [curPtr]; ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [chainMerge3SpecAtWExt]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs g s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  have hregs2 : OverDecRegs img ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hF2, hsym2, hsaved2⟩
  have hpost_eq :
      prostChainGAt A (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64) curPtr (c.payload ++ rest) rest ∗
        A.pool ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRestExt A g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapExt A g rest v c := by
    dsimp only [curPtr]
    exact overDecRecvPostMergeHeap_eq_unsplit_ext A g v hsuf_pay
  rw [hpost_eq]
  exact hsegB img ext hLoads hAC s0 s2 g v c rest hok hfresh hsuf hlen hregs2 hx0_2

/-- Allocator-polymorphic tag 7 (`receiver_chains`) decode arm parameterized by
`OverDecRecvSegBStmtExt A` and `Chain3OkAtWExt A`. -/
theorem overDecArm_recv_of_segB_chain3_ext {A : RustAlloc}
    (hsegB : OverDecRecvSegBStmtExt A)
    (hChain3 : ∀ img ext, Obj.Loads libsignalSessionImage img →
      CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
      Chain3OkAtWExt A img ext) :
    OverDecArmStmtTRExt A OverDecRecvField :=
  fun img ext hLoads hAC s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 hx22 =>
    overDecArm_recv_ext hsegB img ext hLoads (c3_stage1Alloc_of_allocContractsX hAC)
      (hChain3 img ext hLoads hAC) s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 hx22

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
