/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Leaf
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2 -- shake: keep

/-!
# Varint Arms (Tags 1, 5, 10, 11) of Inlined `SessionStructure::decode`

Verifies the varint field arms (`overDecArm_varint` and `overDecArm_varint_cli_okTR`) of the
inlined `SessionStructure::decode` loop in `message_decrypt_prekey::<Coins>::{closure#0}`:
tag 1 (`session_version` at `[sp, #0xa78]`), tag 5 (`previous_counter` at `[sp, #0xa7c]`),
tag 10 (`remote_registration_id` at `[sp, #0xa80]`), and tag 11 (`local_registration_id` at
`[sp, #0xa84]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField SSG)
open CryptoVerification.E2E.Record.L1GX (kyberAt)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.SpqrV1.Varint

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓] decryptPrekeyClosure_fnOff

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
  exact ProofLib.SepWPp.call_frame_frozen (x := x) (F := F) hcall hF hsym hpc hrun hsp hlr hspec hφ hP
    (fun sf code R' _ hex => by rw [hexit_false] at hex; exact allowPanic_not_exited hex)
    (fun sf _ => by rw [hpan_eq]; exact allowPanic_oom_of_trace_eq htr)
    (fun sf hpcm hrunm hspm hcsm hF' hsym' =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hF' hsym')
    (fun sf R' _ hoom_post => by
      rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim)

/-! ## Callee Contracts (`decode_varint [local#5]`, `skip_field [local#6]`) -/

theorem decodeVarint5_ok_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    DecodeVarint5OkExtX img A ext := by
  have hFromW := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorFrom_okW hAC
  have hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img) :=
    decodeErrorFromSpecWithStack_inImage_le
      (s1 := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorHookStackW)
      (s2 := decodeErrorHookStackX) hFromW
  have hSlowW := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeVarintSlow_okW hFromW
  have hSlow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecX A).inImage img) :=
    decodeVarintSlowX_ok_of_session2
      (decodeVarintSlowSpecWithStack_inImage_mono
        (s1 := CryptoVerification.LibsignalTripleRatchet.WireX.varintSlowStackX)
        (s2 := decodeVarintSlowStackX) hSlowW)
  refine decodeVarint5_ok_of_contracts_x ?_ ?_
  · rw [decodeVarint5_add_from_eq_fnAddr]; exact hFrom
  · rw [decodeVarint5_add_slow_eq_fnAddr]; exact hSlow

abbrev decodeVarint5_ok_of_allocContractsX := @decodeVarint5_ok_alloc

theorem skipField6_ok_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    SkipField6OkExtX img A ext := by
  have hFromW := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorFrom_okW hAC
  have hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img) :=
    decodeErrorFromSpecWithStack_inImage_le
      (s1 := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorHookStackW)
      (s2 := decodeErrorHookStackX) hFromW
  refine skipField6_ok_of_contracts ?_ (decodeVarint5_ok_alloc hAC)
  rw [skipField6_add_from_eq_fnAddr]
  exact hFrom

theorem decodeVarint5_call_addr_eq (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr decryptPrekeyClosureName +
      bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
           ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64) =
      (libsignalSessionCode.rebase b H).fnAddr decodeVarint5Name := by
  have h1 := (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]")
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff decryptPrekeyClosureName)) +
    bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
         ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff decodeVarint5Name)
  rw [h1, h2]
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Stack, Cursor, and `prostSSGQAt` Split Helpers -/

theorem stackAt_overDecStackX_eq_decodeVarint2StackX (q : BitVec 64) :
    stackAt q overDecStackX =
      memRegion (q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX) ∗
        stackAt q decodeVarint2StackX :=
  ProofLib.stackAt_split_bottom q decodeVarint2StackX
    (overDecStackX - decodeVarint2StackX) (by decide)

theorem suffix_payload_of_suffix_enc {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) :
    (fl.payload ++ rest) <:+ enc := by
  rcases hsuf with ⟨pre, hpre⟩
  refine ⟨pre ++ encodeKey fl.tag fl.wt, ?_⟩
  rw [List.append_assoc, ← List.append_assoc (encodeKey fl.tag fl.wt), ← GenFieldQ.enc, hpre]

theorem payload_append_length_lt_of_suffix {pfx rest enc : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    (pfx ++ rest).length < 2 ^ 63 := by
  rcases hsuf with ⟨pre, hpre⟩
  have hle : (pfx ++ rest).length ≤ enc.length := by
    simp only [← hpre, List.length_append]; omega
  omega

theorem sliceCursorAfter_split_of_suffix (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
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

theorem sliceCursorAfter_unsplit_of_suffix (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
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

def kyberPre (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
  | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4

theorem kyberAt_eq_sep (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAt A ss kyber R = kyberPre A ss kyber ∗ R := by
  cases kyber with
  | none => simp only [kyberAt, kyberPre, sepConj_assoc]
  | some p => rcases p with ⟨i, ct⟩; simp only [kyberAt, kyberPre, sepConj_assoc]

def prostSSGQHead (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => CryptoVerification.E2E.Record.DeserializeGeneral.prostChainGAt A a c)
      (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => CryptoVerification.E2E.Record.DeserializeGeneral.prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         CryptoVerification.E2E.Record.L1GX.pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberPre A ss v.ext.kyber

theorem prostSSGQAt_eq_head_tail (A : RustAlloc) (q : BitVec 64) (v : SSGQ) :
    prostSSGQAt A (q + 0x930#64) v =
      prostSSGQHead A (q + 0x930#64) v ∗
        ((q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        ((q + 0xa84#64) ↦₃₂ v.ext.locReg) := by
  unfold prostSSGQAt prostSSGQHead
  rw [kyberAt_eq_sep]
  have h148 : (q + 0x930#64) + 0x148#64 = q + 0xa78#64 := by bv_omega
  have h14c : (q + 0x930#64) + 0x14c#64 = q + 0xa7c#64 := by bv_omega
  have h150 : (q + 0x930#64) + 0x150#64 = q + 0xa80#64 := by bv_omega
  have h154 : (q + 0x930#64) + 0x154#64 = q + 0xa84#64 := by bv_omega
  rw [h148, h14c, h150, h154]
  ac_rfl

def overDecVarintRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQHead A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX)

abbrev overDecVarintRest (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overDecVarintRestExt CryptoVerification.E2E.Record.A0 g v curLen

theorem overDecHeap_eq_varint_split_ext {A : RustAlloc} (g : OverDecG) (v : SSGQ)
    {pfx rest : List (BitVec 8)} (hsuf : (pfx ++ rest) <:+ g.enc) :
    overDecHeapExt A g (pfx ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
      overDecVarintRestExt A g v (pfx ++ rest).length := by
  unfold overDecHeapExt overDecVarintRestExt
  rw [sliceCursorAfter_split_of_suffix (g.q + 0x920#64) g.encPtr hsuf,
      prostSSGQAt_eq_head_tail A g.q v,
      stackAt_overDecStackX_eq_decodeVarint2StackX g.q]
  ac_rfl

theorem overDecHeap_eq_varint_split (g : OverDecG) (v : SSGQ) {pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ g.enc) :
    overDecHeap g (pfx ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
      overDecVarintRest g v (pfx ++ rest).length :=
  overDecHeap_eq_varint_split_ext g v hsuf

theorem overDecHeap_eq_varint_unsplit_ext {A : RustAlloc} (g : OverDecG) (v' : SSGQ)
    {pfx rest : List (BitVec 8)} (hsuf : (pfx ++ rest) <:+ g.enc) :
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v'.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v'.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v'.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v'.ext.locReg) ∗
      overDecVarintRestExt A g v' (pfx ++ rest).length =
      overDecHeapExt A g rest v' := by
  unfold overDecHeapExt overDecVarintRestExt
  rw [← sliceCursorAfter_unsplit_of_suffix (g.q + 0x920#64) g.encPtr hsuf,
      prostSSGQAt_eq_head_tail A g.q v',
      stackAt_overDecStackX_eq_decodeVarint2StackX g.q]
  ac_rfl

theorem overDecHeap_eq_varint_unsplit (g : OverDecG) (v' : SSGQ) {pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ g.enc) :
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v'.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v'.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v'.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v'.ext.locReg) ∗
      overDecVarintRest g v' (pfx ++ rest).length =
      overDecHeap g rest v' :=
  overDecHeap_eq_varint_unsplit_ext g v' hsuf

theorem decodeVarint2SpecX_inImage_pre_eq (img : Obj.Image) (A : RustAlloc)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (s : State) :
    ((decodeVarint2SpecX A).inImage img).pre ⟨bufRef, slot, ptr, bs⟩ s =
      ⌜(img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧
        s.readReg64 .x0 = bufRef ∧ bs.length < 2 ^ 63⌝ ∗
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗
        A.pool ∗ stackAt s.sp decodeVarint2StackX) := by
  dsimp only [Spec.inImage, decodeVarint2SpecX, ImgCallInv]
  rw [pure_sepConj_pure_assoc]

theorem decodeVarint2SpecX_inImage_post_encodeVarint_eq (img : Obj.Image) (A : RustAlloc)
    (bufRef slot ptr : BitVec 64) (val : BitVec 32) (rest : List (BitVec 8)) (s1 s2 : State) :
    ((decodeVarint2SpecX A).inImage img).post
      ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩ s1 s2 =
      ⌜s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = val.setWidth 64⌝ ∗
      ⌜s2.trace = s1.trace⌝ ∗
      ((bufRef ↦₆₄ slot) ∗
        sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
        A.pool ∗ stackAt s1.sp decodeVarint2StackX) := by
  dsimp only [Spec.inImage, decodeVarint2SpecX]
  rw [decodeVarint_encodeVarint (val.setWidth 64) rest]
  dsimp only
  ac_rfl

private def OverDecSavedRegs (g : OverDecG) (s : State) : Prop :=
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

private theorem overDecSavedRegs_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegs g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegs g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

set_option maxHeartbeats 600000 in
private theorem overDecArm_varint_of_pre_post_ext {A : RustAlloc}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32}
    {frameRest : SepProp}
    (hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g armOff s)
    (hsplit : overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ oldVal) ∗
      frameRest)
    (hunsplit :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ val) ∗
      frameRest =
      overDecHeapExt A g rest v')
    (hpre_step : SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + retOff ∧
        OverDecSavedRegs g s1))
    (hpost_step : ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + retOff →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + spOff) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf)) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest v'))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, hF, hsym, hsaved⟩
  have hlen_pay : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 :=
    payload_append_length_lt_of_suffix hsuf_pay hlen
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  rw [hsplit]
  refine SepWPp_bind_sepWP_frame hF hsym hpre_step
    rfl
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hlr1, hsaved1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length)
  refine SepWPp_call_frame_frozen_oom
    (x := (⟨g.q + 0xbe8#64, g.q + 0x920#64, curPtr, encodeVarint (val.setWidth 64) ++ rest⟩ :
      DecodeVarintSlowGhost))
    (φ := (img.FrozenLoaded s1 ∧ s1.symtab = img.symtab) ∧
      s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
      (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63)
    (T := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX)
    (F := ((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest)
    hF1 hsym1 htr1 (decodeVarint5_ok_alloc hAC) hpc1 hrun1 hsp1_al hlr1
    (by rw [decodeVarint2SpecX_inImage_pre_eq, hsp1])
    ⟨⟨hF1, hsym1⟩, hx0_1, hlen_pay⟩
    (by dsimp only [curPtr]; simp only [sepConj_assoc])
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  rw [decodeVarint2SpecX_inImage_post_encodeVarint_eq, hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_2, hx1_2⟩ => ?_
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs g s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  refine SepWPp_ret_sepWP_frame hF2 hsym2
    (hpost_step s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2 hsaved2)
    (F := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      frameRest)
    (by dsimp only [curPtr]; ac_rfl)
    fun sf hpcf hrunf hFf hsymf ⟨hspf, htrf, hsavedf⟩ => ?_
  have hspf_align : (sf.sp &&& 15#64 == 0#64) = true := by rw [hspf]; exact hq_align
  refine ⟨⟨hpcf, hrunf, hspf, hspf_align, htrf, hFf, hsymf, hsavedf⟩, ?_⟩
  apply Entails.of_eq
  rw [← hunsplit]
  dsimp only [curPtr]
  ac_rfl

private theorem overDecArm_varint_of_pre_post
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hAC : Proofs.libsignal.Stage1X.AllocContractsX img CryptoVerification.E2E.Record.A0 ext)
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32}
    {frameRest : SepProp}
    (hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegs img ext s0 g armOff s)
    (hsplit : overDecHeap g (encodeVarint (val.setWidth 64) ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ oldVal) ∗
      frameRest)
    (hunsplit :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ val) ∗
      frameRest =
      overDecHeap g rest v')
    (hpre_step : SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + retOff ∧
        OverDecSavedRegs g s1))
    (hpost_step : ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + retOff →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + spOff) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf)) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeap g (encodeVarint (val.setWidth 64) ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest v'))
      (PanicOomProp s0) :=
  overDecArm_varint_of_pre_post_ext hAC hsuf_pay hlen hregs hsplit hunsplit hpre_step hpost_step

/-! ## Pre-Call and Post-Call `SepWP` Lemmas -/

attribute [local simp, local arm64_norm, local wp_norm] State.readReg32

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm, local wp_norm]
theorem truncate_32_setWidth_64 (v : BitVec 32) : BitVec.truncate 32 (v.setWidth 64) = v := by
  bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth_32_setWidth_64 (v : BitVec 32) : BitVec.setWidth 32 (v.setWidth 64) = v := by
  bv_robdd

set_option maxHeartbeats 400000 in
private theorem overDecVarint_pre_tag1 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegs img ext s0 g 0x21bc#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x21c8#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _, _,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  closure_fetches_range_cli img.base (Rust.withPanics ext) 8636 8644
  dsimp only [contractProg] at hpc ⊢
  rw [← decodeVarint5_call_addr_eq img.base (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_post_tag1 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x21c8#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + 0xa78#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa78#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 8648 8648
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9340 9344
  dsimp only [contractProg] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_pre_tag5 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegs img ext s0 g 0x21e8#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x21f4#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _, _,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  closure_fetches_range_cli img.base (Rust.withPanics ext) 8680 8688
  dsimp only [contractProg] at hpc ⊢
  rw [← decodeVarint5_call_addr_eq img.base (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_post_tag5 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x21f4#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + 0xa7c#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa7c#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 8692 8692
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9152 9156
  dsimp only [contractProg] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_pre_tag10 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegs img ext s0 g 0x23a8#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x23b4#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _, _,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9128 9136
  dsimp only [contractProg] at hpc ⊢
  rw [← decodeVarint5_call_addr_eq img.base (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_post_tag10 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x23b4#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + 0xa80#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa80#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9140 9140
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9660 9664
  dsimp only [contractProg] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_pre_tag11 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegs img ext s0 g 0x2390#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarint5Name) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x239c#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _, _,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9104 9112
  dsimp only [contractProg] at hpc ⊢
  rw [← decodeVarint5_call_addr_eq img.base (Rust.withPanics ext)]
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDecVarint_post_tag11 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x239c#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegs g s2 →
      SepWP (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s2
        ((g.q + 0xa84#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa84#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegs g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9116 9116
  closure_fetches_range_cli img.base (Rust.withPanics ext) 9652 9656
  dsimp only [contractProg] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

/-! ## Main Varint Arm Theorems -/

set_option maxHeartbeats 600000 in
theorem overDecArm_varint_ext {A : RustAlloc} : OverDecArmStmtExt A OverDecVarintField := by
  intro img ext _hLoads hAC s0 s g v fl rest hP _hOk _hFresh hsuf hlen hregs hx0 _hx22
  rcases fl with (_ | _)
  · rename_i fb
    rcases fb with (val | _ | _ | _ | val | _ | _ | _)
    · -- Tag 1: .base (.version val)
      have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_of_pre_post_ext hAC hsuf_pay hlen hregs
        (spOff := 0xa78#64) (oldVal := v.base.version) (val := val)
        (frameRest :=
          ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A (g.q + 0x930#64) v =
              prostSSGQHead A (g.q + 0x930#64)
                (v.apply (.base (.version val))) := rfl
          have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A g (v.apply (.base (.version val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.version val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag1 hregs hx0)
        overDecVarint_post_tag1
    · cases hP
    · cases hP
    · cases hP
    · -- Tag 5: .base (.prevCounter val)
      have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_of_pre_post_ext hAC hsuf_pay hlen hregs
        (spOff := 0xa7c#64) (oldVal := v.base.prevCounter) (val := val)
        (frameRest :=
          ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A (g.q + 0x930#64) v =
              prostSSGQHead A (g.q + 0x930#64)
                (v.apply (.base (.prevCounter val))) := rfl
          have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A g (v.apply (.base (.prevCounter val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.prevCounter val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag5 hregs hx0)
        overDecVarint_post_tag5
    · cases hP
    · cases hP
    · cases hP
  · cases hP
  · cases hP
  · -- Tag 10: .remReg val
    rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_of_pre_post_ext hAC hsuf_pay hlen hregs
      (spOff := 0xa80#64) (oldVal := v.ext.remReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
        overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A (g.q + 0x930#64) v =
            prostSSGQHead A (g.q + 0x930#64)
              (v.apply (.remReg val)) := rfl
        have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A g (v.apply (.remReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.remReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag10 hregs hx0)
      overDecVarint_post_tag10
  · -- Tag 11: .locReg val
    rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_of_pre_post_ext hAC hsuf_pay hlen hregs
      (spOff := 0xa84#64) (oldVal := v.ext.locReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A (g.q + 0x930#64) v =
            prostSSGQHead A (g.q + 0x930#64)
              (v.apply (.locReg val)) := rfl
        have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A g (v.apply (.locReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.locReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag11 hregs hx0)
      overDecVarint_post_tag11
  · cases hP
  · cases hP
  · cases hP

theorem overDecArm_varint : OverDecArmStmt OverDecVarintField :=
  overDecArm_varint_ext

theorem overDecArm_varint_tr_ext {A : RustAlloc} : OverDecArmStmtTRExt A OverDecVarintField :=
  overDecArm_varint_ext.toTR

theorem overDecArm_varint_tr : OverDecArmStmtTR OverDecVarintField :=
  overDecArm_varint_tr_ext

alias overDecArm_varint_cli_ok_ext := overDecArm_varint_ext
alias overDecArm_varint_cli_okTR_ext := overDecArm_varint_tr_ext
alias overDecArm_varint_cli_ok := overDecArm_varint
alias overDecArm_varint_cli_okTR := overDecArm_varint_tr

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
