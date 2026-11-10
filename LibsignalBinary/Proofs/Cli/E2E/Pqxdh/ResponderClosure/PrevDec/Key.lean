/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2 -- shake: keep

/-!
# Key Decode and Jump-Table Dispatch (`+0x216c → overDecArmOff fl`)

Verifies key decoding and `.rodata` jump-table dispatch (`overDecKey_of`, `overDecKey_cli_ok`) at
`+0x216c..+0x21b8` in `message_decrypt_prekey::<Coins>::{closure#0}`, calling `decode_varint [local#5]`
and branching via `br x9` to `entry + overDecArmOff fl`.
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
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint (decodeVarint2SpecX decodeVarint2StackX)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint5Name)

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

private theorem stackAt_sub_eq (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

/-! ## Pure Helpers on `GenFieldQ` Keys and `.rodata` Jump Table -/

private theorem overDecWt_toNat_eq (fl : GenFieldQ) :
    (overDecWt fl).toNat = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

/-- The 64-bit key value `fl.tag * 8 + (overDecWt fl).toNat` of `fl`. -/
abbrev overDecKeyVal (fl : GenFieldQ) : BitVec 64 :=
  BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat)

private theorem decodeVarint_fl_enc (fl : GenFieldQ) (rest : List (BitVec 8)) :
    decodeVarint (fl.enc ++ rest) = some (overDecKeyVal fl, fl.payload ++ rest) := by
  rw [GenFieldQ.enc, List.append_assoc, encodeKey, overDecKeyVal, overDecWt_toNat_eq fl]
  exact decodeVarint_encodeVarint _ _

/-- The 15-byte jump table in `.rodata` referenced by `adrp/add x11` at `+0x21a4/+0x21a8`. -/
abbrev overDecJtabBytes : List (BitVec 8) :=
  [0#8, 68#8, 63#8, 53#8, 11#8, 22#8, 73#8, 58#8, 101#8, 123#8, 117#8, 58#8, 6#8, 39#8, 17#8]

/-- The jump-table byte for `fl` (`overDecJtabBytes[fl.tag - 1]`). -/
def overDecJtabByte (fl : GenFieldQ) : BitVec 8 :=
  match fl with
  | .base (.version _) => 0#8
  | .base (.lik _) => 68#8
  | .base (.rik _) => 63#8
  | .base (.root _) => 53#8
  | .base (.prevCounter _) => 11#8
  | .base (.sender _) => 22#8
  | .base (.recv _) => 73#8
  | .base (.pending _) | .pendingId _ _ | .pendingSpk _ _ _ => 101#8
  | .remReg _ => 123#8
  | .locReg _ => 117#8
  | .abk _ => 6#8
  | .kyber _ _ => 39#8
  | .pq _ => 17#8

private theorem rodata_overDecJtab_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)) -
       num% (ls_field% dataOff))).take 15 = overDecJtabBytes := by
  rfl_kernel

private theorem holdsBytes_overDecJtab {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s) :
    Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)))
      overDecJtabBytes (fun _ => .ro) :=
  loads_rodata_holdsBytes hLoads hF
    (off := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)))
    (n := 15) (bs := overDecJtabBytes)
    (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel)
    (by rfl_kernel)
    rfl
    rodata_overDecJtab_eq

private theorem holdsBytes_singleton_of_getElem {m : Memory} {addr : BitVec 64}
    {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) (i : Nat) (hi : i < bs.length) :
    Arm64.Obj.HoldsBytes m (addr + BitVec.ofNat 64 i) [bs[i]] (fun _ => .ro) := by
  intro j hj
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simpa using h i hi

private theorem overDecJtab_tag_sub_one_lt (fl : GenFieldQ) :
    fl.tag - 1 < overDecJtabBytes.length := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp [GenFieldQ.tag, GenField.tag, overDecJtabBytes]

private theorem overDecJtab_getElem_eq (fl : GenFieldQ) :
    overDecJtabBytes[fl.tag - 1]'(overDecJtab_tag_sub_one_lt fl) = overDecJtabByte fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem holdsBytes_overDecJtabByte {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s) (fl : GenFieldQ) :
    Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)) + BitVec.ofNat 64 (fl.tag - 1))
      [overDecJtabByte fl] (fun _ => .ro) := by
  rw [← overDecJtab_getElem_eq fl]
  exact holdsBytes_singleton_of_getElem (holdsBytes_overDecJtab hLoads hF)
    (fl.tag - 1) (overDecJtab_tag_sub_one_lt fl)

private theorem sepWPp_intro_overDecJtabByte {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s) (fl : GenFieldQ)
    (h : SepWPp prog ret s
      (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)) + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ
        overDecJtabByte fl) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc, ← pointsToBytesRO_singleton]
  exact Satisfies.of_holdsBytes_ro (holdsBytes_overDecJtabByte hLoads hF fl) (by simp) hm

/-! ## Slice Cursor Split and Unsplit Helpers -/

private theorem fl_payload_rest_len_le (fl : GenFieldQ) (rest : List (BitVec 8)) :
    (fl.payload ++ rest).length ≤ (fl.enc ++ rest).length := by
  simp only [GenFieldQ.enc, List.length_append]
  omega

private theorem sliceCursorAfter_split_of_append (slot ptr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs2 =
      Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 bs1.length) bs2 ∗ (ptr ↦ₛ bs1) := by
  unfold Prost.sliceCursorAfter Prost.sliceCursorAt
  have hsub : (bs1 ++ bs2).length - bs2.length = bs1.length := by
    rw [List.length_append]; omega
  rw [hsub, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

private theorem sliceCursorAfter_unsplit_of_append (slot ptr : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (hle : bs3.length ≤ bs2.length) :
    Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 bs1.length) bs2 bs3 ∗ (ptr ↦ₛ bs1) =
      Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs3 := by
  unfold Prost.sliceCursorAfter
  have hadd : (ptr + BitVec.ofNat 64 bs1.length) + BitVec.ofNat 64 (bs2.length - bs3.length) =
      ptr + BitVec.ofNat 64 ((bs1 ++ bs2).length - bs3.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [List.length_append]
    omega
  rw [hadd, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

/-! ## Stage 1 (`+0x216c → +0x2174`): `decode_varint [local#5]` Call -/

private abbrev overDecDv5RelOff : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2 ^ 64)

private theorem decodeVarint5_ok_sub {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hV : DecodeVarint5OkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecDv5RelOff)
      ((decodeVarint2SpecX A).inImage img) := by
  have heq :
      (contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecDv5RelOff =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint5Name := by
    change (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName + _ =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decodeVarint5Name
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, decryptPrekeyClosure_fnOff,
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]")]
    bv_omega
  rw [heq]
  exact hV

set_option maxHeartbeats 400000 in
private theorem overDecKey_precall_sepWP (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG)
    (hregs : OverDecRegs img ext s0 g 0x216c#64 s) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecDv5RelOff)
      s emp
      (fun sm P' => (P' ⊢ emp) ∧
        sm.sp = g.q ∧ (sm.sp &&& 15#64 == 0#64) = true ∧ sm.trace = s0.trace ∧
        sm.readReg64 .x0 = g.q + 0xbe8#64 ∧
        sm.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2174#64 ∧
        sm.readReg64 .x19 = g.r19 ∧ sm.readReg64 .x20 = g.r20 ∧ sm.readReg64 .x26 = g.r26 ∧
        sm.readReg64 .x21 = g.q + 0x930#64 ∧ sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sm.readReg64 .x27 = g.prevPtr ∧
        sm.readReg64 .x28 = g.q + 0xa90#64 ∧ sm.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs g.sv) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _, _,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  closure_fetches_range_cli img.base (Rust.withPanics ext) 0x216c 0x2170
  dsimp only [contractProg, tripleRatchetProgAt, overDecDv5RelOff] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 2 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]

private theorem overDec_call_decodeVarint5 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 sm : State} {g : OverDecG} {fl : GenFieldQ}
    {pfx rest : List (BitVec 8)} {F : SepProp} {Q : State → SepProp → Prop}
    (hV : DecodeVarint5OkExtX img A ext)
    (hFm : img.FrozenLoaded sm) (hsymm : sm.symtab = img.symtab) (htrm : sm.trace = s0.trace)
    (hpcm : sm.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecDv5RelOff)
    (hrunm : sm.status = .Running) (hspm : sm.sp = g.q)
    (halm : (sm.sp &&& 15#64 == 0#64) = true)
    (hx0m : sm.readReg64 .x0 = g.q + 0xbe8#64)
    (hlrm : sm.readReg64 .lr = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2174#64)
    (hlen63 : (fl.enc ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State,
      s2.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2174#64 →
      s2.status = .Running → s2.sp = g.q →
      img.FrozenLoaded s2 → s2.symtab = img.symtab → s2.trace = s0.trace →
      CalleeSavedPreserved sm s2 →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = overDecKeyVal fl →
      SepWPp (contractProg img.base ext) ret s2
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.enc ++ rest) (fl.payload ++ rest) ∗
          A.pool ∗
          stackAt g.q decodeVarint2StackX) ∗ F)
        Q (PanicOomProp s0)) :
    SepWPp (contractProg img.base ext) ret sm
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
        A.pool ∗
        stackAt g.q decodeVarint2StackX) ∗ F)
      Q (PanicOomProp s0) := by
  let x : DecodeVarintSlowGhost :=
    ⟨g.q + 0xbe8#64, g.q + 0x920#64, g.encPtr + BitVec.ofNat 64 pfx.length, fl.enc ++ rest⟩
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) (decodeVarint5_ok_sub hV)
    hFm hsymm hpcm hrunm halm hlrm
    (fun R hm => ?_)
    (fun sf code R' _ hpost => ?_)
    (fun sf _ _ => ?_)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hF2 hsym2 => ?_)
    (fun sf R' _ hoom => ?_)
  · dsimp only [Spec.inImage, decodeVarint2SpecX, x]
    rw [hspm, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hFm, hsymm⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hlen63⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [Spec.inImage, decodeVarint2SpecX] at hpost
    exact allowPanic_not_exited hpost
  · dsimp only [Spec.inImage, decodeVarint2SpecX]
    exact allowPanic_oom_of_trace_eq htrm
  · dsimp only [Spec.inImage, decodeVarint2SpecX, x]
    rw [decodeVarint_fl_enc fl rest, hspm]
    dsimp only
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hx0_2, hx1_2⟩ => ?_
    refine SepWPp.pure_left fun htr2 => ?_
    exact SepWPp.congr_pre (by ac_rfl)
      (hnext s2 hpc2 hrun2 (hsp2.trans hspm) hF2 hsym2 (htr2.trans htrm) hcs2 hx0_2 hx1_2)
  · dsimp only [Spec.inImage, decodeVarint2SpecX] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## Stage 2 (`+0x2174 → overDecArmOff fl`): Jump-Table Dispatch -/

private theorem adrp_overDecJtab_page_eq (base fnEntry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64)
    (hentry : base + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") = fnEntry) :
    (fnEntry + (0x21a4#64 : BitVec 64)) &&& 0xfffffffffffff000#64 =
      base + bv% (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)) := by
  subst hentry
  rw [BitVec.add_assoc base (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) 0x21a4#64]
  exact adrp_page_of_aligned halign

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32 (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32#64 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_nat (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_and7 (fl : GenFieldQ) :
    overDecKeyVal fl &&& 7#64 = overDecWt fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecWt_ule6 (fl : GenFieldQ) :
    (6#64).ule (overDecWt fl) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecWt, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (overDecKeyVal fl)) = overDecKeyVal fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr3 (fl : GenFieldQ) :
    overDecKeyVal fl >>> 3 = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3#32) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_nat (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecTag_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 fl.tag)) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_beq_zero (fl : GenFieldQ) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_beq_zero (fl : GenFieldQ) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) == 0#32) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_64 (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag - 1#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_add_neg1_64 (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag + 0xffffffffffffffff#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_sub1 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) - 1#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_add_neg1 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) + 4294967295#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (fl.tag - 1))) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14 (fl : GenFieldQ) :
    (14#32).ult (BitVec.setWidth 32 (BitVec.ofNat 64 (fl.tag - 1))) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_64 (fl : GenFieldQ) :
    (14#64).ult (BitVec.ofNat 64 (fl.tag - 1)) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2#64) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_nat (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_zext_add_armOff (fl : GenFieldQ) :
    8636#64 + (BitVec.zeroExtend 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

set_option maxHeartbeats 600000 in
private theorem overDecKey_jtab_sepWP (img : Obj.Image) (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (s0 s2 : State) (g : OverDecG) (fl : GenFieldQ)
    (hregs : OverDecRegs img ext s0 g 0x2174#64 s2)
    (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = overDecKeyVal fl) :
    SepWP (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecArmOff fl) s2
      ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)) + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ
        overDecJtabByte fl)
      (fun sf P' =>
        (P' ⊢ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a4)
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x21a8)) + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ
        overDecJtabByte fl)) ∧
        sf.sp = g.q ∧ (sf.sp &&& 15#64 == 0#64) = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = overDecKeyVal fl ∧
        sf.readReg64 .x19 = g.r19 ∧ sf.readReg64 .x20 = g.r20 ∧ sf.readReg64 .x26 = g.r26 ∧
        sf.readReg64 .x21 = g.q + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x27 = g.prevPtr ∧
        sf.readReg64 .x28 = g.q + 0xa90#64 ∧ sf.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs g.sv) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _, _,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have halign : img.base &&& 0xfff#64 = 0#64 := base_aligned_of_loads hLoads
  have hentry_eq :
      img.base + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") =
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName := by
    rw [Program.fnAddr_rebase, decryptPrekeyClosure_fnOff]
  closure_fetches_range_cli img.base (Rust.withPanics ext) 0x2174 0x21b8
  dsimp only [contractProg, tripleRatchetProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = overDecKeyVal fl := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s2.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s2.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s2.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s2.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s2.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s2.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s2.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  have _hadrp := adrp_overDecJtab_page_eq img.base entry halign hentry_eq
  iterate 18 wp_step
  refine SepWP.done (by simp only [arm64_norm, BitVec.add_assoc])
    (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]

private theorem drop_left_sepWPp {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

set_option maxHeartbeats 600000 in
/-- Key (`+0x216c → overDecArmOff fl`) parameterized by `decode_varint [local#5]` contract
(`A : RustAlloc`). -/
theorem overDecKey_of_ext {A : RustAlloc}
    (hV : ∀ img ext,
      Proofs.libsignal.Stage1X.AllocContractsX img A ext →
      DecodeVarint5OkExtX img A ext) :
    OverDecKeyStmtExt A := by
  intro img ext hLoads hAC s0 s g v fl rest _hAny _hok hsuf hlen hregs
  rcases hsuf with ⟨pfx, hpfx⟩
  have hlen63 : (fl.enc ++ rest).length < 2 ^ 63 := by
    have hle : (fl.enc ++ rest).length ≤ g.enc.length := by
      have hlen_eq := congrArg List.length hpfx
      rw [List.length_append] at hlen_eq
      omega
    omega
  have hF : img.FrozenLoaded s := hregs.2.2.2.2.2.1
  have hsym : s.symtab = img.symtab := hregs.2.2.2.2.2.2.1
  refine SepWPp_bind_sepWP_frame hF hsym (overDecKey_precall_sepWP img ext s0 s g hregs)
    (F := overDecHeapExt A g (fl.enc ++ rest) v)
    (by simp only [emp_sepConj])
    fun sm hpcm hrunm hFm hsymm hregsm => ?_
  rcases hregsm with ⟨hspm, halm, htrm, hx0m, hlrm,
    hx19m, hx20m, hx26m, hx21m, hx24m, hx25m, hx27m, hx28m, hx29m, hvregsm⟩
  have hheap_split :
      emp ∗ overDecHeapExt A g (fl.enc ++ rest) v =
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
          A.pool ∗
          stackAt g.q decodeVarint2StackX) ∗
         (overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ pfx) ∗
          prostSSGQAt A (g.q + 0x930#64) v ∗
          memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
          memRegion (g.q + 0xbf0#64) 128 ∗
          memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX))) := by
    have hcur :
        Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.enc ++ rest) =
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
            (g.encPtr ↦ₛ pfx) := by
      rw [← hpfx]
      exact sliceCursorAfter_split_of_append (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
    unfold overDecHeapExt
    rw [hcur, stackAt_sub_eq g.q overDecStackX decodeVarint2StackX (by decide) (by decide), emp_sepConj]
    ac_rfl
  rw [hheap_split]
  refine overDec_call_decodeVarint5 (hV img ext hAC) hFm hsymm htrm hpcm hrunm hspm halm hx0m hlrm hlen63
    fun s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2 hx1_2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, hx29_cs, hvregs_cs⟩
  have hal2 : (s2.sp &&& 15#64 == 0#64) = true := by simpa only [hsp2, hspm] using halm
  have hregs2 : OverDecRegs img ext s0 g 0x2174#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hal2, htr2, hF2, hsym2,
     hx19_cs.trans hx19m, hx20_cs.trans hx20m, hx26_cs.trans hx26m,
     hx21_cs.trans hx21m, hx24_cs.trans hx24m, hx25_cs.trans hx25m,
     hx27_cs.trans hx27m, hx28_cs.trans hx28m, hx29_cs.trans hx29m,
     hvregs_cs.trans hvregsm⟩
  have hheap_unsplit :
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A.pool ∗
        stackAt g.q decodeVarint2StackX) ∗
       (overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ pfx) ∗
        prostSSGQAt A (g.q + 0x930#64) v ∗
        memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
        memRegion (g.q + 0xbf0#64) 128 ∗
        memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX))) =
      overDecHeapExt A g (fl.payload ++ rest) v := by
    have hunsplit :=
      sliceCursorAfter_unsplit_of_append (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
        (fl.payload ++ rest) (fl_payload_rest_len_le fl rest)
    rw [hpfx] at hunsplit
    unfold overDecHeapExt
    rw [← hunsplit, stackAt_sub_eq g.q overDecStackX decodeVarint2StackX (by decide) (by decide)]
    ac_rfl
  rw [hheap_unsplit]
  refine sepWPp_intro_overDecJtabByte hLoads hF2 fl ?_
  refine SepWPp_bind_sepWP_frame hF2 hsym2
    (overDecKey_jtab_sepWP img ext hLoads s0 s2 g fl hregs2 hx0_2 hx1_2)
    rfl
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  apply drop_left_sepWPp
  rcases hregsf with ⟨hspf, half, htrf, hx0f, hx22f,
    hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩
  refine SepWPp.done hpcf hrunf
    ⟨⟨hpcf, hrunf, hspf, half, htrf, hFf, hsymf,
      hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩,
     hx0f, hx22f, Entails.refl _⟩

theorem overDecKey_of
    (hV : ∀ img ext,
      Proofs.libsignal.Stage1X.AllocContractsX img CryptoVerification.E2E.Record.A0 ext →
      DecodeVarint5OkExtX img CryptoVerification.E2E.Record.A0 ext) :
    OverDecKeyStmt :=
  overDecKey_of_ext hV

theorem decodeVarint5_ok_stage1 {img : Obj.Image} {A : RustAlloc}
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

theorem overDecKey_cli_ok_ext {A : RustAlloc} : OverDecKeyStmtExt A :=
  overDecKey_of_ext fun _img _ext hAC => decodeVarint5_ok_stage1 hAC

/-- Unconditional CLI key-dispatch contract (`OverDecKeyStmt`). -/
theorem overDecKey_cli_ok : OverDecKeyStmt :=
  overDecKey_cli_ok_ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
