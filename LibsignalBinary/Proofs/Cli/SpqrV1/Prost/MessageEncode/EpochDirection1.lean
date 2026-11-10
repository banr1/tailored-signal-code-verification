/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `prost::encoding::message::encode<EpochDirection> [local#3]` Verification

Proves stage lemmas and top-level `subroutine_ok` contracts for `EpochDirection` message encoding
on the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.Layout.L26

open Lean Meta Elab Tactic ProofLib

/-- Fetch instructions in `[kStart, kEnd)` for `encode<EpochDirection> [local#3]`. -/
elab "ed1_fetches_range_cli " b:term:max H:term:max _entry:term:max kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let sym := "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"
  let entry ← ProofLib.CodeLookup.lookupOff ``CryptoVerification.libsignalSessionCode sym
  let off := entry.val
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent entry.decl
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let decName := Name.str `CryptoVerification.SpqrV1.Prost.MessageEncode
      ("libsignalSessionBinCli_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k)))
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd decName)
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $fnOff (by decide) $dec))
    else
      evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec))

end CryptoVerification.SpqrV1.Layout.L26

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L26
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

/-- Stage 1 (`+0 .. +172`) of `encode<EpochDirection> [local#3]`: saves the 64-byte frame and
encodes the outer length-delimited header `(tag << 3) | 2` and payload length
`epochDirectionPBEncodedLen d`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_hdr_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (v cap0 ptr0 dirA nextPtr prevPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    (hfit : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat ∨
      bs0.length + (epochDirectionHeaderBytes tag d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v)
    (hcs : AuthEncodeCalleeSaved s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt sp (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 172#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 →
      AuthEncodeCalleeSaved s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap1 ptr1 (bs0 ++ epochDirectionHeaderBytes tag d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn1 : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) := Or.inl rfl
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 40 44
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 168 172
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches
  have hhdr_bds := epochDirectionHeaderBytes_len_bounds tag d
  let S := epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_prologue hres b ext hfn1 tag dirA v sp
    (F := vecU8At A v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ F)
    hhs0 hpc hrun hsp halign htr hw0 hx1 hx2 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx21_1 hcs1
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have htag_eq := encodeVarint_epochDirection_tag_eq_proto tag
  have hvarint1_fit :
      bs0.length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint
          (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat ∨
      bs0.length + 10 < 2 ^ 62 := by
    rw [htag_eq]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_auth_encode_varint_call (x0 := dummyAuthGhost) b A ext henc
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)
    v cap0 ptr0 sp (entry + 44#64) bs0 hvarint1_fit
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
    (by dsimp [S]; ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01
  rw [htag_eq] at hpres01
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_len b ext hfn1 v dirA nextPtr prevPtr sp d hnext_lt hprev_lt hlen_fit
    (F := vecU8At A v cap01 ptr01 (bs0 ++ Proto.encodeKey tag .lengthDelimited) ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ S ∗ F)
    hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hcs2 (by rw [htag_eq]; ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  have hhdr_eq :
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint
          (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))).length =
      bs0.length + (epochDirectionHeaderBytes tag d).length := by
    rw [List.length_append, hhdr_bds.1]; omega
  have hvarint2_fit :
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint
          (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))).length ≤ cap01.toNat ∨
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length + 10 < 2 ^ 62 := by
    rw [hhdr_eq, List.length_append]
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_auth_encode_varint_call (x0 := dummyAuthGhost) b A ext henc
    (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))
    v cap01 ptr01 sp (entry + 172#64) (bs0 ++ Proto.encodeKey tag .lengthDelimited) hvarint2_fit
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
  rw [hhdr_eq] at hpres1
  have hpres_all : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat →
      cap1 = cap0 ∧ ptr1 = ptr0 := by
    intro hle0
    obtain ⟨hc01, hp01⟩ := hpres01 (by omega)
    obtain ⟨hc1, hp1⟩ := hpres1 (by rw [hc01]; exact hle0)
    exact ⟨hc1.trans hc01, hp1.trans hp01⟩
  refine SepWPp.weaken_pre
    (by dsimp [S]; rw [bs0_append_epochDirectionHeaderBytes bs0 tag d]; exact Entails.of_eq (by ac_rfl))
    (hnext s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4
      (by rw [hcs34.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.2.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.2.2.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.2.2.2.1]; simp only [arm64_norm, *])
      hcs4 (Nat.le_trans hge01 hge1) hpres_all)

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_ctr_from_192_1 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (v curCap curPtr dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hctr_ne : (d.ctr == 0#32) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 224#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSaved s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗
          A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn1 : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) := Or.inl rfl
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 220 224
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches
  obtain ⟨hctr_len, _⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr_ne
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_ctr_tag b A ext hfn1 v curCap curPtr dirA sp bs1 d hlt
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hctr_eq :
      (bs1 ++ [0x08#8]).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64)).length =
      bs1.length + (epochDirectionCtrBytes d).length := by
    rw [List.length_append, List.length_singleton, hctr_len]; omega
  have hvarint_fit :
      (bs1 ++ [0x08#8]).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
    rw [hctr_eq, List.length_append, List.length_singleton]
    rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
  refine step_auth_encode_varint_call (x0 := dummyAuthGhost) b A ext henc
    (d.ctr.zeroExtend 64) v curCap curPtr sp (entry + 224#64) (bs1 ++ [0x08#8]) hvarint_fit
    (F := F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
    (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  rw [hctr_eq] at hpres2
  refine SepWPp.weaken_pre
    (by rw [bs_append_epochDirectionCtrBytes_of_ne_zero bs1 d hctr_ne]; exact Entails.of_eq (by ac_rfl))
    (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2
      (by rw [hcs12.1]; simp only [arm64_norm, *])
      (by rw [hcs12.2.1]; simp only [arm64_norm, *])
      (by rw [hcs12.2.2.1]; simp only [arm64_norm, *])
      (by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *])
      hcs2 hge2 hpres2)

/-- Stage 2 (`+172 .. +224`) of `encode<EpochDirection> [local#3]`: encodes field 1 (`ctr : u32`,
tag 1) when `d.ctr != 0`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_ctr_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (v cap1 ptr1 dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 172#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 224#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSaved s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗
          A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep192 := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_ctr_from_192_1 b A ext henc
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 172 192
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 496 516
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches
  subst hP
  cases hctr : (d.ctr == 0#32)
  · obtain ⟨hctr_len, hctr_ge2⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap1.toNat = bs1.length :=
        cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
      have hfit2 : bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_auth_do_reserve2_call (x0 := dummyAuthGhost) hres b A ext hdoReserve v cap1 ptr1 sp
        (entry + 508#64) bs1 1 hbound1 (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs (mid := entry + 192#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep192 v newCap1 newPtr1 dirA sp bs1 d hctr (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge2 _ =>
          hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm
            (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply SepWPp.of_sepWP_cs (mid := entry + 192#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep192 v cap1 ptr1 dirA sp bs1 d hctr hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs (mid := entry + 224#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionCtrBytes_of_zero bs1 d hctr]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

local macro "an" : tactic => `(tactic| simp only [arm64_norm, *])
local macro "an0" : tactic => `(tactic| simp only [arm64_norm])

private theorem sessionMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc sessionMemcpyRegionSpec) : subroutine_ok prog pc (withStack sessionMemcpyRegionSpec stk) :=
  subroutine_ok_refine_frame h
    (fun x R s0 hpre => ⟨x, stackAt s0.sp stk,
      by dsimp only [withStack, sessionMemcpyRegionSpec] at hpre ⊢; convert hpre using 1; ac_rfl,
      fun sf hpost => by dsimp only [withStack, sessionMemcpyRegionSpec] at hpost ⊢; convert hpost using 1; ac_rfl⟩)
    (fun _ _ _ _ hp => allowPanic_not_exited hp) (fun _ _ _ _ _ he => allowPanic_not_exited he) (fun _ _ _ _ _ _ ho => (allowPanic_not_exited ho).elim)

private theorem step_ed1_memcpy_call {resStack : Nat}
    (b : BitVec 64) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withAuthEncodeCS, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withAuthEncodeCS, withStack, sessionMemcpyRegionSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withAuthEncodeCS, withStack, sessionMemcpyRegionSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (AuthEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

private theorem step_next_from_300_1_xa {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_ne : d.next.isEmpty = false) (hle : bs2.length + d.next.length ≤ curCap.toNat)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 300#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = nextPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 328#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ d.next) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 300 328
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches; subst hP
  have hnext_ne_nil : d.next ≠ [] := List.isEmpty_eq_false_iff.mp hnext_ne
  have hnext_pos : 0 < d.next.length := List.length_pos_of_ne_nil hnext_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 d.next.length hle hcap_lt hptr_ne hnext_pos, epochDirectionElemsAt]
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy")); wp_steps
  apply SepWP.done (by an) (by an); intro hinv1
  refine step_ed1_memcpy_call b ext hmemcpy
    (curPtr + BitVec.ofNat 64 bs2.length) nextPtr sp (entry + 320#64) d.next
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.next.length)
        (curCap.toNat - bs2.length - d.next.length) ∗
      ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      ((dirA + 32#64) ↦₆₄ prevPtr) ∗ ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
      (prevPtr ↦ₛ d.prev) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗ F) (by an) (by an) (by an) halign (by an) (by an)
    (by an) (by an)
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (hcs.step (by an0) (by an0)
      (by an0) (by an0) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = dirA := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs (mid := entry + 328#64); wp_steps
  apply SepWP.done (by an) (by an); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by an) (by an) (by an) (by an) (by an) (by an) (by an) (hcs1.step (by an0) (by an0)
        (by an0) (by an0) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 d.next hle hcap_lt hptr_ne hnext_ne_nil, epochDirectionElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_next_from_248_1_xa {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_ne : d.next.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 328#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSaved s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep300 := step_next_from_300_1_xa b A ext hmemcpy
  have hfn1 : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) := Or.inl rfl
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 276 300; ed1_fetches_range_cli b (Rust.withPanics ext) entry 536 572
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches
  have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hnext_ne
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_next_tag b A ext hfn1 v curCap curPtr dirA nextPtr sp bs1 d hlt
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")); wp_steps
  apply SepWP.done (by an) (by an); intro hinv1
  have hvarint_fit : (bs1 ++ [0x12#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.next.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_auth_encode_varint_call (x0 := dummyAuthGhost) b A ext henc
    (BitVec.ofNat 64 d.next.length) v curCap curPtr sp (entry + 280#64)
    (bs1 ++ [0x12#8]) hvarint_fit (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) (by an) (by an) (by an)
    halign (by an) (by an) (by an) (by an) (hcs1.step (by an0) (by an0)
      (by an0) (by an0) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x12#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.next.length)
  have hbs2_len : bs2.length + d.next.length = bs1.length + (epochDirectionNextBytes d).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hnext_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  have hx23_2 : s2.readReg64 .x23 = nextPtr := by rw [hcs12.2.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hnext_lt63 : d.next.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + d.next.length
  · have hfit_next : bs2.length + d.next.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_next⟩ := elem_len_after_reserve_not_ult hfit_next hneed
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")); wp_steps
    apply SepWP.done (by an) (by an); intro hinv2
    refine step_auth_do_reserve2_call (x0 := dummyAuthGhost) hres b A ext hdoReserve v cap2 ptr2 sp
      (entry + 552#64) bs2 d.next.length hbound_next (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by an) (by an) (by an) halign (by an) (by an) (by an)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (hcs2.step (by an0) (by an0)
        (by an0) (by an0) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.next.length)
    change (BitVec.ofNat 64 d.next.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = dirA := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_3 : s3.readReg64 .x23 = nextPtr := by rw [hcs23.2.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs (mid := entry + 300#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv3
    exact hstep300 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d hnext_ne hle3
      (F := A.pool ∗ F) (by an) (by an) (by an) halign (by an) (by an) (by an) (by an) (by an) (by an) (by an)
      (hcs3.step (by an0) (by an0) (by an0) (by an0) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + d.next.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mp h)
    have hpres_all : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 300#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv2
    exact hstep300 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hnext_ne hle_fast
      (F := A.pool ∗ F) (by an) (by an) (by an) halign (by an) (by an) (by an) (by an) (by an) (by an) (by an)
      (hcs2.step (by an0) (by an0) (by an0) (by an0) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres_all))

private theorem step_next_1_xa {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v cap1 ptr1 dirA nextPtr prevPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (d : EpochDirectionPB) (hnext_lt : d.next.length < 2 ^ 63)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 224#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 328#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSaved s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep248 := step_next_from_248_1_xa hres b A ext henc hdoReserve hmemcpy
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 224 248; ed1_fetches_range_cli b (Rust.withPanics ext) entry 516 536
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches; subst hP
  have ⟨hnext_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  cases hn : d.next.isEmpty
  · have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hn
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader, epochDirectionElemsAt]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")); wp_steps
      apply SepWP.done (by an) (by an); intro hinv0
      have hcap_eq : cap1.toNat = bs1.length :=
        cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
      have hfit2 : bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_auth_do_reserve2_call (x0 := dummyAuthGhost) hres b A ext hdoReserve v cap1 ptr1 sp
        (entry + 528#64) bs1 1 hbound1 (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        (by an) (by an) (by an) halign (by an) (by an) (by an)
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by an0) (hcs.step (by an0) (by an0)
          (by an0) (by an0) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs (mid := entry + 248#64); wp_steps
      apply SepWP.done (by an) (by an); intro hinv1
      exact hstep248 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs1 d hn (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by an) (by an) (by an) halign (by an) (by an) (by an)
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by an0) (by an0) (by an0) (by an0) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 _ =>
          hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply SepWPp.of_sepWP_cs (mid := entry + 248#64); wp_steps
      apply SepWP.done (by an) (by an); intro hinv0
      exact hstep248 v cap1 ptr1 dirA nextPtr prevPtr sp bs1 d hn hlt1 hfit (F := F) (by an) (by an) (by an)
        halign (by an) (by an) (by an) (by an) (by an) (by an) (by an) (hcs.step (by an0) (by an0)
          (by an0) (by an0) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs (mid := entry + 328#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionNextBytes_of_empty bs1 d hn]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 (by an) (by an) (by an) (by an) (by an) (by an) (by an) (hcs.step (by an0) (by an0)
          (by an0) (by an0) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_prev_from_404_1_xa {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_ne : d.prev.isEmpty = false) (hle : bs2.length + d.prev.length ≤ curCap.toNat)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = prevPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 432#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ d.prev) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 404 432
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches; subst hP
  have hprev_ne_nil : d.prev ≠ [] := List.isEmpty_eq_false_iff.mp hprev_ne
  have hprev_pos : 0 < d.prev.length := List.length_pos_of_ne_nil hprev_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 d.prev.length hle hcap_lt hptr_ne hprev_pos, epochDirectionElemsAt]
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy")); wp_steps
  apply SepWP.done (by an) (by an); intro hinv1
  refine step_ed1_memcpy_call b ext hmemcpy
    (curPtr + BitVec.ofNat 64 bs2.length) prevPtr sp (entry + 424#64) d.prev
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.prev.length)
        (curCap.toNat - bs2.length - d.prev.length) ∗
      ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      (nextPtr ↦ₛ d.next) ∗ ((dirA + 32#64) ↦₆₄ prevPtr) ∗
      ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗ F) (by an) (by an) (by an)
    halign (by an) (by an) (by an) (by an)
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (hcs.step (by an0) (by an0)
      (by an0) (by an0) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs (mid := entry + 432#64); wp_steps
  apply SepWP.done (by an) (by an); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by an) (by an) (by an) (by an) (hcs1.step (by an0) (by an0)
        (by an0) (by an0) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 d.prev hle hcap_lt hptr_ne hprev_ne_nil, epochDirectionElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_prev_from_352_1_xa {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_ne : d.prev.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 352#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 432#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSaved s0 sm → curCap.toNat ≤ cap3.toNat →
      (bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat → cap3 = curCap ∧ ptr3 = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap3 ptr3 (bs1 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep404 := step_prev_from_404_1_xa b A ext hmemcpy
  have hfn1 : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) := Or.inl rfl
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 380 404; ed1_fetches_range_cli b (Rust.withPanics ext) entry 616 652
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches
  have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hprev_ne
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_prev_tag b A ext hfn1 v curCap curPtr prevPtr sp bs1 d hlt
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")); wp_steps
  apply SepWP.done (by an) (by an); intro hinv1
  have hvarint_fit : (bs1 ++ [0x1a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.prev.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_auth_encode_varint_call (x0 := dummyAuthGhost) b A ext henc
    (BitVec.ofNat 64 d.prev.length) v curCap curPtr sp (entry + 384#64)
    (bs1 ++ [0x1a#8]) hvarint_fit (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) (by an) (by an) (by an)
    halign (by an) (by an) (by an) (by an) (hcs1.step (by an0) (by an0)
      (by an0) (by an0) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.prev.length)
  have hbs2_len : bs2.length + d.prev.length = bs1.length + (epochDirectionPrevBytes d).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hprev_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = prevPtr := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hprev_lt63 : d.prev.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + d.prev.length
  · have hfit_prev : bs2.length + d.prev.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_prev⟩ := elem_len_after_reserve_not_ult hfit_prev hneed
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")); wp_steps
    apply SepWP.done (by an) (by an); intro hinv2
    refine step_auth_do_reserve2_call (x0 := dummyAuthGhost) hres b A ext hdoReserve v cap2 ptr2 sp
      (entry + 632#64) bs2 d.prev.length hbound_prev (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by an) (by an) (by an) halign (by an) (by an) (by an)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (hcs2.step (by an0) (by an0)
        (by an0) (by an0) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.prev.length)
    change (BitVec.ofNat 64 d.prev.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = prevPtr := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs (mid := entry + 404#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv3
    exact hstep404 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d hprev_ne hle3
      (F := A.pool ∗ F) (by an) (by an) (by an) halign (by an) (by an) (by an) (by an) (by an)
      (hcs3.step (by an0) (by an0) (by an0) (by an0) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + d.prev.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mp h)
    have hpres_all : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 404#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv2
    exact hstep404 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hprev_ne hle_fast
      (F := A.pool ∗ F) (by an) (by an) (by an) halign (by an) (by an) (by an) (by an) (by an)
      (hcs2.step (by an0) (by an0) (by an0) (by an0) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hcsm hge2 hpres_all))

private theorem step_prev_1_xa {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (v cap2 ptr2 dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_lt : d.prev.length < 2 ^ 63)
    (hfit : bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 328#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + 432#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSaved s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep352 := step_prev_from_352_1_xa hres b A ext henc hdoReserve hmemcpy
  ed1_fetches_range_cli b (Rust.withPanics ext) entry 328 352; ed1_fetches_range_cli b (Rust.withPanics ext) entry 596 616
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry
  examples_hide_fetches; subst hP
  have ⟨hprev_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hp : d.prev.isEmpty
  · have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hp
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by ac_rfl) fun hcap2_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader, epochDirectionElemsAt]
    by_cases hcap2 : cap2 == BitVec.ofNat 64 bs2.length
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")); wp_steps
      apply SepWP.done (by an) (by an); intro hinv0
      have hcap_eq : cap2.toNat = bs2.length :=
        cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2)) hcap2
      have hfit2 : bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_auth_do_reserve2_call (x0 := dummyAuthGhost) hres b A ext hdoReserve v cap2 ptr2 sp
        (entry + 608#64) bs2 1 hbound1 (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        (by an) (by an) (by an) halign (by an) (by an) (by an)
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by an0) (hcs.step (by an0) (by an0)
          (by an0) (by an0) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs2, vecHeader]
      apply SepWPp.of_sepWP_cs (mid := entry + 352#64); wp_steps
      apply SepWP.done (by an) (by an); intro hinv1
      exact hstep352 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs2 d hp (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by an) (by an) (by an) halign (by an) (by an) (by an)
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *]) (hcs1.step (by an0) (by an0)
          (by an0) (by an0) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 _ =>
          hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hlt1 : bs2.length < cap2.toNat :=
        lt_cap_toNat_of_beq_false hcap2_le (Bool.eq_false_iff.mpr hcap2)
      apply SepWPp.of_sepWP_cs (mid := entry + 352#64); wp_steps
      apply SepWP.done (by an) (by an); intro hinv0
      exact hstep352 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hp hlt1 hfit (F := F) (by an) (by an) (by an)
        halign (by an) (by an) (by an) (by an) (by an) (hcs.step (by an0) (by an0) (by an0) (by an0) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs (mid := entry + 432#64); wp_steps
    apply SepWP.done (by an) (by an); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionPrevBytes_of_empty bs2 d hp]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap2 ptr2 (by an) (by an) (by an) (by an) (hcs.step (by an0) (by an0) (by an0) (by an0) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## Top-Level Correctness of `encode<EpochDirection> [local#3]` -/

/-- General `SepWPp` correctness for `encode<EpochDirection> [local#3]`, parameterized by
`resStack` (`doReserveStack` or `doReserveStackX`) with bounded-stack `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirection1_gen_ok_ext_xa
    {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodeEpochDirectionPinnedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (withAuthEncodeCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeEpochDirectionPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn1 : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) := Or.inl rfl
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre; dsimp only [encodeEpochDirectionPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hlen_fit⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hnext_lt, hprev_lt, hnext_cap0, hprev_cap0⟩ :=
    epochDirectionPBPinnedAt_bounds_of_satisfies (A := A) (g := x.g) (dirA := x.dirA) (d := x.dir)
      (F := vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  obtain ⟨_, hcap_lt, _⟩ :=
    Auth.vecU8At_bounds_of_satisfies (A := A) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A x.v x.cap x.ptr x.bs ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)) ∗
      epochDirectionRestAt A x.g x.dirA x.dir) ∗ R := by
    rw [epochDirectionPBPinnedAt_eq_elems A x.g x.dirA x.dir hnext_cap0 hprev_cap0] at hpre_mem
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have htot_split := encodeEpochDirectionMsg_len_split x.tag x.dir
  have htot_len := epochDirectionPBEncodedLen_eq_fields_len x.dir
  have hlen_pb_lt : epochDirectionPBEncodedLen x.dir < 2 ^ 64 := by
    rw [htot_len]; rcases hlen_fit with h | h <;> omega
  have hfit_hdr : x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length ≤ x.cap.toNat ∨
      x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length + 10 < 2 ^ 62 := by
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  let S := epochDirectionSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_hdr_1 hres b A ext henc
    x.tag x.v x.cap x.ptr x.dirA x.g.next.ptr x.g.prev.ptr s0.sp x.bs x.dir
    hnext_lt hprev_lt hlen_pb_lt hfit_hdr
    (F := epochDirectionRestAt A x.g x.dirA x.dir)
    hpc hrun rfl halign rfl hw0 hx1 hx2 (AuthEncodeCalleeSaved.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hge1 hpres1
  let bs1 := x.bs ++ epochDirectionHeaderBytes x.tag x.dir
  have hfit_ctr : bs1.length + (epochDirectionCtrBytes x.dir).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs1]; rw [List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_ctr_1 hres b A ext henc hdoReserve
    x.v cap1 ptr1 x.dirA s0.sp bs1 x.dir hfit_ctr
    (F := epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗ S ∗
      epochDirectionRestAt A x.g x.dirA x.dir)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    (by dsimp [bs1, S]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hge2 hpres2
  let bs2 := bs1 ++ epochDirectionCtrBytes x.dir
  have hfit_next : bs2.length + (epochDirectionNextBytes x.dir).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionNextBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs2, bs1]; rw [List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_next_1_xa hres b A ext henc hdoReserve hmemcpy
    x.v cap2 ptr2 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs2 x.dir hnext_lt hfit_next
    (F := S ∗ epochDirectionRestAt A x.g x.dirA x.dir)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
    (by dsimp [bs2, S]; ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hcs3 hge3 hpres3
  let bs3 := bs2 ++ epochDirectionNextBytes x.dir
  have hfit_prev : bs3.length + (epochDirectionPrevBytes x.dir).length ≤ cap3.toNat ∨
      bs3.length + (epochDirectionPrevBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs3, bs2, bs1]; rw [List.length_append, List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_prev_1_xa hres b A ext henc hdoReserve hmemcpy
    x.v cap3 ptr3 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs3 x.dir hprev_lt hfit_prev
    (F := S ∗ epochDirectionRestAt A x.g x.dirA x.dir)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 hcs3
    (by dsimp [bs3, S]) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hcs4 hge4 hpres4
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_epilogue hres b ext hfn1 s0.sp
    (F := vecU8At A x.v cap4 ptr4 (bs3 ++ epochDirectionPrevBytes x.dir) ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗ A.pool ∗
      epochDirectionRestAt A x.g x.dirA x.dir)
    hpc4 hrun4 hsp4 halign htr4 hcs4 (by dsimp [S]; ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _; refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap4.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
      cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hfit_cap
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by dsimp [bs1]; rw [hc1, List.length_append]; omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by dsimp [bs2, bs1]; rw [hc2, hc1, List.length_append, List.length_append]; omega)
    obtain ⟨hc4, hp4⟩ := hpres4 (by
      dsimp [bs3, bs2, bs1]
      rw [hc3, hc2, hc1, List.length_append, List.length_append, List.length_append]; omega)
    exact ⟨hc4.trans (hc3.trans (hc2.trans hc1)), hp4.trans (hp3.trans (hp2.trans hp1))⟩
  dsimp only [encodeEpochDirectionPinnedSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨cap4, ptr4, ?_⟩
  have hpure : (x.cap.toNat ≤ cap4.toNat ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
        cap4 = x.cap ∧ ptr4 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  dsimp [bs3, bs2, bs1] at hm
  rw [hpure, pure_true, emp_sepConj,
    epochDirectionPBPinnedAt_eq_elems A x.g x.dirA x.dir hnext_cap0 hprev_cap0,
    ← bs0_append_encodeEpochDirectionMsg x.bs x.tag x.dir]
  convert hm using 1; ac_rfl

/-- General `SepWPp` correctness for `encode<EpochDirection> [local#3]` with 0-stack `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirection1_gen_ok_ext
    {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64) {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodeEpochDirectionPinnedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy")) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    (hrun : s0.status = .Running) (hpre : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).pre x s0 ∗ R) (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeEpochDirectionPinnedSpec A).onPanic x s0 sf ∗ R)) :=
  CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirection1_gen_ok_ext_xa hres henc hdoReserve
    (subroutine_ok_withAuthEncodeCS s0 (sessionMemcpy_to_withStack (48 + resStack) hmemcpy)) hpc hrun hpre hsp

/-- `encode<EpochDirection> [local#3]` satisfies `encodeEpochDirectionPinnedSpec A` under
`AllocContracts b A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1PinnedOkExt b A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_encodeVarint2_fnAddr_eq]; exact CryptoVerification.Cli.SpqrV1.Varint.encode_varint2_fit_ok_ext hA
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (doReserve2SpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_doReserve2_fnAddr_eq]; exact CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy")) sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name
      (num% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (by rw [(ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"), (ls_stub% "memcpy")])
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirection1_gen_ok_ext (by decide)
    (subroutine_ok_withAuthEncodeCS s0 henc0) (subroutine_ok_withAuthEncodeCS s0 hdoReserve0)
    hmemcpy hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- `encode<EpochDirection> [local#3]` satisfies `encodeEpochDirectionSpec A` under
`AllocContracts b A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1OkExt b A ext :=
  epochDirection_unpinned_of_pinned (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext hA)

/-- `encode<EpochDirection> [local#3]` satisfies
`(encodeEpochDirectionPinnedSpecX A).inImage img` under `AllocContracts img.base A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1PinnedOkX img A ext := by
  have hdoReserve := CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_encodeVarint2_fnAddr_eq]; exact CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2_fit_ok_ext_x img A ext hdoReserve
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      ((doReserve2SpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_doReserve2_fnAddr_eq]; exact hdoReserve
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy")) sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name
      (num% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      (by rw [(ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"), (ls_stub% "memcpy")])
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirection1_gen_ok_ext (by decide)
    (subroutine_ok_withAuthEncodeCS_x img s0 hinv0 henc0)
    (subroutine_ok_withAuthEncodeCS_x img s0 hinv0 hdoReserve0)
    hmemcpy hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- `encode<EpochDirection> [local#3]` satisfies `(encodeEpochDirectionSpecX A).inImage img`
under `AllocContracts img.base A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1OkX img A ext :=
  epochDirection_unpinned_of_pinned_x (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext_x hA)

end CryptoVerification.SpqrV1.Prost.MessageEncode
