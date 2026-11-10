/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `encode<EpochDirection> [local#3]` Basic-Block Step Lemmas

Proves prologue, inline `EpochDirection::encoded_len` computation, field tag pushes, and epilogue
lemmas for `prost::encoding::message::encode::<EpochDirection, Vec<u8>> [local#3]` on the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalTripleRatchet.Prost

open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Varint

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

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

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    (encodeEpochDirectionPinnedSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    (encodeEpochDirectionSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    ((encodeEpochDirectionPinnedSpecX A).inImage img)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeEpochDirection1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name)
    ((encodeEpochDirectionSpecX A).inImage img)

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_encodeVarint2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name,
    CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name, h1, h2]; bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_doReserve2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name,
    CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name, h1, h2]; bv_omega

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = entry ∨
    (tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name = entry

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirectionEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirectionEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
scoped elab "ed_fetches_cli " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off1 := (num% (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"))
  let off2 := 0x4d3c8
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]").decl
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d3c8
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}"))
    let dec2 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirectionEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.epochDirectionEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

/-- Shared prologue (`+0..+40`): saves the 64-byte frame and prepares `x0 = (tag << 3) | 2`,
`x1 = v`, `x19 = v`, `x21 = dirA`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_prologue {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (tag : BitVec 32) (dirA v sp : BitVec 64)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = stackAt sp (authEncodeStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 40#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((stackAt (sp - 64#64) (0x30 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 0 40
  examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  rw [stackAt_authEncode hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 40#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  have hx0_eq :
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (2#64 ||| BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 0#5)) <<< 3))) =
      (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) := by
    change BitVec.zeroExtend 64 (BitVec.truncate 32
      (2#64 ||| BitVec.zeroExtend 64 (s.readReg32 .x0 <<< 3))) = _
    rw [hw0]; dsimp only [Proto.WireType.toU32]; bv_bits
  refine SepWPp.weaken_pre (by dsimp only [epochDirectionSavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))

/-- Shared inline `EpochDirection::encoded_len` computation (`+44..+168` and `+452..+484`):
loads `w23 = d.ctr`, `x22 = d.next.length`, `x20 = d.prev.length`, and computes
`x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d)` and `x1 = v` at `entry + 168#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_len (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (v dirA nextPtr prevPtr sp : BitVec 64) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = dirA)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 168#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 44 168
  ed_fetches_cli b (Rust.withPanics ext) hfn 452 484
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionElemsAt]
  obtain ⟨hnext_beq, hnext_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  obtain ⟨hprev_beq, hprev_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hctr : (d.ctr == 0#32) <;> cases hn : d.next.isEmpty <;> cases hp : d.prev.isEmpty
  · -- ctr != 0, next non-empty, prev non-empty
    have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have hadd12 := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq
        (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next)
        (c := epochDirectionPBEncodedLen d) rfl hlen_fit
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr != 0, next non-empty, prev empty
    have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hadd12 := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    have htot_eq : epochDirectionPBEncodedLen d =
        u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hp]
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr != 0, next empty, prev non-empty
    have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq
        (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr)
        (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr != 0, next empty, prev empty
    have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have htot_eq : epochDirectionPBEncodedLen d = u32VarintFieldEncodedLen d.ctr := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn, hp]
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr == 0, next non-empty, prev non-empty
    have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : bytesFieldEncodedLen d.next + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq
        (a := bytesFieldEncodedLen d.prev)
        (b := bytesFieldEncodedLen d.next)
        (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr == 0, next non-empty, prev empty
    have hn_val := bv_bytesField_nonempty hn
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr,
        bytesFieldEncodedLen, hp]
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr == 0, next empty, prev non-empty
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.prev := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr,
        bytesFieldEncodedLen, hn]
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- ctr == 0, next empty, prev empty
    have htot_eq : epochDirectionPBEncodedLen d = 0 := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr,
        bytesFieldEncodedLen, hn, hp]
    apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)

/-- Shared `ctr` tag push (`+192..+220`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`
and sets `x0 = d.ctr.zeroExtend 64`, `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_ctr_tag (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (v curCap curPtr dirA sp : BitVec 64)
    (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 220#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = d.ctr.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 192 220
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 220#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Shared `next` tag push (`+248..+276`):
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, length-delimited) to `buf`
and sets `x0 = x22`, `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_next_tag (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (v curCap curPtr dirA nextPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 276#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = nextPtr →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 248 276
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 276#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Shared `prev` tag push (`+352..+380`):
given `curBs.length < curCap.toNat`, pushes `0x1a#8` (`tag = 3`, length-delimited) to `buf`
and sets `x0 = x20`, `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_push_prev_tag (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (v curCap curPtr prevPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 352#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 380#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = prevPtr →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x1a#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 352 380
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 380#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x1a#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Shared epilogue (`+432..+452`):
restores `x20, x19, x22, x21, x24, x23, fp, lr`, deallocates the 64-byte frame, and returns. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_epochDir_epilogue {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsEpochDirectionEncodeEntry b ext entry)
    (sp : BitVec 64)
    {s0 s : State} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 432#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
        (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_cli b (Rust.withPanics ext) hfn 432 452
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionSavedFrame]
  have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1)))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24)
        (Entails.sepExists_right (s0.readReg64 .x23)
          (Entails.sepExists_right (s0.readReg64 .x22)
            (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20)
                (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

end CryptoVerification.SpqrV1.Prost.MessageEncode
