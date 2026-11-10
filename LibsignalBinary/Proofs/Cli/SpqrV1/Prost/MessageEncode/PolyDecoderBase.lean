/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommon
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `encode<PolynomialDecoder> [local#3]` Basic-Block Step Lemmas

Proves pure model bridge lemmas and basic-block step lemmas for
`prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>> [local#3]` on the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth

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

/-! ## Pure Model and `LibsignalSpqrV1.Proto` Bridge Lemmas -/

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodePolyDecoder1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name) (encodePolyDecoderPinnedSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodePolyDecoder1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name) (encodePolyDecoderSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodePolyDecoder1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name)
    ((encodePolyDecoderPinnedSpecX A).inImage img)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodePolyDecoder1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name)
    ((encodePolyDecoderSpecX A).inImage img)

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1_encodedLen1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenLocal1Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name,
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenLocal1Name, h1, h2]; bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1_encodeVarint2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name,
    CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name, h1, h2]; bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1_encodeRepeated1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name + bv% ((2^64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name,
    CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name, h1, h2]; bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1_doReserve2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"); have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name,
    CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name, h1, h2]; bv_omega

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name = entry ∨
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name = entry

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polyDecoderEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polyDecoderEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
scoped elab "pd_fetches_cli" b:term:arg H:term:arg hfn:ident lo:num hi:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off1 := (num% (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"))
  let off2 := 0x4d14c
  let loN := lo.getNat
  let hiN := hi.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]").decl
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d14c
  for i in [loN / 4 : hiN / 4] do
    let k := 4 * i
    let dec1 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}"))
    let dec2 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polyDecoderEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.polyDecoderEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

/-- Prologue (`+0..+36`): allocates the 48-byte frame, saves `fp, lr, x21, x20, x19`, and sets
`x20 = decA`, `x1 = v`, `x19 = v`, and `x0 = ((tag <<< 3) ||| 2#32).zeroExtend 64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_prologue {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) (tag : BitVec 32) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (s1 : State) (sv3 : BitVec 64),
      s1.pc = entry + 36#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 →
      s1.readReg64 .x1 = v → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 0 36; examples_hide_fetches
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  have hw0' : BitVec.truncate 32 (s.readReg64 .x0) = tag := hw0
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 36#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0] at hw0' ⊢; simp only [arm64_norm]
          exact polyDecoder_tag_orr_eq tag)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+40..+44` (`mov x0, x20`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_mov_x0_x20_40
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 44#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = decA → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 40 44; examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 44#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+48..+52` (`mov x1, x19`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_mov_x1_x19_48
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) (decA v x0v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 48#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = x0v) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 52#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = x0v → s1.readReg64 .x1 = v → s1.readReg64 .x19 = v →
      s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 48 52; examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 52#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+56..+64`: loads `w0 = pb.ptsNeeded` from `[x20, #0x18]` and branches to `entry + 108#64`
if zero, else falls through to `entry + 64#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_check_ptsNeeded (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.ptsNeeded == 0#32 then 108#64 else 64#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 56 64
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpn : (pb.ptsNeeded == 0#32)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs (mid := entry + 64#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs (mid := entry + 108#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+80..+104`: pushes tag byte `0x08#8` (field 1, varint) into `curBs` and sets `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_push_ptsNeeded_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 104#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 80 104
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 104#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+108..+116`: loads `w0 = pb.polys` from `[x20, #0x1c]` and branches to `entry + 160#64`
if zero, else falls through to `entry + 116#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_check_polys (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 108#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.polys == 0#32 then 160#64 else 116#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 108 116
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpl : (pb.polys == 0#32)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs (mid := entry + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs (mid := entry + 160#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+132..+156`: pushes tag byte `0x10#8` (field 2, varint) into `curBs` and sets `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_push_polys_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 132#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 156#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 132 156
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 156#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+160..+172`: loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, and sets
`w0 = 3#32`, `x3 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_prep_pts
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) (decA v sp : BitVec 64)
    (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 160#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 172#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg32 .x0 = 3#32 → s1.readReg64 .x1 = g.pts.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → s1.readReg64 .x3 = v →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 160 172; examples_hide_fetches; subst hP
  dsimp only [polyDecoderElemsAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 172#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+176..+188` / `+248..+264`: loads `w8 = boolByte pb.isComplete` from `[decA + 0x20]`;
executes the epilogue at `+248` when `false`, or falls through to `+188` when `true`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_check_isComplete {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} {s0 s : State} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hfalse : pb.isComplete = false → ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F))
    (htrue : pb.isComplete = true → ∀ s1 : State,
      s1.pc = entry + 188#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s1
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 176 188
  pd_fetches_cli b (Rust.withPanics ext) hfn 248 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  cases hc : pb.isComplete
  · have hbyte : boolByte pb.isComplete = 0#8 := by rw [hc]; rfl
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
    apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr)
    dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← hbyte]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    · apply (hfalse hc)
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
  · have hbyte : boolByte pb.isComplete = 1#8 := by rw [hc]; rfl
    apply SepWPp.of_sepWP_cs (mid := entry + 188#64)
    dsimp only [polyDecoderElemsAt]; rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by rw [← hbyte]; dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (htrue hc _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1))

/-- Step `+204..+228`: pushes tag byte `0x20#8` (field 4, varint) into `curBs` and compares
`curCap` with the updated length at `+228`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_push_isComplete_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 204#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx8 : s.readReg64 .x8 = curCap) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 228#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x8 = curCap → s1.readReg64 .x9 = curPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      s1.pstate = subsPState64 curCap (BitVec.ofNat 64 (curBs ++ [0x20#8]).length) →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1
        (vecU8At A v curCap curPtr (curBs ++ [0x20#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 204 228; examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 228#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hlen1 : BitVec.ofNat 64 curBs.length + 1#64 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length := by
    rw [List.length_append, List.length_singleton]; exact (BitVec.ofNat_add curBs.length 1).symm
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x20#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+232..+264`: pushes value byte `0x01#8` into `curBs`, updates `[v + 16]`, and executes
the epilogue. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_polyDecoder_push_isComplete_val_epilogue {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} {s0 s : State} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsPolyDecoderEncodeEntry b ext entry)
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 232#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length) (hx19 : s.readReg64 .x19 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf →
      Q sf ((vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_cli b (Rust.withPanics ext) hfn 232 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr); dsimp only [msgEnc48SavedFrame]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
  refine SepWPp.weaken_pre
    (show _ ⊢ (vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
  · rw [← vecU8At_close_one A v curCap curPtr curBs 0x01#8 hlt]
    have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19)
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
    dsimp only [msgEnc48SavedFrame]
  · apply hnext
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · epochEncLen_cc_close
    · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩

end CryptoVerification.SpqrV1.Prost.MessageEncode
