/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `encode<ChainParams> [local#3]` Step Lemmas

Proves basic-block step lemmas (prologue, inline encoded-length computation, tag pushes, branch
splits, and epilogue) for `prost::encoding::message::encode::<ChainParams, Vec<u8>> [local#3]` on
the CLI image.
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

@[local arm64_norm] private theorem zext64_trunc32_orr_1 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 1#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_trunc32_orr_100000001 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 0x100000001#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_orr_1_32 (w : BitVec 32) :
    BitVec.zeroExtend 64 (w ||| 1#32) = BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeChainParams1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name)
    (encodeChainParamsSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeChainParams1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name)
    ((encodeChainParamsSpecX A).inImage img)

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_encodeVarint2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name, CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name, h1, h2]
  bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_doReserve2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name, CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name, h1, h2]
  bv_omega

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry ∨
    (tripleRatchetProgAtExt b ext).fnAddr encodeChainParams2Name = entry

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParamsEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeChainParams2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParamsEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeChainParams2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
elab "chainParams_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off1 := (num% (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]"))
  let off2 := 0x4cd78
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]").decl
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4cd78
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}"))
    let dec2 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParamsEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParamsEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

open Lean Elab Tactic in
elab "chainParams1_fetches_range_cli " b:term:max H:term:max _entry:term:max
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (num% (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]"))
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]").decl
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $fnOff (by decide) $dec))
    else
      evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec))

/-- Shared prologue (`+0x000..+0x028`, offsets `0..40`):
saves `fp, lr, x21, x20, x19`, sets `x19 = v`, `x20 = p.maxOooKeys.zeroExtend 64`,
`x21 = p.maxJump.zeroExtend 64`, `x0 = (2#32 ||| (tag <<< 3)).zeroExtend 64`, `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_prologue {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (v sp : BitVec 64) (tag : BitVec 32) (p : ChainParamsPB)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hhs0 : s = s0)
    (hP : P = stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = entry + 40#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (2#32 ||| (tag <<< 3)).zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 0 40
  examples_hide_fetches
  subst hP hhs0
  dsimp only [State.readReg32, Reg.x0, Reg.x1, Reg.x2] at hw0 hw1 hw2
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_varint hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 40#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ sv3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; congr 1; bv_bits)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))
  dsimp only [msgEnc48SavedFrame]
  exact Entails.of_eq (by ac_rfl)

/-- Shared length computation (`+0x02c..+0x074` / `+0x0bc..+0x0cc`, offsets `44..116` and `188..204`):
when `(p.maxOooKeys == 0#32) = false`, reaches `entry + 116#64` (`+0x074`);
when `(p.maxOooKeys == 0#32) = true`, reaches `entry + 204#64` (`+0x0cc`);
in both cases with `x0 = BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length` and `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_len (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 44#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if p.maxOooKeys == 0#32 then 204#64 else 116#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 44 116
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 188 204
  examples_hide_fetches
  have hraw := chainParams_encodeRaw_length p
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    have hadd := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen p.maxJump) (u32VarintFieldEncodedLen p.maxOooKeys)
    apply SepWPp.of_sepWP_cs (mid := entry + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply SepWPp.of_sepWP_cs (mid := entry + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmo_z, Nat.add_zero]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    apply SepWPp.of_sepWP_cs (mid := entry + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, Nat.zero_add]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply SepWPp.of_sepWP_cs (mid := entry + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, hmo_z]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

/-- Shared `maxJump` tag push (`+0x0e4..+0x100`, offsets `228..256`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`
and sets `x0 = p.maxJump.zeroExtend 64`, `x1 = v`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_push_maxJump_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 256#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = p.maxJump.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 228 256
  examples_hide_fetches
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 256#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Shared `maxOooKeys` tag push + frame restore (`+0x090..+0x0b8`, offsets `144..184`):
given `curBs.length < curCap.toNat`, pushes `0x10#8` (`tag = 2`, varint) to `buf`,
sets `x0 = p.maxOooKeys.zeroExtend 64`, `x1 = v`, and restores the 48-byte stack frame
(`sp = sp`, `lr = s0.readReg64 .lr`), arriving at `entry + 184#64` (`+0x0b8`, the `b encode_varint` tailcall). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_push_maxOooKeys_epilogue (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 184#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr →
      sm.readReg64 .x0 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      CalleeSavedPreserved s0 sm →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 144 184
  examples_hide_fetches
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 184#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by epochEncLen_cc_close)
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩)
  dsimp only [msgEnc48SavedFrame]
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Shared epilogue (`+0x108..+0x118`, offsets `264..280`):
restores `x20, x19, x21, fp, lr` and `sp`, returning to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_epilogue {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (sp sv3 : BitVec 64)
    {s0 s : State} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf (stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 264 280
  examples_hide_fetches
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1)))
  exact sepConj_mono_left
    (stackAt_msgEnc48_varint_recombine hres sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))

/-- Shared branch after header length varint (`120..124` or `208..212`):
lands at `entry + (if p.maxJump == 0#32 then 124#64 else 212#64)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_hdr_branch (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if p.maxOooKeys == 0#32 then 208#64 else 120#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 120 124
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 208 212
  examples_hide_fetches
  cases hmo : (p.maxOooKeys == 0#32) <;> cases hmj : (p.maxJump == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 124#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 124#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

/-- Shared branch after `maxJump` (`124..128` or `260..264`):
lands at `entry + (if p.maxOooKeys == 0#32 then 264#64 else 128#64)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_maxJump_branch (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry)
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if p.maxJump == 0#32 then 124#64 else 260#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 124 128
  chainParams_fetches_range_cli b (Rust.withPanics ext) entry hfn 260 264
  examples_hide_fetches
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 264#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs (mid := entry + 264#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

end CryptoVerification.SpqrV1.Prost.MessageEncode
