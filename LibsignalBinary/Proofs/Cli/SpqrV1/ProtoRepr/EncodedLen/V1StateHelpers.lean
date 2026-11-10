/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent -- shake: keep
public meta import Lean -- shake: keep

/-!
# CLI `V1State::encoded_len` Shared Tails and Single-Callee Branches

Defines `IsV1StateEntry` and proves shared outer-varint/epilogue tails (`+524`, `+1580`) and
single-callee variant branches (`k = 0, 2, 7`: `.keysUnsampled`, `.headerSent`, `.ct1Sampled`) for
`V1State::encoded_len` on the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

/-! ## 1. Entry Membership and Instruction Fetch Macro -/

/-- Entry-point membership for the two CLI copies of `V1State::encoded_len`. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr v1StateEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "v1State_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]")), 0x62a00]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x62a00
  ]
  let skip : Array Nat := #[
    56, 60,
    124, 188, 260, 324, 376, 408, 472, 520, 600, 664,
    756, 820, 912, 976, 1024, 1076, 1140, 1192, 1256,
    1332, 1336, 1340, 1372, 1376, 1380, 1412, 1416, 1420,
    1452, 1456, 1460, 1492, 1496, 1500, 1532, 1536, 1540,
    1556, 1560, 1564, 1620, 1624, 1628, 1632, 1636, 1640
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    if !skip.contains k then
      let decs := offs.map fun off =>
        mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
          s!"spqrV1StateBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
      let d0 := decs[0]!; let d1 := decs[1]!
      let f0 := fnOffs[0]!; let f1 := fnOffs[1]!
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        evalTactic (← `(tactic|
          have := pair_fetch_entry $hfn
            ($fetchEntry (b := $b) (H := $H) $f0 (by decide) $d0)
            ($fetchEntry (b := $b) (H := $H) $f1 (by decide) $d1)))
      else
        evalTactic (← `(tactic|
          have := pair_fetch_add $hfn (k := $kq)
            ($fetchAdd (b := $b) (H := $H) (k := $kq) $f0 (by decide) $d0)
            ($fetchAdd (b := $b) (H := $H) (k := $kq) $f1 (by decide) $d1)))

/-! ## 2. Niche Arithmetic & Stack Split Helpers -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 3. Option Cap / Rest Splits for `Unchunked` Sub-Messages -/

/-- Direct epilogue at `+524` (`0x20c`): given `X0 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)`
    and `v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64`, computes `1 + varintLen + len` in `X0`,
    restores `x19, fp, lr`, and returns to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_524 (b : BitVec 64)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 524 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Shared outer-varint + epilogue tail at `+1580` (`0x62c`): given
    `X8 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)` and
    `v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64`, computes `1 + varintLen + len` in `X0`,
    branches `HI` to `+564`, restores `x19, fp, lr`, and returns to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 (b : BitVec 64)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1580 1620
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 564 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-! ## 4. Single-Callee Variant Branches (`k = 0, 2, 7`) -/

/-- Branch `k = 0` (`keysUnsampled`, `+80`): steps from `entry + 80#64` through `+1580` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_keysUnsampled (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (g : Unchunked2PBGhost) (a sp : BitVec 64) (v : V1State.Chunked.KeysUnsampled)
    (hfit : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : (optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
            (optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 80 100
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1028 1072
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap with ⟨hcap_beq, hcap_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_beq hcap_bne
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none]
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none, ← huc]
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, optKeysUnsampledPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_beq hcap_bne
    have hu_fit : keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optKeysUnsampledPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u)]
    apply SepWPp.of_sepWP (mid := entry + 1024#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u), ← huc]
    have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((keysUnsampledPBPinnedAt A g (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by
      simp only [huc, optKeysUnsampledPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl
    refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf_eq := bv_optMsgField_some (inner := keysUnsampledPBEncodedLen u)
      (tot := optKeysUnsampledPBFieldEncodedLen (some u)) rfl
    have htot_fit : optKeysUnsampledPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) <
        optKeysUnsampledPBFieldEncodedLen (some u) := by
      simp only [optKeysUnsampledPBFieldEncodedLen]; omega
    have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hf_eq, hx0_1])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 2` (`headerSent`, `+372`): steps `ADD X0, X0, #8; BL Chunked.HeaderSent; B +524`
    through `+524..+572` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerSent (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.HeaderSent)
    (hfit : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.headerSent v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 372 384
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  apply SepWPp.of_sepWP (mid := entry + 376#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPp.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) v _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPp.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  apply SepWPp.of_sepWP (mid := entry + 524#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_524 b abs entry hfn sp (.headerSent v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, hx0_1])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 7` (`ct1Sampled`, `+520`): steps `BL Chunked.Ct1Sampled` and falls through
    to `+524..+572`, returning to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Sampled (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.Ct1Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedCt1SampledPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPp.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g a (sp - 32#64) v s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPp.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_524 b abs entry hfn sp (.ct1Sampled v) hfit
    hpc1 hrun1 hsp1 halign (by simpa [v1StateInnerPayloadEncodedLen] using hx0_1)
    ⟨by simp [h20_1, h20], by simp [h21_1, h21], by simp [h22_1, h22],
     by simp [h23_1, h23], by simp [h24_1, h24], by simp [h25_1, h25],
     by simp [h26_1, h26], by simp [h27_1, h27], by simp [h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by rw [htrf, htr1]) hx0f hcsf

end CryptoVerification.SpqrV1.ProtoRepr
