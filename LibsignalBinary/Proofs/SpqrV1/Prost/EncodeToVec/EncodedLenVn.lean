/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import ProofLib.SepLogic.WPp

/-!
# Phase 1a (`0x6d010 .. 0x6d18c/0x6d1bc`): Prologue and `Option<VersionNegotiation>::encoded_len`

Proves symbolic execution of the prologue and inline `Option<VersionNegotiation>::encoded_len`
in `<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`:
1. Prologue (`+0 .. +48`, `0x6d010 .. 0x6d040`): allocates the 144-byte frame (`sp - 144#64`),
   saves `x19..x28, x29, x30` at `[sp - 96#64, sp)`, sets `x29 = sp - 96#64`, `x20 = a`,
   `x27 = sret`, and loads `x25 = optVersionNegCap g.vn st.versionNegotiation`.
2. Inline `Option<VersionNegotiation>::encoded_len` (`+48 .. +380/+428`, `0x6d040 .. 0x6d18c/0x6d1bc`):
   computes `x21 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## Instruction Fetch Infrastructure & Shared `SepWPp` Helpers -/

theorem encodeToVec_fetch_entry {prog : Program} {name : String}
    {entry : BitVec 64} (hfn : prog.fnAddr name = entry) {ins : Instr}
    (h : prog.fetch (prog.fnAddr name) = some ins) :
    prog.fetch entry = some ins :=
  hfn ▸ h

theorem encodeToVec_fetch_add {prog : Program} {name : String}
    {entry : BitVec 64} (hfn : prog.fnAddr name = entry) {k : Nat} {ins : Instr}
    (h : prog.fetch (prog.fnAddr name + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins :=
  hfn ▸ h

open Lean Elab Tactic in
scoped elab "etv_fetches " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let off := 0x67c18
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x67c18
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.EncodeToVec |>.str
      s!"spqrEncodeToVecBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := encodeToVec_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff (by decide) $dec)))
    else
      evalTactic (← `(tactic|
        have := encodeToVec_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec)))

/-! ## Step 1a: `VersionNegotiation::encoded_len` Sub-Blocks (`+52 .. +368`, `0x6d044 .. 0x6d180`) -/

/-- Step `+52 .. +88` (`0x6d044 .. 0x6d068`): computes `x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)`. -/
theorem step_encodeToVec_vn_authKey (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 52#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 88#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 52 88
  examples_hide_fetches; subst hP
  dsimp only [versionNegotiationRest]
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := EncodedLen.bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    apply SepWPp.of_sepWP_cs (mid := entry + 88#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = vn.authKey.length := by
      unfold bytesFieldEncodedLen
      cases h : vn.authKey with
      | nil => rfl
      | cons _ _ => rw [h] at hemp; cases hemp
    apply SepWPp.of_sepWP_cs (mid := entry + 88#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hzero, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Step `+88 .. +160/+288` (`0x6d068 .. 0x6d0b0/0x6d130`): computes `x9 = i32VarintFieldEncodedLen vn.direction`
and `x10 = i32VarintFieldEncodedLen vn.minVersion`, reaching either `+160` or `+288`. -/
theorem step_encodeToVec_vn_dir_minVer (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 88#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = entry + 160#64 ∨ s1.pc = entry + 288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 88 160
  etv_fetches b (Rust.withPanics ext) hfn 272 288
  examples_hide_fetches; subst hP
  dsimp only [versionNegotiationRest]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_mv : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = false := by simp [hmv]
    by_cases hdir : vn.direction = 0#32
    · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
      have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
      have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
      apply SepWPp.of_sepWP_cs (mid := entry + 288#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)
    · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
      have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
      have hstep_d := bv_i32VarintField_nonzero hdir
      apply SepWPp.of_sepWP_cs (mid := entry + 288#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · have hbeq_mv : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_mv := bv_i32VarintField_nonzero hmv
    suffices h132 : ∀ s_mid : State,
        s_mid.pc = entry + 132#64 → s_mid.status = .Running → s_mid.sp = s.sp → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = s.readReg64 .x8 →
        s_mid.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
        s_mid.readReg64 .x10 = vn.minVersion.signExtend 64 →
        s_mid.readReg64 .x20 = a → s_mid.readReg64 .x25 = s.readReg64 .x25 →
        s_mid.readReg64 .x27 = s.readReg64 .x27 → s_mid.readReg64 .fp = s.readReg64 .fp →
        StepInv s0 s_mid →
        SepWPp (spqrProgAtExt b ext) ret s_mid (versionNegotiationRest A g a vn ∗ F) Q Qp by
      by_cases hdir : vn.direction = 0#32
      · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
        have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
        have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
        apply SepWPp.of_sepWP_cs (mid := entry + 132#64); wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
        exact h132 _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv)
      · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
        have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
        have hstep_d := bv_i32VarintField_nonzero hdir
        apply SepWPp.of_sepWP_cs (mid := entry + 132#64); wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
        exact h132 _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv)
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx20_m hx25_m hx27_m hfp_m hinv_m
    apply SepWPp.of_sepWP_cs (mid := entry + 160#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv)

/-- Step `+160/+288 .. +324` (`0x6d0b0/0x6d130 .. 0x6d154`): computes
`x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)`. -/
theorem step_encodeToVec_vn_chainParams (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 160#64 ∨ s.pc = entry + 288#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 324#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = s.readReg64 .x10 →
      s1.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 160 244
  etv_fetches b (Rust.withPanics ext) hfn 288 324
  examples_hide_fetches; subst hP
  dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsPBFieldEncodedLen]
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 324#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       refine SepWPp.weaken_pre
         (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
             simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
         (hnext _
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *])
           (by rw [hcp]; simp only [arm64_norm, optChainParamsPBFieldEncodedLen, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)))
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    suffices h172 : ∀ s_mid : State,
        s_mid.pc = entry + 172#64 → s_mid.status = .Running → s_mid.sp = s.sp → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = s.readReg64 .x8 → s_mid.readReg64 .x9 = s.readReg64 .x9 →
        s_mid.readReg64 .x10 = s.readReg64 .x10 → s_mid.readReg64 .x20 = a →
        s_mid.readReg64 .x25 = s.readReg64 .x25 → s_mid.readReg64 .x27 = s.readReg64 .x27 →
        s_mid.readReg64 .fp = s.readReg64 .fp → StepInv s0 s_mid →
        SepWPp (spqrProgAtExt b ext) ret s_mid
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
           EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
           ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
           ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
           memRegion (a + 44#64) 4 ∗ F) Q Qp by
      rcases hpc with hpc | hpc <;>
        (apply SepWPp.of_sepWP_cs (mid := entry + 172#64); wp_steps;
         apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
         refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
           (h172 _
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (hinv0.trans hinv)))
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx20_m hx25_m hx27_m hfp_m hinv_m
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply SepWPp.of_sepWP_cs (mid := entry + 324#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      apply SepWPp.of_sepWP_cs (mid := entry + 324#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply SepWPp.of_sepWP_cs (mid := entry + 324#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      apply SepWPp.of_sepWP_cs (mid := entry + 324#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))

/-- Step `+0 .. +380/+428` (`0x6d010 .. 0x6d18c/0x6d1bc`): prologue + inline
`Option<VersionNegotiation>::encoded_len` + loading `x19 = optChainCap g.chain st.chain`. -/
theorem step_encodeToVec_prologue_and_vn {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (sret a sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running) (hsp : s0.sp = sp)
    (hx0 : s0.readReg64 .x0 = sret) (hx1 : s0.readReg64 .x1 = a)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗ stackAt sp (encodeToVecStackOf resStack)) ∗ F)
    (hnext : ∀ (s1 : State) (v0 v1 v2 v3 v4 v5 : BitVec 64),
      s1.pc = (if st.chain.isSome then entry + 380#64 else entry + 428#64) →
      s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s0.trace →
      (st.chain = none → s1.readReg64 .x8 = 0#64) →
      s1.readReg64 .x19 = optChainCap g.chain st.chain → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) →
      s1.readReg64 .x22 = a + 48#64 →
      s1.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s1.readReg64 .x27 = sret → s1.readReg64 .fp = sp - 96#64 → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1
        ((pqRatchetStatePBPinnedAt A g a st ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s0 P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 0 52
  etv_fetches b (Rust.withPanics ext) hfn 244 272
  etv_fetches b (Rust.withPanics ext) hfn 324 388
  etv_fetches b (Rust.withPanics ext) hfn 424 428
  examples_hide_fetches; subst hP
  have hsp_sub_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = sret := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  rw [stackAt_encodeToVec_split hres sp, pqRatchetStatePBPinnedAt,
    optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 =>
    SepWPp.exists_elim fun v3 => SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => ?_
  rw [cells_12_sub_96_eq sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => SepWPp.exists_elim fun r2 =>
    SepWPp.exists_elim fun r3 => SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r5 =>
    SepWPp.exists_elim fun r6 => SepWPp.exists_elim fun r7 => SepWPp.exists_elim fun r8 =>
    SepWPp.exists_elim fun r9 => SepWPp.exists_elim fun r10 => SepWPp.exists_elim fun r11 => ?_
  refine sepWPp_extract_pure
    (((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
       (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome) ∧
     ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
       (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome))
    (fun R hm => ⟨?_, ?_⟩) (fun ⟨hvn_cap, hch_cap⟩ => ?_)
  · apply optVersionNegRest_cap_bounds (A := A) (p := a)
      (R := (a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
        ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        optChainRest A g.chain (a + 0x30#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11) ∗ F ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · apply optChainRest_cap_bounds (A := A) (p := a + 0x30#64)
      (R := (a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
        optVersionNegRest A g.vn a st.versionNegotiation ∗
        ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11) ∗ F ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  apply SepWPp.of_sepWP_cs (mid := entry + 44#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_pro
  refine SepWPp.weaken_pre
    (P' := ((a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
      optVersionNegRest A g.vn a st.versionNegotiation ∗
      ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      optChainRest A g.chain (a + 0x30#64) st.chain ∗
      optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (by rw [encodeToVecSavedRegs]; exact Entails.of_eq (by ac_rfl)) ?_
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hvn_cap hinv_pro
    simp only [Option.isSome_none, Bool.not_false] at hvn_cap
    cases hch : st.chain with
    | none =>
      rw [hch] at hch_cap
      simp only [Option.isSome_none, Bool.not_false] at hch_cap
      apply SepWPp.of_sepWP_cs (mid := entry + 428#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun _ => by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, optVersionNegotiationPBFieldEncodedLen, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_pro.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      exact Entails.of_eq (by ac_rfl)
    | some ch =>
      rw [hch] at hch_cap
      simp only [Option.isSome_some, Bool.not_true] at hch_cap
      apply SepWPp.of_sepWP_cs (mid := entry + 380#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_some, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun h => by rw [hch] at h; cases h)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, optVersionNegotiationPBFieldEncodedLen, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_pro.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      exact Entails.of_eq (by ac_rfl)
  | some vn =>
    have hauth_lt := vn_authKey_len_lt_of_state hvn hlen
    rw [hvn] at hvn_cap hinv_pro
    simp only [Option.isSome_some, Bool.not_true] at hvn_cap
    dsimp only [optVersionNegRest]
    apply SepWPp.of_sepWP_cs (mid := entry + 52#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    let F_vn : SepProp :=
      ((a ↦₆₄ optVersionNegCap g.vn (some vn)) ∗
       ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
       optChainRest A g.chain (a + 0x30#64) st.chain ∗
       optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
       stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
       encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
       encodeToVecSavedRegs sp s0) ∗ F
    refine SepWPp.weaken_pre (P' := versionNegotiationRest A g.vn a vn ∗ F_vn)
      (Entails.of_eq (by dsimp only [F_vn]; ac_rfl)) ?_
    refine step_encodeToVec_vn_authKey b A ext hfn a g.vn vn hauth_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hinv_pro.trans hinv0) rfl ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx20_1 hx25_1 hx27_1 hfp1 hinv1
    refine step_encodeToVec_vn_dir_minVer b A ext hfn a g.vn vn
      hpc1 hrun1 hx20_1 hinv1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx8_2 hx9_2 hx10_2 hx20_2 hx25_2 hx27_2 hfp2 hinv2
    refine step_encodeToVec_vn_chainParams b A ext hfn a g.vn vn
      hpc2 hrun2 hx20_2 hinv2 rfl ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx8_3 hx9_3 hx10_3 hx11_3 hx20_3 hx25_3 hx27_3 hfp3 hinv3
    have hvn_sum := bv_vn_sum_eq vn
    have hopt_vn := bv_optVN_some_eq vn
    cases hch : st.chain with
    | none =>
      rw [hch] at hch_cap
      simp only [Option.isSome_none, Bool.not_false] at hch_cap
      dsimp only [F_vn]; rw [hch]
      apply SepWPp.of_sepWP_cs (mid := entry + 428#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun _ => by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv3.trans hinv4))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      dsimp only [optVersionNegRest]
      exact Entails.of_eq (by ac_rfl)
    | some ch =>
      rw [hch] at hch_cap
      simp only [Option.isSome_some, Bool.not_true] at hch_cap
      dsimp only [F_vn]; rw [hch]
      apply SepWPp.of_sepWP_cs (mid := entry + 380#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_some, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun h => by rw [hch] at h; cases h)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv3.trans hinv4))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      dsimp only [optVersionNegRest]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.EncodeToVec
