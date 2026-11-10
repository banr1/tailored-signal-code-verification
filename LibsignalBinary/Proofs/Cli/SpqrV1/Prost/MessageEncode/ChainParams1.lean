/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `prost::encoding::message::encode<ChainParams>` Verification

Proves `encode_chainParams_1_ok_ext` and `encode_chainParams_1_ok_ext_x` for
`prost::encoding::message::encode::<ChainParams, Vec<u8>> [local#3]` on the CLI image.
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

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.cp1_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  subst hfn; exact h1

open Lean Elab Tactic in
elab "cp1_fetches_cli " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (num% (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]"))
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]").decl
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.cp1_fetch_add $hfn (k := $kq) ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec)))

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_reserve_212_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 228#64 →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 → sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm → curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 212 228
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 300 320
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48_do_reserve2_call hres b A ext hdoReserve v curCap curPtr sp
      (entry + 312#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs (mid := entry + 228#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs (mid := entry + 228#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_reserve_128_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 144#64 →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm → curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 128 144
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 280 300
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48_do_reserve2_call hres b A ext hdoReserve v curCap curPtr sp
      (entry + 292#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_hdr_1 {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap0 ptr0 sp : BitVec 64) (bs0 : List (BitVec 8))
    (hfit_hdr : bs0.length + (chainParamsHeaderBytes tag p).length ≤ cap0.toNat ∨
      bs0.length + (chainParamsHeaderBytes tag p).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 0#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump) (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v) (hcs : MsgEnc48CalleeSaved s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64),
      sm.pc = entry + (if p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 → MsgEnc48CalleeSaved s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (chainParamsHeaderBytes tag p).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap1 ptr1 (bs0 ++ chainParamsHeaderBytes tag p) ∗ A.pool ∗
          stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry := Or.inl hfn1
  have hlen_eq := chainParamsHeaderBytes_len_eq tag p
  obtain ⟨hb1, hb2, _⟩ := chainParamsHeaderBytes_len_bounds tag p
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_prologue hres b ext hfn v sp tag p (by rw [hpc, BitVec.add_zero])
    hrun hsp halign htr hw0 hw1 hw2 hx3 hcs hhs0
    (F := vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F) (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 40 44
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 116 120
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 204 208
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_varint_call b A ext hencVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)
    v cap0 ptr0 sp (entry + 44#64) bs0 (by omega)
    (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_len b ext hfn p v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hcs3
  have hfit_len : (bs0 ++ LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length)).length ≤ cap01.toNat ∨
      (bs0 ++ LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit_hdr with h | h
    · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
    · right; omega
  cases hmo : (p.maxOooKeys == 0#32)
  · simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc3
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    refine step_msg48_encode_varint_call b A ext hencVarint
      (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) v cap01 ptr01 sp (entry + 120#64)
      (bs0 ++ LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)) hfit_len
      (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs34.2.2.1]; simp only [arm64_norm, *]
    rw [bs0_append_chainParamsHeaderBytes bs0 tag p]
    have hpc4' : s4.pc = entry + (if p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
      simp only [hmo, Bool.false_eq_true, ↓reduceIte, hpc4]
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_hdr_branch b ext hfn p v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s5 sv3 cap1 ptr1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_)
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append]; omega)
  · simp only [hmo, ↓reduceIte] at hpc3
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    refine step_msg48_encode_varint_call b A ext hencVarint
      (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) v cap01 ptr01 sp (entry + 208#64)
      (bs0 ++ LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64)) hfit_len
      (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs34.2.2.1]; simp only [arm64_norm, *]
    rw [bs0_append_chainParamsHeaderBytes bs0 tag p]
    have hpc4' : s4.pc = entry + (if p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
      simp only [hmo, ↓reduceIte, hpc4]
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_hdr_branch b ext hfn p v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s5 sv3 cap1 ptr1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_)
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append]; omega)

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_maxJump_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (p : ChainParamsPB) (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit_mj : curBs.length + (Proto.encodeUint32Field 1#32 p.maxJump).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 1#32 p.maxJump).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if p.maxJump == 0#32 then 124#64 else 212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + (if p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 1#32 p.maxJump).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 1#32 p.maxJump) ∗
          A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry := Or.inl hfn1
  cases hmj : (p.maxJump == 0#32)
  · simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨hlen_mj, hge2_mj⟩ := maxJump_field_len_of_ne_zero p hmj
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_reserve_212_1 hres b A ext hfn1 hdoReserve v curCap curPtr sp curBs p (by omega)
      hpc hrun hsp halign htr hx19 hx20 hx21 hcs hP ?_
    intro s1 cap01 ptr01 hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hlt01 hge01 hpres01
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_push_maxJump_tag b A ext hfn v cap01 ptr01 sp curBs p hlt01
      hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1
      (F := A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hx21_2 hcs2
    cp1_fetches_cli b (Rust.withPanics ext) hfn1 256 260
    examples_hide_fetches
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (p.maxJump.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_mj with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48_encode_varint_call b A ext hencVarint (p.maxJump.zeroExtend 64)
      v cap01 ptr01 sp (entry + 260#64) (curBs ++ [0x08#8]) hfit_v (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv2)
      (by ac_rfl) ?_
    intro s3 nextCap nextPtr hpc3 hrun3 hsp3 htr3 hcs23 hcs3 hge1 hpres1
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    rw [bs_append_maxJump_of_ne_zero curBs p hmj]
    have hpc3' : s3.pc = entry + (if p.maxJump == 0#32 then 124#64 else 260#64) := by
      simp only [hmj, Bool.false_eq_true, ↓reduceIte, hpc3]
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_maxJump_branch b ext hfn p v sp hpc3' hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
    refine hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · subst hP
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_after_maxJump_branch b ext hfn p v sp
      (by simp only [hmj, ↓reduceIte] at hpc ⊢; exact hpc) hrun hsp htr hx19 hx20 hcs ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
    rw [← bs_append_maxJump_of_zero curBs p hmj]
    exact hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)

private theorem calleeSavedPreserved_setPC {s0 s : State} (pc : BitVec 64)
    (hcc : CalleeSavedPreserved s0 s) :
    CalleeSavedPreserved s0 (s.setPC pc) := by
  simpa only [CalleeSavedPreserved, State.readReg64_setPC, calleeSavedVRegs_setPC] using hcc

private theorem msgEnc48CalleeSaved_setPC {s0 s : State} (pc : BitVec 64)
    (hcs : MsgEnc48CalleeSaved s0 s) (hinv : StepInv s (s.setPC pc)) :
    MsgEnc48CalleeSaved s0 (s.setPC pc) :=
  hcs.step (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) hinv

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_tailcall_184_1 {resStack : Nat} (hres96 : resStack + 96 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hfit_v : curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((vecU8At A v nextCap nextPtr (curBs ++ LibsignalProtoCodec.encodeVarint val) ∗
        A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  cp1_fetches_cli b (Rust.withPanics ext) hfn1 184 188
  examples_hide_fetches
  subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  exact step_msg48_encode_varint_tailcall (s := s.setPC (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)))
    hres96 b A ext hencVarint val v curCap curPtr sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) curBs hfit_v (F := F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun)
    ((State.sp_setPC _ _).trans hsp)
    halign
    ((State.trace_setPC _ _).trans htr)
    ((State.readReg64_setPC _ _ _).trans hlr)
    ((State.readReg64_setPC _ _ _).trans hx0)
    ((State.readReg64_setPC _ _ _).trans hx1)
    (calleeSavedPreserved_setPC _ hcc)
    (msgEnc48CalleeSaved_setPC _ hcs hinv)
    rfl hnext

private theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_maxOooKeys_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = entry)
    {s0 s : State}
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64)) (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (p : ChainParamsPB) (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hfit_mo : curBs.length + (Proto.encodeUint32Field 2#32 p.maxOooKeys).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 2#32 p.maxOooKeys).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if p.maxOooKeys == 0#32 then 264#64 else 128#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInv s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 2#32 p.maxOooKeys).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 2#32 p.maxOooKeys) ∗
        A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.IsChainParamsEncodeEntry b ext entry := Or.inl hfn1
  have hres96 : resStack + 96 < 2 ^ 64 := by omega
  cases hmo : (p.maxOooKeys == 0#32)
  · simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨hlen_mo, hge2_mo⟩ := maxOooKeys_field_len_of_ne_zero p hmo
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_reserve_128_1 hres b A ext hfn1 hdoReserve v curCap curPtr sp curBs p (by omega)
      hpc hrun hsp halign htr hx19 hx20 hcs
      (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by rw [hP]; ac_rfl) ?_
    intro s1 cap01 ptr01 hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hcs1 hlt01 hge01 hpres01
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_push_maxOooKeys_epilogue b A ext hfn v cap01 ptr01 sp sv3 curBs p hlt01
      hpc1 hrun1 hsp1 halign htr1 hx1_1 hx19_1 hx20_1 hcs1
      (F := A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hlr2 hx0_2 hx1_2 hcc2 hcs2
    have hfit_v : (curBs ++ [0x10#8]).length +
        (LibsignalProtoCodec.encodeVarint (p.maxOooKeys.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x10#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_mo with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_tailcall_184_1 hres96 b A ext hfn1 hencVarint (p.maxOooKeys.zeroExtend 64)
      v cap01 ptr01 sp sv3 (curBs ++ [0x10#8]) hfit_v
      hpc2 hrun2 hsp2 halign htr2 hlr2 hx0_2 hx1_2 hcc2 hcs2 (F := F) (by ac_rfl) ?_
    intro sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf hge1 hpres1
    have hq := hnext sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf.2.2.2.2.2.2.2.2 (Nat.le_trans hge01 hge1) (by
      intro hle
      obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
      exact hpres1 (by rw [List.length_append, List.length_singleton]; omega))
    rwa [← bs_append_maxOooKeys_of_ne_zero curBs p hmo] at hq
  · simp only [hmo, ↓reduceIte] at hpc
    refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_chainParams_epilogue hres96 b ext hfn sp sv3 hpc hrun hsp halign htr hcs
      (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F) (by rw [hP]; ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hinvf
    have hq := hnext sf curCap curPtr hpcf hrunf hspf htrf hccf hinvf (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    rw [bs_append_maxOooKeys_of_zero curBs p hmo] at hq
    have hEq : stackAt sp (msgEnc48VarintStackOf resStack) ∗ (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F) =
        (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F := by
      ac_rfl
    rwa [hEq]

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParams1_gen_ok_ext {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodeChainParamsGhost} {R : SepProp} {s0 : State}
    (hencV : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeChainParamsSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeChainParamsSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainParamsSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn1 : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name := rfl
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres96 : resStack + 96 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodeChainParamsSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hw1, hw2, hx3, _, _, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48VarintStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeChainParamsMsg_len_split x.tag x.p
  have hfit_hdr : x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat ∨
      x.bs.length + (chainParamsHeaderBytes x.tag x.p).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_hdr_1 hres96 b A ext hfn1 hencV x.tag x.p x.v x.cap x.ptr s0.sp x.bs hfit_hdr
    (F := emp) (by rw [hpc, BitVec.add_zero]) hrun rfl halign rfl hw0 hw1 hw2 hx3
    (MsgEnc48CalleeSaved.refl s0) rfl rfl ?_
  intro s1 sv3 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs1 hge1 hpres1
  have hfit_mj : (x.bs ++ chainParamsHeaderBytes x.tag x.p).length +
      (Proto.encodeUint32Field 1#32 x.p.maxJump).length ≤ cap1.toNat ∨
      (x.bs ++ chainParamsHeaderBytes x.tag x.p).length +
      (Proto.encodeUint32Field 1#32 x.p.maxJump).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_maxJump_1 hres b A ext hfn1 hencV hdoR x.p x.v cap1 ptr1 s0.sp
    (x.bs ++ chainParamsHeaderBytes x.tag x.p) hfit_mj hpc1 hrun1 hsp1 halign htr1
    hx19_1 hx20_1 hx21_1 hcs1
    (F := msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  have hfit_mo : ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ Proto.encodeUint32Field 1#32 x.p.maxJump).length +
      (Proto.encodeUint32Field 2#32 x.p.maxOooKeys).length ≤ cap2.toNat ∨
      ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ Proto.encodeUint32Field 1#32 x.p.maxJump).length +
      (Proto.encodeUint32Field 2#32 x.p.maxOooKeys).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_append]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [List.length_append]; omega)
      omega
    · right; omega
  refine CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.step_maxOooKeys_1 hres b A ext hfn1 hencV hdoR x.p x.v cap2 ptr2 s0.sp sv3
    ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ Proto.encodeUint32Field 1#32 x.p.maxJump)
    hfit_mo hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (F := emp) (by ac_rfl) ?_
  intro sf cap3 ptr3 hpcf hrunf hspf htrf hccf hinvf hge3 hpres3
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hge_all : x.cap.toNat ≤ cap3.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 hge3)
  have hpres_all : x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
      cap3 = x.cap ∧ ptr3 = x.ptr := by
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by rw [List.length_append]; omega)
    exact hpres3 (by rw [List.length_append, List.length_append]; omega)
  dsimp only [encodeChainParamsSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap3, ptr3, ?_⟩
  have hpure : (x.cap.toNat ≤ cap3.toNat ∧
      (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
        cap3 = x.cap ∧ ptr3 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj, bs0_append_encodeChainParamsMsg x.bs x.tag x.p]
  convert hm using 1; ac_rfl

/-- `prost::encoding::message::encode::<ChainParams, Vec<u8>> [local#3]` satisfies
`EncodeChainParams1OkExt`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_chainParams_1_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeChainParams1OkExt b A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_encodeVarint2_fnAddr_eq]; exact CryptoVerification.Cli.SpqrV1.Varint.encode_varint2_fit_ok_ext hA
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      (doReserve2SpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_doReserve2_fnAddr_eq]; exact CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext hA
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParams1_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_ext s0 henc0) (subroutine_ok_withMsgEnc48CS_ext s0 hdoR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- `prost::encoding::message::encode::<ChainParams, Vec<u8>> [local#3]` satisfies
`EncodeChainParams1OkX` under `AllocContracts img.base A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_chainParams_1_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EncodeChainParams1OkX img A ext := by
  have hdoReserve := CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_encodeVarint2_fnAddr_eq]
    exact CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2_fit_ok_ext_x img A ext hdoReserve
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") % 2^64))
      ((doReserve2SpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_doReserve2_fnAddr_eq]; exact hdoReserve
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.chainParams1_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 henc0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hdoR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Prost.MessageEncode
