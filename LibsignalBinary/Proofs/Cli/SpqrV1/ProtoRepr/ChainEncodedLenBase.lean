/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.Fetch
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Fetch
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `Chain::encoded_len` Base Definitions and `links` Loop Lemmas

Defines CLI `Chain::encoded_len` contract predicates, entry membership, and instruction-fetch
elaboration, and proves field-layout decomposition and `links: Vec<Epoch>` loop lemmas.
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

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.epochLocal1_fnAddr_eq_chainLocal1_sub (b : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLenLocal1Name =
      (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" - ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") % 2^64) :=
  Program.fnAddr_callee_add_of_fnOff
    (ls_lemma% fnOff "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]")
    (ls_lemma% fnOff "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]")
    rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.bl_target_of_local1 {b : BitVec 64} {abs : String → Option (State → State)}
    {entry epochEntry : BitVec 64}
    (h1 : (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name = entry)
    (h2 : (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLenLocal1Name = epochEntry) :
    entry + 124#64 + (-3160#64) = epochEntry ∧
    entry + (124#64 + (-3160#64)) = epochEntry ∧
    entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" - ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") % 2^64) = epochEntry ∧
    entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" - ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") % 2^64) = epochEntry := by
  subst h1; subst h2
  rw [CryptoVerification.Cli.SpqrV1.ProtoRepr.epochLocal1_fnAddr_eq_chainLocal1_sub]
  refine ⟨by bv_lin, by bv_lin, rfl, by bv_lin⟩

attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.ProtoRepr.sext64_truncate32
  CryptoVerification.SpqrV1.ProtoRepr.signExtend64_beq_zero64

/-- `Chain::encoded_len [local#3]` satisfies `chainEncodedLenPinnedSpec A` on
`tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name)
    (chainEncodedLenPinnedSpec A)

/-- `Chain::encoded_len [local#3]` satisfies `chainEncodedLenSpec A` on
`tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name)
    (chainEncodedLenSpec A)

/-- `Chain::encoded_len [local#3]` satisfies `chainEncodedLenPinnedSpec A` on
`tripleRatchetProgAt`. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name)
    (chainEncodedLenPinnedSpec A)

/-- `Chain::encoded_len [local#3]` satisfies `chainEncodedLenSpec A` on
`tripleRatchetProgAt`. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name)
    (chainEncodedLenSpec A)

/-- Entry-address pair predicate for the two CLI copies of `Chain::encoded_len` (`[local#3]` and
`[local#2]`) and their corresponding `Epoch::encoded_len` callees. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry epochEntry : BitVec 64) : Prop :=
  ((tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name = entry ∧
    (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLenLocal1Name = epochEntry) ∨
  ((tripleRatchetProgAtExt b abs).fnAddr chainEncodedLenLocal2Name = entry ∧
    (tripleRatchetProgAtExt b abs).fnAddr epochEncodedLenLocal2Name = epochEntry)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncLen_fetch_entry {b : BitVec 64} {abs : String → Option (State → State)}
    {entry epochEntry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr chainEncodedLenLocal2Name) = some ins) :
    (tripleRatchetProgAtExt b abs).fetch entry = some ins := by
  rcases hfn with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact h1
  · exact h2

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncLen_fetch_add {b : BitVec 64} {abs : String → Option (State → State)}
    {entry epochEntry : BitVec 64} (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr chainEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b abs).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact h1
  · exact h2

open Lean Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` (byte offsets from function entry `entry`) when
    `hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry` and `[kStart, kEnd)` avoids `+0x07c` (`124`). -/
elab "chain_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off1 := (num% (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]"))
  let off2 := 0x63398
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]").decl
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63398
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
      s!"spqrChainEncLenBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}"))
    let dec2 := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
      s!"spqrChainEncLenBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncLen_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncLen_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

/-! ## Field Layout Decomposition for `chainPBPinnedAt` -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_prologue_dir (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) (ch : ChainPB)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chainUnpacked A g a ch ∗
      chainStackFrame sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ch.currentEpoch == 0#64 then entry + 388#64 else entry + 72#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 (i32VarintFieldEncodedLen ch.direction) →
      sm.readReg64 .x8 = ch.currentEpoch →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((chainUnpacked A g a ch ∗ chainSavedFrame sp s v56) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 72
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 376 388
  subst hP
  dsimp only [chainUnpacked, chainStackFrame, chainSavedFrame]
  by_cases hdir : ch.direction = 0#32
  · cases hce : (ch.currentEpoch == 0#64) with
    | true =>
      have hce_bne : (ch.currentEpoch != 0#64) = false := by simp [bne, hce]
      apply SepWPp.of_sepWP (mid := if ch.currentEpoch == 0#64 then entry + 388#64 else entry + 72#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [i32VarintFieldEncodedLen]) (by simp_all)
        (by simp_all [ChainHighCalleeSaved])
    | false =>
      have hce_bne : (ch.currentEpoch != 0#64) = true := by simp [bne, hce]
      apply SepWPp.of_sepWP (mid := if ch.currentEpoch == 0#64 then entry + 388#64 else entry + 72#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [i32VarintFieldEncodedLen]) (by simp_all)
        (by simp_all [ChainHighCalleeSaved])
  · have hdir_beq : (ch.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have henc := bv_i32VarintField_nonzero hdir
    apply SepWPp.of_sepWP (mid := if ch.currentEpoch == 0#64 then entry + 388#64 else entry + 72#64)
    wp_steps
    apply SepWP.done (by cases (ch.currentEpoch == 0#64) <;> simp_all) (by simp_all)
    exact hnext _ (by cases (ch.currentEpoch == 0#64) <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [ChainHighCalleeSaved])

/-! ## Step 1B: `current_epoch` + load `links.len` (`+0x048..+0x068` and `+0x184..+0x18c`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_current_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB)
    (hb : ChainBounds g ch)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if ch.currentEpoch == 0#64 then entry + 388#64 else entry + 72#64))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (i32VarintFieldEncodedLen ch.direction))
    (hx8 : s.readReg64 .x8 = ch.currentEpoch)
    (hP : P = chainUnpacked A g a ch ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ch.links.isEmpty then entry + 400#64 else entry + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 (i32VarintFieldEncodedLen ch.direction) →
      sm.readReg64 .x22 = BitVec.ofNat 64 (u64VarintFieldEncodedLen ch.currentEpoch) →
      sm.readReg64 .x23 = BitVec.ofNat 64 ch.links.length →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 72 108
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 388 400
  obtain ⟨_, _, _, hlinks_beq, hlinks_bne, _, _⟩ := hb
  subst hP
  dsimp only [chainUnpacked]
  by_cases hce : ch.currentEpoch = 0#64
  · simp only [hce, beq_self_eq_true, ↓reduceIte] at hpc
    cases hle : ch.links.isEmpty with
    | true =>
      apply SepWPp.of_sepWP (mid := if ch.links.isEmpty then entry + 400#64 else entry + 108#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
        (by simp_all) (by simp_all [ChainHighCalleeSaved])
    | false =>
      apply SepWPp.of_sepWP (mid := if ch.links.isEmpty then entry + 400#64 else entry + 108#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
        (by simp_all) (by simp_all [ChainHighCalleeSaved])
  · have hce_beq : (ch.currentEpoch == 0#64) = false := beq_eq_false_iff_ne.mpr hce
    simp only [hce_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := chain_bv_u64VarintField_nonzero hce
    apply SepWPp.of_sepWP (mid := if ch.links.isEmpty then entry + 400#64 else entry + 108#64)
    wp_steps
    apply SepWP.done (by cases ch.links.isEmpty <;> simp_all) (by simp_all)
    exact hnext _ (by cases ch.links.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [ChainHighCalleeSaved])

/-! ## Step 2: `links: Vec<Epoch>` (`+0x06c..+0x0b4` and `+0x190..+0x194`) -/

/-- `ch.links = []`: `+0x190..+0x194` (`400..408`) jumps to `entry + 184#64` (`+0x0b8`) with `x8 = 0#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_empty (b : BitVec 64)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (ch : ChainPB) (hlinks : ch.links = [])
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 400#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 ch.links.length)
    (hnext : ∀ sm : State,
      sm.pc = entry + 184#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x8 = BitVec.ofNat 64 (chainLinksFieldEncodedLen ch.links) →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 400 408
  rw [hlinks, List.length_nil] at hx23
  apply SepWPp.of_sepWP (mid := entry + 184#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all)
    (by simp_all [chainLinksFieldEncodedLen, chainLinksBodiesEncodedLen])
    (by simp_all [ChainHighCalleeSaved])

/-- Loop setup (`+0x06c..+0x074`, `108..120`): loads `x20 = g.links.ptr`, sets `x24 = 0`, `x25 = x23`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_init (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 108#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = a)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 ch.links.length)
    (hP : P = chainUnpacked A g a ch ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 120#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = g.links.ptr →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = BitVec.ofNat 64 ch.links.length →
      sm.readReg64 .x24 = 0#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 ch.links.length →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 108 120
  subst hP
  dsimp only [chainUnpacked]
  apply SepWPp.of_sepWP (mid := entry + 120#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all)
    (by simp_all [ChainHighCalleeSaved])

/-- Step `+0x078..+0x07c` (`mov x0, x20; bl epochEntry`) and invoke `epochEncodedLenSpec A`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_epoch_call (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (hepoch : subroutine_ok (tripleRatchetProgAtExt b abs) epochEntry (epochEncodedLenSpec A))
    (ptr : BitVec 64) (ep : ChainEpochPB) (hfit : EpochEncodedLenFits ep)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 120#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ptr)
    (hP : P = (chainEpochPBAt A ptr ep ∗ stackAt s.sp epochEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 128#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  have hstep_bl : SepWP (tripleRatchetProgAtExt b abs) epochEntry s P
      (fun s1 P1 => s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = ptr ∧
        s1.readReg64 .lr = entry + 128#64 ∧
        CalleeSavedPreserved s s1 ∧ P1 = P) := by
    clear hepoch hnext hP hfit
    rcases hfn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨ht1, ht2, ht3, ht4⟩ := CryptoVerification.Cli.SpqrV1.ProtoRepr.bl_target_of_local1 h1 h2
      have hf120 := libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 120)
        (ls_lemma% fnOff "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") (by decide) (ls_decode% spqrChainEncLenBinCli (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 120))
      have hf124 := libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 124)
        (ls_lemma% fnOff "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]") (by decide) (ls_decode% spqrChainEncLenBinCli (ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" + 124))
      rw [show (libsignalSessionCode.rebase b (Rust.withPanics abs)).fnAddr
          CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name = entry from h1] at hf120 hf124
      clear h1 h2
      wp_steps
      apply SepWP.done (by simp_all [arm64_norm]) (by simp_all)
      refine ⟨by simp_all, by simp_all, by simp_all, by simp_all, by chainEncLen_cc_close, rfl⟩
    · obtain ⟨ht1, ht2, ht3, ht4⟩ := bl_target_of_local2 h1 h2
      have hf120 := libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 120)
        libsignalSessionCode_fnOff_0x63398 (by decide) spqrChainEncLenBin_decode_0x63410
      have hf124 := libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 124)
        libsignalSessionCode_fnOff_0x63398 (by decide) spqrChainEncLenBin_decode_0x63414
      rw [show (libsignalSessionCode.rebase b (Rust.withPanics abs)).fnAddr
          chainEncodedLenLocal2Name = entry from h1] at hf120 hf124
      clear h1 h2
      wp_steps
      apply SepWP.done (by simp_all [arm64_norm]) (by simp_all)
      refine ⟨by simp_all, by simp_all, by simp_all, by simp_all, by chainEncLen_cc_close, rfl⟩
  apply SepWPp.of_sepWP (mid := epochEntry)
  refine SepWP.mono hstep_bl ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, htr1, hx0_1, hlr1, hcs1, rfl⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1] at hsp_al ⊢; exact hsp_al
  refine call_frame_nopanic (x := ⟨ptr, ep⟩) (φ := s1.readReg64 .x0 = ptr ∧ EpochEncodedLenFits ep)
    (T := chainEpochPBAt A ptr ep ∗ stackAt s1.sp epochEncodedLenStack) (F := F)
    hepoch hpc1 hrun1 hsp1_al hlr1
    (by simp [epochEncodedLenSpec])
    ⟨hx0_1, hfit⟩
    (by rw [hsp1, hP])
    (by intro _; rfl)
    (by intro _ _; rfl)
    (by intro _; rfl)
    ?_
  intro sm hpcm hrunm hspm hcsm
  rw [show (epochEncodedLenSpec A).post ⟨ptr, ep⟩ s1 sm =
      ⌜sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) ∧ sm.trace = s1.trace⌝ ∗
        (chainEpochPBAt A ptr ep ∗ stackAt s1.sp epochEncodedLenStack) by
      simp [epochEncodedLenSpec]]
  rw [sepConj_assoc]
  apply SepWPp.pure_elim
  rintro ⟨hx0_m, htr_m⟩
  rw [hsp1, ← hP]
  exact hnext sm hpcm hrunm (hspm.trans hsp1) (htr_m.trans htr1) hx0_m (hcs1.trans hcsm)

/-- Induction over `rem : List ChainEpochPB` (`rem ≠ []`) for the `links` loop (`+0x078..+0x0b4`)
    to `entry + 184#64` (`+0x0b8`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_loop (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (hepoch : subroutine_ok (tripleRatchetProgAtExt b abs) epochEntry (epochEncodedLenSpec A))
    (rem : List ChainEpochPB) (hrem : rem ≠ [])
    (ptr : BitVec 64) (acc totalLen : Nat)
    (hrem_lt : rem.length < 2 ^ 64)
    (hepochs : ∀ ep ∈ rem, EpochEncodedLenFits ep)
    (hfit_loop : acc + chainLinksBodiesEncodedLen rem + totalLen < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 120#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ptr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalLen)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 acc)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rem.length)
    (hP : P = (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr rem ∗
      stackAt s.sp epochEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 184#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x8 = BitVec.ofNat 64 (acc + chainLinksBodiesEncodedLen rem + totalLen) →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  induction rem generalizing ptr acc s P F with
  | nil => contradiction
  | cons ep rest ih =>
    chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 128 184
    rw [chainLinksBodiesEncodedLen_cons] at hfit_loop
    have hep_fit : EpochEncodedLenFits ep := hepochs ep (List.mem_cons_self ..)
    have hbody_lt : chainEpochPBBodyEncodedLen ep < 2 ^ 64 := by omega
    have hacc_lt : acc + chainEpochPBBodyEncodedLen ep < 2 ^ 64 := by omega
    obtain ⟨hadd_body, hccb1, hccb2, hccb3, hccb4⟩ :=
      adds_no_overflow_of_eq (a := chainEpochPBEncodedLen ep)
        (b := varintLen (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)))
        (c := chainEpochPBBodyEncodedLen ep) rfl hbody_lt
    obtain ⟨hadd_acc, hcca1, hcca2, hcca3, hcca4⟩ :=
      adds_no_overflow_of_eq (a := chainEpochPBBodyEncodedLen ep)
        (b := acc) (c := acc + chainEpochPBBodyEncodedLen ep) rfl hacc_lt
    let FCall : SepProp :=
      arrayAt (fun e addr => chainEpochPBAt A addr e) 112 (ptr + 112#64) rest ∗ F
    have hP_call : P = (chainEpochPBAt A ptr ep ∗ stackAt s.sp epochEncodedLenStack) ∗ FCall := by
      rw [hP]
      dsimp only [arrayAt, FCall]
      ac_rfl
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_epoch_call (F := FCall) b A abs entry epochEntry hfn hepoch ptr ep hep_fit
      hpc hrun hsp_al hx20 hP_call ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1
    have hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
    have hx20_1 : s1.readReg64 .x20 = ptr := hcs1.2.1.trans hx20
    have hx21_1 : s1.readReg64 .x21 = s.readReg64 .x21 := hcs1.2.2.1
    have hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22 := hcs1.2.2.2.1
    have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 totalLen := hcs1.2.2.2.2.1.trans hx23
    have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 acc := hcs1.2.2.2.2.2.1.trans hx24
    have hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 (ep :: rest).length :=
      hcs1.2.2.2.2.2.2.1.trans hx25
    have hhigh1 : ChainHighCalleeSaved s s1 := ChainHighCalleeSaved.of_calleeSaved hcs1
    cases rest with
    | nil =>
      clear ih hepoch hP hP_call FCall hepochs
      simp only [List.length_singleton] at hx25_1
      have hrest0 : chainLinksBodiesEncodedLen [] = 0 := rfl
      rw [hrest0, Nat.add_zero] at hfit_loop
      obtain ⟨hadd_tot, hcct1, hcct2, hcct3, hcct4⟩ :=
        adds_no_overflow_of_eq (a := acc + chainEpochPBBodyEncodedLen ep)
          (b := totalLen)
          (c := acc + chainEpochPBBodyEncodedLen ep + totalLen)
          (Nat.add_comm totalLen _) hfit_loop
      apply SepWPp.of_sepWP (mid := entry + 184#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [chainLinksBodiesEncodedLen_cons])
        (hhigh1.trans (by simp_all [ChainHighCalleeSaved]))
    | cons ep2 rest' =>
      have hlen_ge : 2 ≤ (ep :: ep2 :: rest').length := by simp
      obtain ⟨hsub_ne0, hne1, hsub_eq⟩ := sub_one_beq_zero_false_of_two_le hlen_ge hrem_lt
      have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1] at hsp_al ⊢; exact hsp_al
      have hstep_tail : SepWP (tripleRatchetProgAtExt b abs) (entry + 120#64) s1 P
          (fun s2 P2 => s2.sp = s.sp ∧
            s2.trace = s.trace ∧ s2.readReg64 .x19 = s.readReg64 .x19 ∧
            s2.readReg64 .x20 = ptr + 112#64 ∧
            s2.readReg64 .x21 = s.readReg64 .x21 ∧
            s2.readReg64 .x22 = s.readReg64 .x22 ∧
            s2.readReg64 .x23 = BitVec.ofNat 64 totalLen ∧
            s2.readReg64 .x24 = BitVec.ofNat 64 (acc + chainEpochPBBodyEncodedLen ep) ∧
            s2.readReg64 .x25 = BitVec.ofNat 64 (ep2 :: rest').length ∧
            ChainHighCalleeSaved s s2 ∧ P2 = P) := by
        clear ih hepoch hnext hP hP_call FCall hepochs hcs1
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine ⟨by simp_all, by simp_all, by simp_all, by simp_all,
          by simp_all, by simp_all, by simp_all, by simp_all,
          by simp only [arm64_norm]; rfl,
          hhigh1.trans (by simp_all [ChainHighCalleeSaved]), rfl⟩
      apply SepWPp.of_sepWP (mid := entry + 120#64)
      refine SepWP.mono hstep_tail ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
        hx24_2, hx25_2, hhigh2, hP2⟩
      rw [hP2]
      have hsp2_al : s2.spAligned = true := by simp only [State.spAligned, hsp2] at hsp_al ⊢; exact hsp_al
      let FIH : SepProp := chainEpochPBAt A ptr ep ∗ F
      have hP_ih : P = (arrayAt (fun e addr => chainEpochPBAt A addr e) 112 (ptr + 112#64) (ep2 :: rest') ∗
          stackAt s2.sp epochEncodedLenStack) ∗ FIH := by
        rw [hP, hsp2]
        dsimp only [arrayAt, FIH]
        ac_rfl
      refine ih (F := FIH) (by simp) (ptr + 112#64) (acc + chainEpochPBBodyEncodedLen ep)
        (by simp only [List.length_cons] at hrem_lt ⊢; omega)
        (fun e he => hepochs e (List.mem_cons_of_mem ep he))
        (by omega)
        hpc2 hrun2 hsp2_al hx20_2 hx23_2 hx24_2 hx25_2 hP_ih ?_
      intro sm hpcm hrunm hspm htrm hx19_m hx21_m hx22_m hx8_m hhighm
      refine hnext sm hpcm hrunm (hspm.trans hsp2) (htrm.trans htr2)
        (hx19_m.trans hx19_2) (hx21_m.trans hx21_2) (hx22_m.trans hx22_2) ?_
        (hhigh2.trans hhighm)
      rw [hx8_m, chainLinksBodiesEncodedLen_cons ep (ep2 :: rest')]
      congr 1
      omega

end CryptoVerification.SpqrV1.ProtoRepr
