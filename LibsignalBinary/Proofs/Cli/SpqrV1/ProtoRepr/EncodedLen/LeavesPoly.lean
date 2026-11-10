/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep
public meta import Lean -- shake: keep

/-!
# CLI `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len` Leaf Proofs

Proves `polyDec_entry_pinned_ok_ext` and `polyEnc_entry_pinned_ok_ext` for the CLI `ProtoRepr`
`PolynomialDecoder` and `PolynomialEncoder` `encoded_len` routines.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Shared Helpers for `repeated bytes` (`Vec<Vec<u8>>`) Loops -/

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr polynomialDecoderEncodedLenLocal2Name = entry

private theorem pair_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 entry : BitVec 64} (hfn : a1 = entry ∨ a2 = entry) {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl <;> assumption

private theorem pair_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 entry : BitVec 64} (hfn : a1 = entry ∨ a2 = entry) {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl <;> assumption

open Lean Elab Tactic in
elab "polyDec_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]")), 0x642fc]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x642fc
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrPolyDecBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
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

/-- Prologue + `pts_needed` (tag 1) + `polys` (tag 2) + load `pts.len`, branching to
    `entry + 220#64` (`+0x0dc`) when `pb.pts.isEmpty` or `entry + 88#64` (`+0x058`) otherwise. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_prefix (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry b abs entry)
    (g : PolynomialDecoderPBGhost) (a sp v16 v8 : BitVec 64) (pb : PolynomialDecoder)
    (hpts_beq : (BitVec.ofNat 64 pb.pts.length == 0#64) = pb.pts.isEmpty)
    (hpts_bne : (BitVec.ofNat 64 pb.pts.length != 0#64) = !pb.pts.isEmpty)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (polynomialDecoderUnpacked A g a pb ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if pb.pts.isEmpty then entry + 220#64 else entry + 88#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.ptsNeeded) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.polys) →
      sm.readReg64 .x10 = BitVec.ofNat 64 pb.pts.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((polynomialDecoderUnpacked A g a pb ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 88
  polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 196 220
  subst hP
  unfold polynomialDecoderUnpacked
  by_cases h1 : pb.ptsNeeded = 0#32
  · by_cases h2 : pb.polys = 0#32
    · apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 220#64 else entry + 88#64)
      wp_steps
      apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
      exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
        (by simp_all [u32VarintFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
    · have h2_beq : (pb.polys == 0#32) = false := beq_eq_false_iff_ne.mpr h2
      have h2_bne : (pb.polys != 0#32) = true := bne_iff_ne.mpr h2
      have henc2 := bv_u32VarintField_nonzero h2
      apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 220#64 else entry + 88#64)
      wp_steps
      apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
      exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
        (by simp_all) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
  · have h1_beq : (pb.ptsNeeded == 0#32) = false := beq_eq_false_iff_ne.mpr h1
    have h1_bne : (pb.ptsNeeded != 0#32) = true := bne_iff_ne.mpr h1
    have henc1 := bv_u32VarintField_nonzero h1
    by_cases h2 : pb.polys = 0#32
    · apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 220#64 else entry + 88#64)
      wp_steps
      apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
      exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [u32VarintFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
    · have h2_beq : (pb.polys == 0#32) = false := beq_eq_false_iff_ne.mpr h2
      have h2_bne : (pb.polys != 0#32) = true := bne_iff_ne.mpr h2
      have henc2 := bv_u32VarintField_nonzero h2
      apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 220#64 else entry + 88#64)
      wp_steps
      apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
      exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])

/-- Loop over `pts: Vec<Vec<u8>>` (`+0x068..+0x098` -> `+0x09c` = `entry + 156#64`) in
    `PolynomialDecoder::encoded_len`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_pts_loop (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry b abs entry)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (p : BitVec 64) (acc : Nat)
    (hacc : acc + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64)
    (hlen : (bs :: rest).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 104#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = p + 16#64)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 (bs :: rest).length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 acc)
    (hP : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 p (bs :: rest) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 156#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = s.readReg64 .x0 →
      sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = s.readReg64 .x9 →
      sm.readReg64 .x10 = s.readReg64 .x10 →
      sm.readReg64 .x14 = BitVec.ofNat 64 (acc + repeatedBytesBodiesEncodedLen (bs :: rest)) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  induction rest generalizing bs p acc s P F with
  | nil =>
    polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 104 156
    have hbody : repeatedBytesBodiesEncodedLen [bs] = bytesElemBodyEncodedLen bs := by
      rw [repeatedBytesBodiesEncodedLen_cons]
      simp [repeatedBytesBodiesEncodedLen]
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have hsub1 : BitVec.ofNat 64 ([bs] : List _).length - 1#64 = 0#64 :=
      ofNat_cons_length_sub_one bs []
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗ F := by
      rw [hP]; simp only [arrayAt, sepConj_emp, rustBytesVecAt_eq_len_sep_rest]
    rw [hP_unfold]
    apply SepWPp.of_sepWP (mid := entry + 156#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP_unfold]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by rw [hbody]; simp_all)
      (by simp_all [EpochEncLenCalleeSaved])
  | cons bs' rest' ih =>
    polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 104 156
    have hcons : repeatedBytesBodiesEncodedLen (bs :: bs' :: rest') =
        bytesElemBodyEncodedLen bs + repeatedBytesBodiesEncodedLen (bs' :: rest') :=
      repeatedBytesBodiesEncodedLen_cons bs (bs' :: rest')
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have ⟨hsub1, h_eq1, h_ne1, hbeq_z, hbne_z⟩ :=
      cons_cons_length_sub_one_flags bs bs' rest' hlen
    have hlen' : (bs' :: rest').length < 2 ^ 64 := by
      simp only [List.length_cons] at hlen ⊢; omega
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) := by
      rw [hP, arrayAt, rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    have hP_repack : (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) =
        arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗
          (rustBytesVecAt A p bs ∗ F) := by
      rw [rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    rw [hP_unfold]
    apply SepWPp.of_sepWP (mid := entry + 104#64)
    wp_step
    wp_steps
    apply SepWP.done (by clear ih; simp_all) (by clear ih; simp_all)
    refine ih bs' (p + 24#64) (acc + bytesElemBodyEncodedLen bs) (by omega) hlen'
      (F := rustBytesVecAt A p bs ∗ F)
      (by clear ih; simp_all) (by clear ih; simp_all) (by clear ih; simp_all [arm64_norm])
      (by clear ih; simp_all) (by clear ih; simp_all)
      hP_repack ?_
    clear ih
    intro sm hpcm hrunm hspm htrm hx0m hx8m hx9m hx10m hx14m hcsm
    rw [← hP_unfold]
    exact hnext sm hpcm hrunm (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by rw [hx14m, hcons, Nat.add_assoc])
      (EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcsm)

/-- Field 3 (`pts: Vec<Vec<u8>>`, tag 3) from `if pb.pts.isEmpty then entry + 220#64 else entry + 88#64`
    to `entry + 164#64` (`+0x0a4`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_pts (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry b abs entry)
    (g : PolynomialDecoderPBGhost) (a : BitVec 64) (pb : PolynomialDecoder)
    (hpts_lt : pb.pts.length < 2 ^ 63)
    (hcap_ne : ∀ bs rest, pb.pts = bs :: rest → g.pts.cap ≠ 0)
    (hfit : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if pb.pts.isEmpty then entry + 220#64 else entry + 88#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.ptsNeeded))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.polys))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pb.pts.length)
    (hP : P = polynomialDecoderUnpacked A g a pb ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 164#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.ptsNeeded) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.polys) →
      sm.readReg64 .x10 = BitVec.ofNat 64 (repeatedBytesFieldEncodedLen pb.pts) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  rcases hpts : pb.pts with _ | ⟨bs, rest⟩
  · polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 220 228
    simp only [hpts, List.isEmpty_nil, ↓reduceIte, List.length_nil] at hpc hx10
    apply SepWPp.of_sepWP (mid := entry + 164#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by rw [hpts]; simp_all [repeatedBytesFieldEncodedLen, repeatedBytesBodiesEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 88 104
    polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 156 164
    simp only [hpts, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hpc hx10
    have hcap := hcap_ne bs rest hpts
    have hlen64 : (bs :: rest).length < 2 ^ 64 := by rw [← hpts]; omega
    have hbody_lt : 0 + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialDecoderPBEncodedLen repeatedBytesFieldEncodedLen at hfit
      rw [hpts] at hfit; omega
    have hP_arr : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 g.pts.ptr (bs :: rest) ∗
        (((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: rest).length) ∗
          (⌜(bs :: rest).length ≤ g.pts.cap.toNat ∧ g.pts.cap.toNat * 24 < 2 ^ 63 ∧ g.pts.ptr ≠ 0⌝ ∗
            A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
            memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: rest).length * 24))
              ((g.pts.cap.toNat - (bs :: rest).length) * 24)) ∗
          ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗
          ((a + 28#64) ↦₃₂ pb.polys) ∗
          ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (a + 33#64) 7) ∗ F) := by
      rw [hP]
      unfold polynomialDecoderUnpacked
      simp only [hpts, vecVecU8Buf_eq_of_ne_zero hcap]
      ac_rfl
    rw [hP_arr]
    apply SepWPp.of_sepWP (mid := entry + 104#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_pts_loop b A abs entry hfn bs rest g.pts.ptr 0 hbody_lt hlen64
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) rfl ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx10_1 hx14_1 hcs1
    rw [Nat.zero_add] at hx14_1
    simp only [arm64_norm, hx0, hx8, hx9, hx10] at hx0_1 hx8_1 hx9_1 hx10_1 hsp1 htr1
    have hcs01 : EpochEncLenCalleeSaved s s1 :=
      EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcs1
    have hrep_lt : repeatedBytesFieldEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialDecoderPBEncodedLen at hfit
      rw [hpts] at hfit; omega
    have ⟨hadd_f3, hult_f3, hule_f3, _, _⟩ :=
      adds_no_overflow_of_eq
        (a := repeatedBytesBodiesEncodedLen (bs :: rest))
        (b := (bs :: rest).length)
        (c := repeatedBytesFieldEncodedLen (bs :: rest))
        (by unfold repeatedBytesFieldEncodedLen; omega) hrep_lt
    rw [← hP_arr]
    apply SepWPp.of_sepWP (mid := entry + 164#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by rw [hpts]; simp_all)
      (EpochEncLenCalleeSaved.trans hcs01 (by simp_all [EpochEncLenCalleeSaved]))

/-- Final sum + `is_complete` (tag 4, `bool`) + epilogue (`+0x0a4..+0x0c0: ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_finish (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry b abs entry)
    (g : PolynomialDecoderPBGhost) (a sp : BitVec 64) (pb : PolynomialDecoder)
    (hfit : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.ptsNeeded))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.polys))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (repeatedBytesFieldEncodedLen pb.pts))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (polynomialDecoderUnpacked A g a pb ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  polyDec_fetches_range_cli b (Rust.withPanics abs) entry hfn 164 196
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have h12 := bv_add_ofNat_comm (u32VarintFieldEncodedLen pb.ptsNeeded)
    (u32VarintFieldEncodedLen pb.polys)
  have ⟨h123, hult123, hule123, _, _⟩ :=
    adds_no_overflow_of_eq
      (a := repeatedBytesFieldEncodedLen pb.pts)
      (b := u32VarintFieldEncodedLen pb.ptsNeeded + u32VarintFieldEncodedLen pb.polys)
      (c := u32VarintFieldEncodedLen pb.ptsNeeded + u32VarintFieldEncodedLen pb.polys +
        repeatedBytesFieldEncodedLen pb.pts)
      (by omega) (by unfold polynomialDecoderPBEncodedLen at hfit; omega)
  have hbool1 := boolByte_zext64_shl_one pb.isComplete
  have hbool2 := boolByte_zext64_shl_one_nat pb.isComplete
  have hbool3 : ((boolByte pb.isComplete).zeroExtend 32).zeroExtend 64 <<< 1 =
      BitVec.ofNat 64 (boolFieldEncodedLen pb.isComplete) := by
    cases pb.isComplete <;> rfl
  have ⟨h1234, hult1234, hule1234, _, _⟩ :=
    adds_no_overflow_of_eq
      (a := u32VarintFieldEncodedLen pb.ptsNeeded + u32VarintFieldEncodedLen pb.polys +
        repeatedBytesFieldEncodedLen pb.pts)
      (b := boolFieldEncodedLen pb.isComplete)
      (c := polynomialDecoderPBEncodedLen pb)
      (by unfold polynomialDecoderPBEncodedLen; omega) hfit
  subst hP
  unfold polynomialDecoderUnpacked
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Any entry satisfying `CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry` satisfies `polynomialDecoderEncodedLenPinnedSpec`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.polyDec_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyDecEntry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (polynomialDecoderEncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, pb⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [polynomialDecoderEncodedLenPinnedSpec, polynomialDecoderPBPinnedAt_eq_unpacked,
    polyEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have ⟨hpts_lt, hpts_beq, hpts_bne, hcap_ne⟩ := polynomialDecoderUnpacked_pts_bounds hpre
  refine ⟨(polynomialDecoderUnpacked A g a pb ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_prefix (F := R) b A ext entry hfn g a s0.sp v16 v8 pb
    hpts_beq hpts_bne hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx10_1 hcs1
  have hP_mid : ((polynomialDecoderUnpacked A g a pb ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R) =
      polynomialDecoderUnpacked A g a pb ∗
        ((((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R) := by
    ac_rfl
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_pts b A ext entry hfn g a pb hpts_lt hcap_ne hfit
    hpc1 hrun1 hx0_1 hx8_1 hx9_1 hx10_1 hP_mid ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hx10_2 hcs2
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyDec_finish (F := R) b A ext entry hfn g a s0.sp pb hfit
    hpc2 hrun2 (by rw [hsp2, hsp1]) halign hx0_2 hx8_2 hx9_2 hx10_2
    (EpochEncLenCalleeSaved.trans hcs1 hcs2) rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [polynomialDecoderEncodedLenPinnedSpec, polynomialDecoderPBPinnedAt_eq_unpacked,
    polyEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
  convert hm_f using 1; ac_rfl

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.PolynomialDecoderEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenLocal1Name) (polynomialDecoderEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.PolynomialDecoderEncodedLenLocal1PinnedOkExt b A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polyDec_entry_pinned_ok_ext b A ext _ (Or.inl rfl)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr polynomialEncoderEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "polyEnc_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]")), 0x615f4]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x615f4
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrPolyEncBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
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

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_prefix (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b abs entry)
    (g : PolynomialEncoderPBGhost) (a sp v16 v8 : BitVec 64) (pb : PolynomialEncoder)
    (hpts_beq : (BitVec.ofNat 64 pb.pts.length == 0#64) = pb.pts.isEmpty)
    (hpts_bne : (BitVec.ofNat 64 pb.pts.length != 0#64) = !pb.pts.isEmpty)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (polynomialEncoderUnpacked A g a pb ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if pb.pts.isEmpty then entry + 144#64 else entry + 52#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.idx) →
      sm.readReg64 .x9 = BitVec.ofNat 64 pb.pts.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((polynomialEncoderUnpacked A g a pb ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 52
  polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 132 144
  subst hP; unfold polynomialEncoderUnpacked
  by_cases h1 : pb.idx = 0#32
  · apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 144#64 else entry + 52#64)
    wp_steps
    apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
    exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
      (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  · have h1_beq : (pb.idx == 0#32) = false := beq_eq_false_iff_ne.mpr h1
    have h1_bne : (pb.idx != 0#32) = true := bne_iff_ne.mpr h1
    have henc1 := bv_u32VarintField_nonzero h1
    apply SepWPp.of_sepWP (mid := if pb.pts.isEmpty then entry + 144#64 else entry + 52#64)
    wp_steps
    apply SepWP.done (by cases pb.pts <;> simp_all) (by simp_all)
    exact hnext _ (by cases pb.pts <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Loop 1 over `pts: Vec<Vec<u8>>` (`+0x044..+0x074` -> `+0x078` = `entry + 120#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_pts_loop (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b abs entry)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) (p : BitVec 64) (acc : Nat)
    (hacc : acc + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64)
    (hlen : (bs :: rest).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 68#64) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 = p + 16#64)
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (bs :: rest).length)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 acc)
    (hP : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 p (bs :: rest) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 120#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = s.readReg64 .x0 → sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = s.readReg64 .x9 →
      sm.readReg64 .x13 = BitVec.ofNat 64 (acc + repeatedBytesBodiesEncodedLen (bs :: rest)) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  induction rest generalizing bs p acc s P F with
  | nil =>
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 68 120
    have hbody : repeatedBytesBodiesEncodedLen [bs] = bytesElemBodyEncodedLen bs := by
      rw [repeatedBytesBodiesEncodedLen_cons]; simp [repeatedBytesBodiesEncodedLen]
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have hsub1 : BitVec.ofNat 64 ([bs] : List _).length - 1#64 = 0#64 :=
      ofNat_cons_length_sub_one bs []
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗ F := by
      rw [hP]; simp only [arrayAt, sepConj_emp, rustBytesVecAt_eq_len_sep_rest]
    rw [hP_unfold]; apply SepWPp.of_sepWP (mid := entry + 120#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP_unfold]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by rw [hbody]; simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | cons bs' rest' ih =>
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 68 120
    have hcons : repeatedBytesBodiesEncodedLen (bs :: bs' :: rest') =
        bytesElemBodyEncodedLen bs + repeatedBytesBodiesEncodedLen (bs' :: rest') :=
      repeatedBytesBodiesEncodedLen_cons bs (bs' :: rest')
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have ⟨hsub1, h_eq1, h_ne1, hbeq_z, hbne_z⟩ := cons_cons_length_sub_one_flags bs bs' rest' hlen
    have hlen' : (bs' :: rest').length < 2 ^ 64 := by simp only [List.length_cons] at hlen ⊢; omega
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) := by
      rw [hP, arrayAt, rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    have hP_repack : (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) =
        arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗
          (rustBytesVecAt A p bs ∗ F) := by
      rw [rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    rw [hP_unfold]; apply SepWPp.of_sepWP (mid := entry + 68#64)
    wp_step; wp_steps
    apply SepWP.done (by clear ih; simp_all) (by clear ih; simp_all)
    refine ih bs' (p + 24#64) (acc + bytesElemBodyEncodedLen bs) (by omega) hlen'
      (F := rustBytesVecAt A p bs ∗ F)
      (by clear ih; simp_all) (by clear ih; simp_all) (by clear ih; simp_all [arm64_norm])
      (by clear ih; simp_all) (by clear ih; simp_all) hP_repack ?_
    clear ih
    intro sm hpcm hrunm hspm htrm hx0m hx8m hx9m hx13m hcsm
    rw [← hP_unfold]
    exact hnext sm hpcm hrunm (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by rw [hx13m, hcons, Nat.add_assoc])
      (EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcsm)

/-- Loop 2 over `polys: Vec<Vec<u8>>` (`+0x0b8..+0x0e8` -> `+0x0ec` = `entry + 236#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_polys_loop (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b abs entry)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) (p : BitVec 64) (acc : Nat)
    (hacc : acc + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64)
    (hlen : (bs :: rest).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 184#64) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 = p + 16#64)
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (bs :: rest).length)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 acc)
    (hP : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 p (bs :: rest) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 236#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = s.readReg64 .x0 → sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = s.readReg64 .x9 →
      sm.readReg64 .x13 = BitVec.ofNat 64 (acc + repeatedBytesBodiesEncodedLen (bs :: rest)) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  induction rest generalizing bs p acc s P F with
  | nil =>
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 184 236
    have hbody : repeatedBytesBodiesEncodedLen [bs] = bytesElemBodyEncodedLen bs := by
      rw [repeatedBytesBodiesEncodedLen_cons]; simp [repeatedBytesBodiesEncodedLen]
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have hsub1 : BitVec.ofNat 64 ([bs] : List _).length - 1#64 = 0#64 :=
      ofNat_cons_length_sub_one bs []
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗ F := by
      rw [hP]; simp only [arrayAt, sepConj_emp, rustBytesVecAt_eq_len_sep_rest]
    rw [hP_unfold]; apply SepWPp.of_sepWP (mid := entry + 236#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP_unfold]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by rw [hbody]; simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | cons bs' rest' ih =>
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 184 236
    have hcons : repeatedBytesBodiesEncodedLen (bs :: bs' :: rest') =
        bytesElemBodyEncodedLen bs + repeatedBytesBodiesEncodedLen (bs' :: rest') :=
      repeatedBytesBodiesEncodedLen_cons bs (bs' :: rest')
    have hstep_lt : acc + bytesElemBodyEncodedLen bs < 2 ^ 64 := by omega
    have helem := bv_repeatedBytes_elem_step acc bs
    have ⟨hadd, hult, hule, _, _⟩ :=
      adds_no_overflow_of_eq (a := acc) (b := bytesElemBodyEncodedLen bs)
        (c := acc + bytesElemBodyEncodedLen bs) (by omega) hstep_lt
    have ⟨hsub1, h_eq1, h_ne1, hbeq_z, hbne_z⟩ := cons_cons_length_sub_one_flags bs bs' rest' hlen
    have hlen' : (bs' :: rest').length < 2 ^ 64 := by simp only [List.length_cons] at hlen ⊢; omega
    have hP_unfold : P = (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) := by
      rw [hP, arrayAt, rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    have hP_repack : (((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs) ∗
        (arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗ F) =
        arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 (p + 24#64) (bs' :: rest') ∗
          (rustBytesVecAt A p bs ∗ F) := by
      rw [rustBytesVecAt_eq_len_sep_rest]; ac_rfl
    rw [hP_unfold]; apply SepWPp.of_sepWP (mid := entry + 184#64)
    wp_step; wp_steps
    apply SepWP.done (by clear ih; simp_all) (by clear ih; simp_all)
    refine ih bs' (p + 24#64) (acc + bytesElemBodyEncodedLen bs) (by omega) hlen'
      (F := rustBytesVecAt A p bs ∗ F)
      (by clear ih; simp_all) (by clear ih; simp_all) (by clear ih; simp_all [arm64_norm])
      (by clear ih; simp_all) (by clear ih; simp_all) hP_repack ?_
    clear ih
    intro sm hpcm hrunm hspm htrm hx0m hx8m hx9m hx13m hcsm
    rw [← hP_unfold]
    exact hnext sm hpcm hrunm (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by rw [hx13m, hcons, Nat.add_assoc])
      (EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcsm)

/-- Field 2 (`pts: Vec<Vec<u8>>`, tag 2) from `if pb.pts.isEmpty then entry + 144#64 else entry + 52#64`
    to `entry + 152#64` (`+0x098`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_pts (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b abs entry)
    (g : PolynomialEncoderPBGhost) (a : BitVec 64) (pb : PolynomialEncoder)
    (hpts_lt : pb.pts.length < 2 ^ 63)
    (hcap_ne : ∀ bs rest, pb.pts = bs :: rest → g.pts.cap ≠ 0)
    (hfit : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if pb.pts.isEmpty then entry + 144#64 else entry + 52#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.idx))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 pb.pts.length)
    (hP : P = polynomialEncoderUnpacked A g a pb ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 152#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.idx) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (repeatedBytesFieldEncodedLen pb.pts) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  rcases hpts : pb.pts with _ | ⟨bs, rest⟩
  · polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 144 152
    simp only [hpts, List.isEmpty_nil, ↓reduceIte, List.length_nil] at hpc hx9
    apply SepWPp.of_sepWP (mid := entry + 152#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all)
      (by rw [hpts]; simp_all [repeatedBytesFieldEncodedLen, repeatedBytesBodiesEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 52 68
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 120 128
    simp only [hpts, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hpc hx9
    have hcap := hcap_ne bs rest hpts
    have hlen64 : (bs :: rest).length < 2 ^ 64 := by rw [← hpts]; omega
    have hbody_lt : 0 + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialEncoderPBEncodedLen repeatedBytesFieldEncodedLen at hfit; rw [hpts] at hfit; omega
    have hP_arr : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 g.pts.ptr (bs :: rest) ∗
        (((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: rest).length) ∗
          (⌜(bs :: rest).length ≤ g.pts.cap.toNat ∧ g.pts.cap.toNat * 24 < 2 ^ 63 ∧ g.pts.ptr ≠ 0⌝ ∗
            A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
            memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: rest).length * 24))
              ((g.pts.cap.toNat - (bs :: rest).length) * 24)) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          vecVecU8Buf A g.polys.cap g.polys.ptr pb.polys ∗
          ((a + 48#64) ↦₃₂ pb.idx) ∗ memRegion (a + 52#64) 4) ∗ F) := by
      rw [hP]; unfold polynomialEncoderUnpacked; simp only [hpts, vecVecU8Buf_eq_of_ne_zero hcap]; ac_rfl
    rw [hP_arr]; apply SepWPp.of_sepWP (mid := entry + 68#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_pts_loop b A abs entry hfn bs rest g.pts.ptr 0 hbody_lt hlen64
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) rfl ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx13_1 hcs1
    rw [Nat.zero_add] at hx13_1
    simp only [arm64_norm, hx0, hx8, hx9] at hx0_1 hx8_1 hx9_1 hsp1 htr1
    have hcs01 : EpochEncLenCalleeSaved s s1 :=
      EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcs1
    have hrep_lt : repeatedBytesFieldEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialEncoderPBEncodedLen at hfit; rw [hpts] at hfit; omega
    have ⟨hadd_f2, hult_f2, hule_f2, _, _⟩ :=
      adds_no_overflow_of_eq (a := repeatedBytesBodiesEncodedLen (bs :: rest)) (b := (bs :: rest).length)
        (c := repeatedBytesFieldEncodedLen (bs :: rest)) (by unfold repeatedBytesFieldEncodedLen; omega) hrep_lt
    rw [← hP_arr]; apply SepWPp.of_sepWP (mid := entry + 152#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by rw [hpts]; simp_all)
      (EpochEncLenCalleeSaved.trans hcs01 (by simp_all [EpochEncLenCalleeSaved]))

/-- Field 1+2 sum + Field 3 (`polys: Vec<Vec<u8>>`, tag 3) + epilogue (`+0x098..+0x108: ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_polys_and_ret (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b abs entry)
    (g : PolynomialEncoderPBGhost) (a sp : BitVec 64) (pb : PolynomialEncoder)
    (hpolys_lt : pb.polys.length < 2 ^ 63)
    (hpolys_beq : (BitVec.ofNat 64 pb.polys.length == 0#64) = pb.polys.isEmpty)
    (hpolys_bne : (BitVec.ofNat 64 pb.polys.length != 0#64) = !pb.polys.isEmpty)
    (hcap_ne : ∀ bs rest, pb.polys = bs :: rest → g.polys.cap ≠ 0)
    (hfit : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 152#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen pb.idx))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (repeatedBytesFieldEncodedLen pb.pts))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (polynomialEncoderUnpacked A g a pb ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  have ⟨h12, hult12, hule12, _, _⟩ :=
    adds_no_overflow_of_eq (a := repeatedBytesFieldEncodedLen pb.pts)
      (b := u32VarintFieldEncodedLen pb.idx)
      (c := u32VarintFieldEncodedLen pb.idx + repeatedBytesFieldEncodedLen pb.pts)
      (by omega) (by unfold polynomialEncoderPBEncodedLen at hfit; omega)
  rcases hpolys : pb.polys with _ | ⟨bs, rest⟩
  · polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 152 168
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 244 268
    rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
    have htot_nil : u32VarintFieldEncodedLen pb.idx + repeatedBytesFieldEncodedLen pb.pts =
        polynomialEncoderPBEncodedLen pb := by
      unfold polynomialEncoderPBEncodedLen
      simp [hpolys, repeatedBytesFieldEncodedLen, repeatedBytesBodiesEncodedLen]
    rw [htot_nil] at h12 hult12 hule12
    subst hP
    unfold polynomialEncoderUnpacked at hnext ⊢
    simp only [hpolys, List.length_nil, arm64_norm] at hnext ⊢
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  · polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 152 184
    polyEnc_fetches_range_cli b (Rust.withPanics abs) entry hfn 236 260
    simp only [hpolys, List.isEmpty_cons, Bool.not_false] at hpolys_beq hpolys_bne
    have hcap := hcap_ne bs rest hpolys
    have hlen64 : (bs :: rest).length < 2 ^ 64 := by rw [← hpolys]; omega
    have hbody_lt : 0 + repeatedBytesBodiesEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialEncoderPBEncodedLen repeatedBytesFieldEncodedLen at hfit; rw [hpolys] at hfit; omega
    have hP_arr : P = arrayAt (fun elem addr => rustBytesVecAt A addr elem) 24 g.polys.ptr (bs :: rest) ∗
        ((((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: rest).length) ∗
          (⌜(bs :: rest).length ≤ g.polys.cap.toNat ∧ g.polys.cap.toNat * 24 < 2 ^ 63 ∧ g.polys.ptr ≠ 0⌝ ∗
            A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
            memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: rest).length * 24))
              ((g.polys.cap.toNat - (bs :: rest).length) * 24)) ∗
          ((a + 48#64) ↦₃₂ pb.idx) ∗ memRegion (a + 52#64) 4) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F) := by
      rw [hP]; unfold polynomialEncoderUnpacked; simp only [hpolys, vecVecU8Buf_eq_of_ne_zero hcap]; ac_rfl
    rw [hP_arr]; apply SepWPp.of_sepWP (mid := entry + 184#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_polys_loop b A abs entry hfn bs rest g.polys.ptr 0 hbody_lt hlen64
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) rfl ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx13_1 hcs1
    rw [Nat.zero_add] at hx13_1
    simp only [arm64_norm, hx0, hsp] at hx0_1 hx8_1 hx9_1 hsp1 htr1
    have hcs01 : EpochEncLenCalleeSaved s0 s1 :=
      EpochEncLenCalleeSaved.trans hcs
        (EpochEncLenCalleeSaved.trans (by simp_all [EpochEncLenCalleeSaved]) hcs1)
    rcases hcs01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
    have hrep_lt : repeatedBytesFieldEncodedLen (bs :: rest) < 2 ^ 64 := by
      unfold polynomialEncoderPBEncodedLen at hfit; rw [hpolys] at hfit; omega
    have ⟨hadd_f3, hult_f3, hule_f3, _, _⟩ :=
      adds_no_overflow_of_eq (a := repeatedBytesBodiesEncodedLen (bs :: rest)) (b := (bs :: rest).length)
        (c := repeatedBytesFieldEncodedLen (bs :: rest)) (by unfold repeatedBytesFieldEncodedLen; omega) hrep_lt
    have ⟨h123, hult123, hule123, _, _⟩ :=
      adds_no_overflow_of_eq (a := repeatedBytesFieldEncodedLen (bs :: rest))
        (b := u32VarintFieldEncodedLen pb.idx + repeatedBytesFieldEncodedLen pb.pts)
        (c := polynomialEncoderPBEncodedLen pb)
        (by unfold polynomialEncoderPBEncodedLen; rw [hpolys]) hfit
    rw [← hP_arr]; subst hP; unfold polynomialEncoderUnpacked
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-- Any entry satisfying `CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry` satisfies `polynomialEncoderEncodedLenPinnedSpec`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.polyEnc_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsPolyEncEntry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (polynomialEncoderEncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, pb⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [polynomialEncoderEncodedLenPinnedSpec, polynomialEncoderPBPinnedAt_eq_unpacked,
    polyEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have ⟨hpts_lt, hpts_beq, hpts_bne, hcap_pts,
        hpolys_lt, hpolys_beq, hpolys_bne, hcap_polys⟩ :=
    polynomialEncoderUnpacked_bounds hpre
  refine ⟨(polynomialEncoderUnpacked A g a pb ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_prefix (F := R) b A ext entry hfn g a s0.sp v16 v8 pb
    hpts_beq hpts_bne hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
  have hP_mid : ((polynomialEncoderUnpacked A g a pb ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R) =
      polynomialEncoderUnpacked A g a pb ∗
        ((((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R) := by ac_rfl
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_pts b A ext entry hfn g a pb hpts_lt hcap_pts hfit
    hpc1 hrun1 hx0_1 hx8_1 hx9_1 hP_mid ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hcs2
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_polyEnc_polys_and_ret (F := R) b A ext entry hfn g a s0.sp pb
    hpolys_lt hpolys_beq hpolys_bne hcap_polys hfit
    hpc2 hrun2 (by rw [hsp2, hsp1]) halign hx0_2 hx8_2 hx9_2
    (EpochEncLenCalleeSaved.trans hcs1 hcs2) rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f; rw [sepConj_emp] at hm_f
  simp only [polynomialEncoderEncodedLenPinnedSpec, polynomialEncoderPBPinnedAt_eq_unpacked,
    polyEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
  convert hm_f using 1; ac_rfl

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.PolynomialEncoderEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenLocal1Name) (polynomialEncoderEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.PolynomialEncoderEncodedLenLocal1PinnedOkExt b A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polyEnc_entry_pinned_ok_ext b A ext _ (Or.inl rfl)

end CryptoVerification.SpqrV1.ProtoRepr
