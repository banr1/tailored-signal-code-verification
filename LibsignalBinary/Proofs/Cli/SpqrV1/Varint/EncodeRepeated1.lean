/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommon
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# Verification of `prost::encoding::bytes::encode_repeated [local#3]`

Proves `encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` on the CLI image, parameterized over
bounded-stack `memcpy` and `elems.length < 2 ^ 59`.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  encodeVarint encodeBytesField encodeRepeatedBytes

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

open Lean Meta Elab Tactic in
local elab "encRepeated_fetches_range " b:term:max H:term:max sym:str
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offExpr ← elabTerm (← `((ls_off% $sym : Nat))) (some (mkConst ``Nat))
  let off ← whnfD offExpr
  let some off := off.rawNatLit? <|> off.nat?
    | throwError "encRepeated_fetches_range: could not reduce ls_off%"
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.Varint |>.str
      ("libsignalSessionBinCli_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k)))))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) (ls_lemma% fnOff $sym) (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) (ls_lemma% fnOff $sym) (by decide) $dec))

theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encodeVarint2_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
      BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
        "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]") =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name, CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2Name, h1, h2]
  bv_omega

theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.doReserve2_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
      BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]") =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name, CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name, h1, h2]
  bv_omega

private theorem sessionMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc sessionMemcpyRegionSpec) :
    subroutine_ok prog pc (withStack sessionMemcpyRegionSpec stk) :=
  subroutine_ok_refine_frame h
    (fun x R s0 hpre => ⟨x, stackAt s0.sp stk,
      by dsimp only [withStack, sessionMemcpyRegionSpec] at hpre ⊢; convert hpre using 1; ac_rfl,
      fun sf hpost => by dsimp only [withStack, sessionMemcpyRegionSpec] at hpost ⊢; convert hpost using 1; ac_rfl⟩)
    (fun _ _ _ _ hp => allowPanic_not_exited hp)
    (fun _ _ _ _ _ he => allowPanic_not_exited he)
    (fun _ _ _ _ _ _ ho => (allowPanic_not_exited ho).elim)

private theorem step_memcpy_call_cs {stackSz : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withEncRepeatedCS s0 (withStack sessionMemcpyRegionSpec stackSz)))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {x0 : EncodeRepeatedGhost} {R : SepProp} {ret : BitVec 64} {P F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt (sp - 80#64) stackSz) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt (sp - 80#64) stackSz) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F) hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withEncRepeatedCS, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs, ⟨hx0, hx1, hx2⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withEncRepeatedCS, withStack, sessionMemcpyRegionSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withEncRepeatedCS, withStack, sessionMemcpyRegionSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))

/-- Copy block (`56..84`) with stack-bounded `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_copy_cs {stackSz : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "memcpy"))
      (withEncRepeatedCS s0 (withStack sessionMemcpyRegionSpec stackSz)))
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8))
    (hle : bs2.length + elemBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hne : elemBs ≠ [])
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 elemBs.length)
    (hx22 : s.readReg64 .x22 = elemPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs2.length)
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase16)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs) ∗ stackAt (sp - 80#64) stackSz) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs) ∗
          stackAt (sp - 80#64) stackSz) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 56 84
  generalize_entry hentry :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name = entry
  examples_hide_fetches
  subst hP
  have hpos : 0 < elemBs.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_expose_slice A v cap ptr bs2 elemBs.length hle hcap hptr hpos]
  apply SepWPp.of_sepWP_cs (mid := entry + BitVec.ofNat 64 (ls_rel%
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
    "memcpy"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine step_memcpy_call_cs b A ext hmemcpy
    (ptr + BitVec.ofNat 64 bs2.length) elemPtr sp (entry + 76#64) elemBs
    (F := (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs2) ∗
      memRegion (ptr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 elemBs.length)
        (cap.toNat - bs2.length - elemBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro sm hpcm1 hrunm1 hspm1 htrm1 hcsm1 hcs_s0
  rcases hcsm1 with ⟨hx19m, hx20m, hx21m, _, hx23m, hx24m, hx25m, _⟩
  apply SepWPp.of_sepWP_cs (mid := entry + 84#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs_s0.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self])))
  rw [← vecU8At_pack_slice A v cap ptr bs2 elemBs hle hcap hptr hne]
  exact Entails.of_eq (by ac_rfl)

/-- Single element iteration (`96..184 → 84`) with stack-bounded `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_iter_cs {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "memcpy"))
      (withEncRepeatedCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (tag : Nat)
    (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8))
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hcopy_step := CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_copy_cs (stackSz := 48 + resStack) b A ext hmemcpy
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 96 188
  generalize_entry hentry :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name = entry
  examples_hide_fetches
  subst hP
  have hlen_ef := encodeBytesField_some_length tag elemBs
  have hkey_eq := encodeKey_lengthDelimited_eq tag
  have hkey_bounds := SpqrV1.Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + 2))
  have hlen_bounds := SpqrV1.Varint.encodeVarint_length_bounds (BitVec.ofNat 64 elemBs.length)
  have hfit1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62 := by
    rw [← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hb8 := base_add16_sub8 curBase
  have hb16 := base_add16_sub8_add8 curBase
  rw [repeatedBytesElemAt]
  apply SepWPp.of_sepWP_cs (mid := entry + BitVec.ofNat 64 (ls_rel%
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
    "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  refine step_encode_varint_call b A ext henc
    (BitVec.ofNat 64 (tag * 8 + 2)) v curCap curPtr sp (entry + 112#64) curBs hfit1
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcsm1 hcs1 hge1 hpres1
  rcases hcsm1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, hx25_1, _⟩
  have hfit2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
      (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat ∨
      (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length + 10 < 2 ^ 62 := by
    rw [List.length_append, ← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  apply SepWPp.of_sepWP_cs (mid := entry + BitVec.ofNat 64 (ls_rel%
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
    "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine step_encode_varint_call b A ext henc
    (BitVec.ofNat 64 elemBs.length) v cap1 ptr1 sp (entry + 124#64)
    (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))) hfit2
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcsm2 hcs2 hge2 hpres2
  rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, _⟩
  set bs2 := curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) ++
    encodeVarint (BitVec.ofNat 64 elemBs.length) with hbs2_def
  have hbs_final : bs2 ++ elemBs = curBs ++ encodeBytesField tag (some elemBs) := by
    simp only [hbs2_def, ← hkey_eq, encodeBytesField_some_eq, List.append_assoc]
  have hbs2_len : bs2.length + elemBs.length =
      curBs.length + (encodeBytesField tag (some elemBs)).length := by
    rw [← List.length_append, hbs_final, List.length_append]
  clear_value bs2
  clear hbs2_def
  rw [vecU8At_eq_header_rest A v cap2 ptr2 bs2]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hbs2_le, hcap2_lt, hptr2_ne⟩ => ?_
  have helem_lt : elemBs.length < 2 ^ 63 := by
    rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + elemBs.length
  · have hfit3 : bs2.length + elemBs.length < 2 ^ 62 := by
      rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = true :=
      (elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mpr hneed
    have hne : elemBs ≠ [] := by
      intro h; subst h; simp at hneed; omega
    obtain ⟨hnot_ult, hnew_ge, hnew_cap, hnew_bound⟩ := elem_len_after_reserve_not_ult hfit3 hneed
    apply SepWPp.of_sepWP_cs (mid := entry + BitVec.ofNat 64 (ls_rel%
      "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hx1_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_do_reserve2_call hres b A ext hdoReserve
      v cap2 ptr2 sp (entry + 168#64) bs2 elemBs.length hnew_bound
      (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
        (elemPtr ↦ₛ elemBs) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; ac_rfl) ?_
    intro s3 newPtr hpc3 hrun3 hsp3 htr3 hcsm3 hcs3
    rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, _, hx24_3, hx25_3, _⟩
    rw [vecU8At_eq_header_rest A v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hnew_le, hnew_lt63, hnew_ptr⟩ => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 56#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    refine hcopy_step v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr elemPtr sp
      (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
      hnew_ge hnew_lt63 hnew_ptr hne
      (F := A.pool ∗
        ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v
          (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2
          hnew_le hnew_lt63 hnew_ptr]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
    refine SepWPp.weaken_pre ?_
      (hnext s4 (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr
        hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
        (by omega) (fun h => absurd h (by omega)))
    rw [hbs_final, repeatedBytesElemAt]
    exact Entails.of_eq (by ac_rfl)
  · have hle2 : bs2.length + elemBs.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hneed ((elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mp h)
    have hpres_all : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap
      have h1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat := by
        rw [← hkey_eq]; omega
      obtain ⟨hc1, hp1⟩ := hpres1 h1
      have h2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
          (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat := by
        rw [hc1, List.length_append, ← hkey_eq]; omega
      obtain ⟨hc2, hp2⟩ := hpres2 h2
      exact ⟨hc2.trans hc1, hp2.trans hp1⟩
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    by_cases helem : elemBs = []
    · subst helem
      apply SepWPp.of_sepWP_cs (mid := entry + 84#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv3
      refine SepWPp.weaken_pre ?_
        (hnext _ cap2 ptr2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (hinv2.trans hinv3))
          (by omega) hpres_all)
      have hbs_nil : bs2 = curBs ++ encodeBytesField tag (some []) := by
        simpa using hbs_final
      rw [← hbs_nil, ← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne,
        repeatedBytesElemAt]
      exact Entails.of_eq (by ac_rfl)
    · have hcbnz : (BitVec.ofNat 64 elemBs.length == 0#64) = false :=
        len_beq_zero_false (List.length_pos_of_ne_nil helem) helem_lt
      apply SepWPp.of_sepWP_cs (mid := entry + 56#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv3
      refine hcopy_step v cap2 ptr2 elemPtr sp
        (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
        hle2 hcap2_lt hptr2_ne helem
        (F := A.pool ∗
          ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (hinv2.trans hinv3))
        (by rw [← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; ac_rfl) ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
      refine SepWPp.weaken_pre ?_
        (hnext s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
          (by omega) hpres_all)
      rw [hbs_final, repeatedBytesElemAt]
      exact Entails.of_eq (by ac_rfl)

/-- Copy block (`56..84`) with 0-stack `memcpy` (upstream API wrapper over `step_copy_cs`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_copy
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      sessionMemcpyRegionSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64) (bs2 elemBs : List (BitVec 8))
    (hle : bs2.length + elemBs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (hne : elemBs ≠ [])
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 elemBs.length)
    (hx22 : s.readReg64 .x22 = elemPtr) (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs2.length)
    (hx24 : s.readReg64 .x24 = remBytes) (hx25 : s.readReg64 .x25 = curBase16) (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal → sm.readReg64 .x24 = remBytes → sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm ((vecU8At A v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hstk0 : stackAt (sp - 80#64) 0 = emp := by
    unfold stackAt; simp [ProofLib.memRegion_zero]
  exact CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_copy_cs
    (stackSz := 0) (s0 := s0) (s := s) (x0 := x0) (R := R) (ret := ret) (P := P) (F := F) (Q := Q)
    b A ext
    (subroutine_ok_withEncRepeatedCS s0 (sessionMemcpy_to_withStack 0 hmemcpy))
    v cap ptr elemPtr sp keyVal remBytes curBase16 bs2 elemBs hle hcap hptr hne
    hpc hrun hsp halign htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    (by rw [hP, hstk0, sepConj_emp])
    (fun sm hpcm hrunm hspm htrm hx19m hx20m hx24m hx25m hcsm =>
      SepWPp.weaken_pre (Entails.of_eq (by rw [hstk0, sepConj_emp]))
        (hnext sm hpcm hrunm hspm htrm hx19m hx20m hx24m hx25m hcsm))

/-- Single element iteration (`96..184 → 84`) with 0-stack `memcpy` (upstream API wrapper over `step_iter_cs`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_iter {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      sessionMemcpyRegionSpec)
    (tag : Nat) (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64) (curBs elemBs : List (BitVec 8))
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes) (hx25 : s.readReg64 .x25 = curBase + 16#64) (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes → sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗ vecU8At A v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) :=
  CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_iter_cs
    (resStack := resStack) (s0 := s0) (s := s) (x0 := x0) (R := R) (ret := ret) (P := P) (F := F) (Q := Q)
    hres b A ext henc hdoReserve
    (subroutine_ok_withEncRepeatedCS s0 (sessionMemcpy_to_withStack (48 + resStack) hmemcpy))
    tag v curCap curPtr curBase elemPtr sp remBytes curBs elemBs hfit
    hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs hP hnext

/-- Latch block for the final element (`84..92 → 212`):
when `x24 = 24`, decrements `x24` by `24`, advances `x25` by `24`, and branches to `entry + 212#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_latch_zero (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (sp curBase : BitVec 64)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 84 96
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name = entry
  examples_hide_fetches
  have hbeq := latch_beq_zero_true
  apply SepWPp.of_sepWP_cs (mid := entry + 212#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))

/-- Latch block when `k > 0` elements remain (`84..92 → 96`) under `k + 1 < 2 ^ 59`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_latch_succ_1_59
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (v keyVal sp curBase : BitVec 64) (k : Nat) (_hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 96#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 84 96
  generalize_entry hentry :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name = entry
  examples_hide_fetches
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply SepWPp.of_sepWP_cs (mid := entry + 96#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))

/-- Loop over non-empty `elems` (`96 → 212`) with `elems.length < 2 ^ 59` and stack-bounded `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_loop_1_59_cs
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "memcpy"))
      (withEncRepeatedCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ [])
    (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  induction elems generalizing curBase curCap curPtr curBs s P F with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    rcases head with ⟨elemPtr, elemBs⟩
    subst hP
    simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit
    have hfit_head : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
        curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_iter_cs hres b A ext
      henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_latch_zero b A ext
        sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1))
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 59 := helem_cnt
      set tail := nextHead :: rest'
      refine CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_latch_succ_1_59 b A ext
        v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase tail.length hrest_pos helem_cnt'
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 ?_
      intro s1' hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
      have hfit_rest : (curBs ++ encodeBytesField tag (some elemBs)).length +
          (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat ∨
          (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length + 10 < 2 ^ 62 := by
        rw [List.length_append]
        rcases hfit with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      refine ih hrest_ne (by omega) (curBase + 24#64) cap1 ptr1
        (curBs ++ encodeBytesField tag (some elemBs)) hfit_rest
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗ F)
        hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
        (by ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 hge2 hpres2
      have hpres_all : curBs.length +
          (encodeRepeatedBytes tag (((elemPtr, elemBs) :: tail).map Prod.snd)).length ≤
          curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap
        simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit_cap
        obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
        have h2 : (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat := by
          rw [hc1, List.length_append]; omega
        obtain ⟨hc2, hp2⟩ := hpres2 h2
        exact ⟨hc2.trans hc1, hp2.trans hp1⟩
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 (by omega) hpres_all)
      clear_value tail
      rw [repeatedBytesSliceAt_cons, List.map_cons, encodeRepeatedBytes_cons, ← List.append_assoc]
      exact Entails.of_eq (by ac_rfl)

/-- Generalized `encode_repeated [local#3]` (`CLI` `[local#1]`) correctness with `< 2 ^ 59` elements
and stack-bounded `memcpy`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encode_repeated_1_59_gen_ok_ext_cs
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel%
          "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "memcpy"))
      (withEncRepeatedCS s0 (withStack sessionMemcpyRegionSpec (48 + resStack))))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59SpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeated59SpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.step_loop_1_59_cs
    hres b A ext henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59SpecOf resStack A).pre x s0, hpre, ?_⟩
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 0 56
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" 212 236
  generalize_entry hentry :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name = entry
  examples_hide_fetches
  dsimp only [encodeRepeated59SpecOf, encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩ => ?_
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit ⊢
  cases elems with
  | nil =>
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap.toNat ∧
        (bs.length +
            (encodeRepeatedBytes tag
              (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).length ≤ cap.toNat →
          cap = cap ∧ ptr = ptr)) = True :=
      eq_true ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨cap, ptr, by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    simpa only [List.map_nil, encodeRepeatedBytes_nil, List.append_nil, sepConj_assoc] using hPR
  | cons head rest =>
    have hne : head :: rest ≠ [] := List.cons_ne_nil _ _
    have hpos : 0 < (head :: rest).length := List.length_pos_of_ne_nil hne
    have hcbz : (BitVec.ofNat 64 (head :: rest).length == 0#64) = false :=
      len_beq_zero_false hpos (by omega)
    have hx24_setup := setup_x24_eq_59 helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => ?_
    refine SepWPp.exists_elim fun v1 => ?_
    refine SepWPp.exists_elim fun v2 => ?_
    refine SepWPp.exists_elim fun v3 => ?_
    refine SepWPp.exists_elim fun v4 => ?_
    refine SepWPp.exists_elim fun v5 => ?_
    refine SepWPp.exists_elim fun v6 => ?_
    refine SepWPp.exists_elim fun v7 => ?_
    refine SepWPp.exists_elim fun v8 => ?_
    refine SepWPp.exists_elim fun v9 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 96#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_pro
    have hx20_setup := setup_x20_eq htag2
    set savedCells : SepProp :=
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ v3) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
    have hpre_loop :
        repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (48 + resStack) ∗ savedCells =
        (repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (48 + resStack)) ∗ savedCells := by
      simp only [sepConj_assoc]
    clear_value savedCells
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    refine hloop tag v s0.sp (head :: rest) hne helem_cnt base cap ptr bs hfit
      (F := savedCells)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign64
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ((EncRepeatedCalleeSaved.refl s0).step (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv_pro)
      hpre_loop ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hcsm hge hpres
    rcases hcsm with ⟨hx26m, hx27m, hx28m, hvregsm, _⟩
    rw [hsaved_def]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap'.toNat ∧
        (bs.length + (encodeRepeatedBytes tag ((head :: rest).map Prod.snd)).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)) = True :=
      eq_true ⟨hge, hpres⟩
    simp only [satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 25#5), v3, s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 19#5), cap', ptr',
      by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    convert hPR using 1
    ac_rfl

/-- Generalized `encode_repeated [local#1]` correctness theorem parameterized by `resStack`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encode_repeated_1_gen_ok_ext
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      sessionMemcpyRegionSpec)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeatedSpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeatedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hpre59 : s0.mem ⊨ (encodeRepeated59SpecOf resStack A).pre x s0 ∗ R := by
    dsimp only [encodeRepeatedSpecOf, encodeRepeated59SpecOf] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩, hrest⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, htag1, htag2, by omega, hfit⟩, hrest⟩
  exact CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encode_repeated_1_59_gen_ok_ext_cs
    hres henc hdoReserve
    (subroutine_ok_withEncRepeatedCS s0 (sessionMemcpy_to_withStack (48 + resStack) hmemcpy))
    hpc hrun hpre59 halign

end EncodeRepeated1

/-- `prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]`
satisfies `encodeRepeatedSpec A` on `tripleRatchetProgAtExt b ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name)
      (encodeRepeatedSpec A) := by
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encodeVarint2_fnAddr_eq]
    exact CryptoVerification.Cli.SpqrV1.Varint.encode_varint2_fit_ok_ext hA
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      (doReserve2SpecOf doReserveStack A) := by
    rw [CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.doReserve2_fnAddr_eq]
    exact CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encode_repeated_1_gen_ok_ext (resStack := doReserveStack) (by decide)
    (subroutine_ok_withEncRepeatedCS s0 henc0)
    (subroutine_ok_withEncRepeatedCS s0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

/-- `prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]`
satisfies `encodeRepeatedSpec A` on `tripleRatchetProgAt b C ctl abs`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name)
      (encodeRepeatedSpec A) :=
  CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

/-- `prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]`
satisfies `(encodeRepeatedSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name)
      ((encodeRepeatedSpecX A).inImage img) := by
  have hdoReserve := CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext_x (img := img) hA
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encodeVarint2_fnAddr_eq]
    exact CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2_fit_ok_ext_x img A ext hdoReserve
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      ((doReserve2SpecOf doReserveStackX A).inImage img) := by
    rw [CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.doReserve2_fnAddr_eq]
    exact hdoReserve
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (encodeRepeatedSpecOf doReserveStackX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := CryptoVerification.Cli.SpqrV1.Varint.EncodeRepeated1.encode_repeated_1_gen_ok_ext (resStack := doReserveStackX) (by decide)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 henc0)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Varint
