/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommon
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::bytes::encode_repeated [local#1]`

Verifies the 59-instruction `encode_repeated::<Vec<u8>, Vec<u8>> [local#1]` routine against
`encodeRepeatedSpec` and `encodeRepeatedSpecX`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.externAt? Program.fnAddr
  encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

open Lean Meta Elab Tactic in
local elab "encRepeated_fetches_range " b:term:max H:term:max sym:str
    kStart:num kEnd:num : tactic => do
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
    let dec := mkIdent (`CryptoVerification.SpqrV1.Varint |>.str
      ("libsignalSessionBin_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k))))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) (ls_lemma% fnOff $sym) (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) (ls_lemma% fnOff $sym) (by decide) $dec))

theorem encodeVarint2_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
      BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
        "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]") =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarint2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeRepeated1Name, encodeVarint2Name, h1, h2]
  bv_omega

theorem doReserve2_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
      BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]") =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve2Name := by
  have h1 := (ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeRepeated1Name, doReserve2Name, h1, h2]
  bv_omega

set_option hygiene false in
local macro "step_copy_body " entry:term:max mcMid:term:max ofCs:term:max csPred:term:max mcCall:term:max : tactic => `(tactic| (
  subst hP
  have hpos : 0 < elemBs.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_expose_slice A v cap ptr bs2 elemBs.length hle hcap hptr hpos]
  apply ($ofCs (mid := $mcMid))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine $mcCall A hmemcpy
    (ptr + BitVec.ofNat 64 bs2.length) elemPtr sp ($entry + 76#64) elemBs
    (F := (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs2) ∗
      memRegion (ptr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 elemBs.length)
        (cap.toNat - bs2.length - elemBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro sm hpcm1 hrunm1 hspm1 htrm1 hcsm1 hcs_s0
  rcases hcsm1 with ⟨hx19m, hx20m, hx21m, _, hx23m, hx24m, hx25m, _⟩
  apply ($ofCs (mid := $entry + 84#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs_s0.trans (by simp only [$csPred:term, arm64_norm, *, and_self])))
  rw [← vecU8At_pack_slice A v cap ptr bs2 elemBs hle hcap hptr hne]
  exact Entails.of_eq (by ac_rfl)))

/-- Copy block (`56..84`): copies `elemBs` (`elemBs ≠ []`) from `elemPtr`
to `ptr + bs2.length` via `memcpy` and updates `[v + 16]` to `bs2.length + elemBs.length`. -/
theorem step_copy (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8))
    (hle : bs2.length + elemBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hne : elemBs ≠ [])
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 56#64)
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
    (hP : P = (vecU8At A v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 56 84
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name = entry_addr
  examples_hide_fetches
  step_copy_body entry_addr
    (entry_addr + BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
    SepWPp.of_sepWP_cs EncRepeatedCalleeSaved step_memcpy_call_gen

theorem step_copy_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8))
    (hle : bs2.length + elemBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hne : elemBs ≠ [])
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 56#64)
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
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_145).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_145 H) ret sm
        ((vecU8At A v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  step_copy_body ((blkPl_145).base) (lsρ spqrMemcpySym)
    SepWPp.of_sepWP_cs_placed EncRepeatedCalleeSavedPlaced step_memcpy_call_gen_placed

set_option hygiene false in
local macro "step_iter_body " entry:term:max encMid:term:max resMid:term:max ofCs:term:max csPred:term:max encCall:term:max resCall:term:max : tactic => `(tactic| (
  subst hP
  have hlen_ef := encodeBytesField_some_length tag elemBs
  have hkey_eq := encodeKey_lengthDelimited_eq tag
  have hkey_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + 2))
  have hlen_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 elemBs.length)
  have hfit1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62 := by
    rw [← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hb8 := base_add16_sub8 curBase
  have hb16 := base_add16_sub8_add8 curBase
  rw [repeatedBytesElemAt]
  apply ($ofCs (mid := $encMid))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  refine $encCall A henc
    (BitVec.ofNat 64 (tag * 8 + 2)) v curCap curPtr sp ($entry + 112#64) curBs hfit1
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
  apply ($ofCs (mid := $encMid))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine $encCall A henc
    (BitVec.ofNat 64 elemBs.length) v cap1 ptr1 sp ($entry + 124#64)
    (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))) hfit2
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    apply ($ofCs (mid := $resMid))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hx1_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine $resCall hres A hdoReserve
      v cap2 ptr2 sp ($entry + 168#64) bs2 elemBs.length hnew_bound
      (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
        (elemPtr ↦ₛ elemBs) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; ac_rfl) ?_
    intro s3 newPtr hpc3 hrun3 hsp3 htr3 hcsm3 hcs3
    rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, _, hx24_3, hx25_3, _⟩
    rw [vecU8At_eq_header_rest A v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hnew_le, hnew_lt63, hnew_ptr⟩ => ?_
    apply ($ofCs (mid := $entry + 56#64))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    refine hcopy_step v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr elemPtr sp
      (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
      hnew_ge hnew_lt63 hnew_ptr hne
      (F := A.pool ∗ stackAt (sp - 80#64) (48 + resStack) ∗
        ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2 hnew_le hnew_lt63 hnew_ptr]; ac_rfl) ?_
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
    apply ($ofCs (mid := $entry + 144#64))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    by_cases helem : elemBs = []
    · subst helem
      apply ($ofCs (mid := $entry + 84#64))
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
      apply ($ofCs (mid := $entry + 56#64))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv3
      refine hcopy_step v cap2 ptr2 elemPtr sp
        (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
        hle2 hcap2_lt hptr2_ne helem
        (F := A.pool ∗ stackAt (sp - 80#64) (48 + resStack) ∗
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
      exact Entails.of_eq (by ac_rfl)))

/-- Single element iteration (`96..184 → 84`):
encodes `encodeBytesField tag (some elemBs)` for the element `(elemPtr, elemBs)` at `curBase`
and stops at loop latch `entry + 84#64`. -/
theorem step_iter {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec)
    (tag : Nat)
    (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8))
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 96#64)
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
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 84#64 →
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
  have hcopy_step := step_copy b A ext hmemcpy
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 96 188
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name = entry_addr
  examples_hide_fetches
  step_iter_body entry_addr
    (entry_addr + BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
      "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
    (entry_addr + BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
    SepWPp.of_sepWP_cs EncRepeatedCalleeSaved step_encode_varint_call_gen step_do_reserve2_call_gen

theorem step_iter_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks)
    {s0 s : State}
    (henc : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat)
    (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8))
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_145).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_145 H) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hcopy_step := step_copy_placed A H hmemcpy
  step_iter_body ((blkPl_145).base) (lsmpl.base 148) (lsmpl.base 157)
    SepWPp.of_sepWP_cs_placed EncRepeatedCalleeSavedPlaced step_encode_varint_call_gen_placed step_do_reserve2_call_gen_placed

set_option hygiene false in
local macro "step_latch_zero_body " entry:term:max ofCs:term:max csPred:term:max : tactic => `(tactic| (
  have hbeq := latch_beq_zero_true
  apply ($ofCs (mid := $entry + 212#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))))

/-- Latch block for the final element (`84..92 → 212`):
when `x24 = 24`, decrements `x24` by `24`, advances `x25` by `24`, and branches to `entry + 212#64`. -/
theorem step_latch_zero (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (sp curBase : BitVec 64)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 84 96
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name = entry_addr
  examples_hide_fetches
  step_latch_zero_body entry_addr SepWPp.of_sepWP_cs EncRepeatedCalleeSaved

theorem step_latch_zero_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (sp curBase : BitVec 64)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_145).base + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_145 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  step_latch_zero_body ((blkPl_145).base) SepWPp.of_sepWP_cs_placed EncRepeatedCalleeSavedPlaced

set_option hygiene false in
local macro "step_latch_succ_body " entry:term:max ofCs:term:max csPred:term:max : tactic => `(tactic| (
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq k hlt
  have hx25_next := base_add16_add24 curBase
  apply ($ofCs (mid := $entry + 96#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))))

/-- Latch block when `k > 0` elements remain (`84..92 → 96`):
decrements `x24` by `24`, advances `x25` by `24`, and falls through to `entry + 96#64`. -/
theorem step_latch_succ (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 58)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 96#64 →
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
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 84 96
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name = entry_addr
  examples_hide_fetches
  step_latch_succ_body entry_addr SepWPp.of_sepWP_cs EncRepeatedCalleeSaved

theorem step_latch_succ_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 58)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_145).base + 96#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_145 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  step_latch_succ_body ((blkPl_145).base) SepWPp.of_sepWP_cs_placed EncRepeatedCalleeSavedPlaced

set_option hygiene false in
local macro "step_loop_body " iterStep:term:max latch0Step:term:max latchSStep:term:max : tactic => `(tactic| (
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
    refine $iterStep tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine $latch0Step sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1))
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 58 := helem_cnt
      set tail := nextHead :: rest'
      refine $latchSStep v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
        tail.length hrest_pos helem_cnt'
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
      exact Entails.of_eq (by ac_rfl)))

/-- Loop over non-empty `elems` (`96 → 212`):
encodes `encodeRepeatedBytes tag (elems.map Prod.snd)` and exits at epilogue `entry + 212#64`. -/
theorem step_loop {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ [])
    (helem_cnt : elems.length < 2 ^ 58)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 96#64)
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
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name + 212#64 →
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
  step_loop_body (step_iter hres b A ext henc hdoReserve hmemcpy) (step_latch_zero b A ext) (step_latch_succ b A ext)

theorem step_loop_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks)
    {s0 : State}
    (henc : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ [])
    (helem_cnt : elems.length < 2 ^ 58)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_145).base + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_145 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  step_loop_body (step_iter_placed hres A H henc hdoReserve hmemcpy) (step_latch_zero_placed A H) (step_latch_succ_placed A H)

set_option hygiene false in
local macro "encode_repeated_gen_body " entry:term:max ofCs:term:max csRefl:term:max : tactic => `(tactic| (
  dsimp only [encodeRepeatedSpecOf]
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
    have hx24_setup := setup_x24_eq helem_cnt
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
    apply ($ofCs (mid := $entry + 96#64))
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
      (($csRefl s0).step (by simp only [arm64_norm])
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
    ac_rfl))

theorem encode_repeated_1_gen_ok_ext {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name)
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
  have hloop := step_loop hres b A ext henc hdoReserve hmemcpy
  refine ⟨(encodeRepeatedSpecOf resStack A).pre x s0, hpre, ?_⟩
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 0 56
  encRepeated_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" 212 236
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name = entry_addr
  examples_hide_fetches
  encode_repeated_gen_body entry_addr SepWPp.of_sepWP_cs EncRepeatedCalleeSaved.refl

theorem encode_repeated_1_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (blkPl_145).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeatedSpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_145 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeatedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := step_loop_placed hres A H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeatedSpecOf resStack A).pre x s0, hpre, ?_⟩
  encode_repeated_gen_body ((blkPl_145).base) SepWPp.of_sepWP_cs_placed EncRepeatedCalleeSavedPlaced.refl

end EncodeRepeated1

theorem encode_repeated_1_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)))
    (hdoReserve0 : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_145 H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_145).rebase (blkPl_145).base H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpec A)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_145).rebase (blkPl_145).base H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecX A)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name)
      (encodeRepeatedSpec A) := by
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [EncodeRepeated1.encodeVarint2_fnAddr_eq]
    exact encode_varint2_fit_ok_ext hA
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (doReserve2SpecOf doReserveStack A) := by
    rw [EncodeRepeated1.doReserve2_fnAddr_eq]
    exact do_reserve2_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeRepeated1Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_gen_ok_ext (resStack := doReserveStack) (by decide)
    (subroutine_ok_withEncRepeatedCS s0 henc0)
    (subroutine_ok_withEncRepeatedCS s0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeRepeated1Name)
      (encodeRepeatedSpec A) :=
  encode_repeated_1_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem encode_repeated_1_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated1Name)
      ((encodeRepeatedSpecX A).inImage img) := by
  have hdoReserve := do_reserve2_ok_ext_x (img := img) hA
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [EncodeRepeated1.encodeVarint2_fnAddr_eq]
    exact encodeVarint2_fit_ok_ext_x img A ext hdoReserve
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      ((doReserve2SpecOf doReserveStackX A).inImage img) := by
    rw [EncodeRepeated1.doReserve2_fnAddr_eq]
    exact hdoReserve
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated1Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeRepeated1Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (encodeRepeatedSpecOf doReserveStackX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_gen_ok_ext (resStack := doReserveStackX) (by decide)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 henc0)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Varint
