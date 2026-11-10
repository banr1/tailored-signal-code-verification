/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

/-!
# `<SignalMessage>::try_from` Loop Combinators, Invariants, and Shared Error Tails

Instruction-fetch macros, slice-cursor splitting lemmas, `SepWPp` combinators, loop register and
memory invariants, and shared `DecodeError::from` / `DecodeError::push` error-tail proofs for
`<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`).
-/

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `SignalMessage::try_from` (`0x25868`), from fn-relative offset `k0`,
    `len` bytes. -/
macro "tryFrom_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H
    (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) $k0 $len)

/-- Container holding all callee `subroutine_ok` hypotheses required by `try_from`. -/
structure TryFromDeps (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (Arm64.State → Arm64.State)) : Prop where
  intoBoxed : IntoBoxedSliceOk img C A ctl abs
  tryClone : TryCloneFromRefOk img C A ctl abs
  varintSlice : DecodeVarintSliceOkW img C A ctl abs
  int32Merge : Int32MergeOkW img C A ctl abs
  skipField : SkipFieldOkW img C A ctl abs
  dropDecodeError : DropDecodeErrorOkW img C A ctl abs
  bytesMerge : BytesMergeOkW img C A ctl abs
  dropSpe : DropSpeOkW img C A ctl abs

/-! ## Suffix and cursor-splitting lemmas for the protobuf codec -/

theorem decodeVarint_suffix {bs : List (BitVec 8)} {v : BitVec 64} {rest : List (BitVec 8)}
    (h : decodeVarint bs = some (v, rest)) :
    ∃ k, 1 ≤ k ∧ k ≤ bs.length ∧ rest = bs.drop k :=
  VarintBridge.decodeVarintAux_suffix bs 0 0 v rest h

theorem decodeKey_suffix {bs : List (BitVec 8)} {tag : ℕ} {wt : WireType} {rest : List (BitVec 8)}
    (h : decodeKey bs = some ((tag, wt), rest)) :
    ∃ k, 1 ≤ k ∧ k ≤ bs.length ∧ rest = bs.drop k ∧ tag < 2 ^ 32 ∧ 1 ≤ tag := by
  unfold decodeKey at h
  cases hd : decodeVarint bs with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨key, r⟩
    simp only [hd] at h
    split at h
    · simp at h
    · rename_i hkey
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none => simp [hwt] at h
      | some wt' =>
        simp only [hwt] at h
        split at h
        · simp at h
        · rename_i htag
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          obtain ⟨k, hk1, hkl, hr⟩ := decodeVarint_suffix hd
          exact ⟨k, hk1, hkl, hr, by omega, by omega⟩

theorem mergeUint32_suffix {wt : WireType} {bs : List (BitVec 8)} {v : BitVec 32}
    {rest : List (BitVec 8)} (h : mergeUint32 wt bs = some (v, rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold mergeUint32 at h
  split_ifs at h
  cases hd : decodeVarint bs with
  | none => simp [hd] at h
  | some p =>
    simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨k, _, hkl, hr⟩ := decodeVarint_suffix hd
    exact ⟨k, hkl, h.2.symm.trans hr⟩

theorem mergeBytes_suffix {wt : WireType} {bs : List (BitVec 8)} {v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k ∧ v.length ≤ bs.length := by
  unfold mergeBytes at h
  split_ifs at h
  cases hd : decodeVarint bs with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨len, r1⟩
    simp only [hd] at h
    split_ifs at h with hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨k1, _, hk1, hr1⟩ := decodeVarint_suffix hd
    have hr1_len : r1.length = bs.length - k1 := by simp [hr1]
    refine ⟨k1 + len.toNat, by omega, ?_, by simp; omega⟩
    rw [hr1, List.drop_drop]

theorem skipBytes_suffix {n : ℕ} {bs rest : List (BitVec 8)}
    (h : skipBytes n bs = some rest) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold skipBytes at h
  split_ifs at h with hlt
  simp only [Option.some.injEq] at h
  exact ⟨n, by omega, h.symm⟩

theorem skipScalar_suffix {wt : WireType} {bs rest : List (BitVec 8)}
    (h : skipScalar wt bs = some rest) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  cases wt <;> simp only [skipScalar] at h
  · simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨⟨v, r⟩, hd, rfl⟩
    obtain ⟨k, _, hkl, hr⟩ := decodeVarint_suffix hd
    exact ⟨k, hkl, hr⟩
  · exact skipBytes_suffix h
  · cases hd : decodeVarint bs with
    | none => simp [hd] at h
    | some p =>
      simp only [hd] at h
      obtain ⟨k1, _, hk1, hr1⟩ := decodeVarint_suffix hd
      obtain ⟨k2, hk2, hr2⟩ := skipBytes_suffix h
      have hr1_len : p.2.length = bs.length - k1 := by simp [hr1]
      exact ⟨k1 + k2, by omega, by rw [hr2, hr1, List.drop_drop]⟩
  · simp at h
  · simp at h
  · exact skipBytes_suffix h

theorem skipField_skipGroup_suffix :
    ∀ (fuel : ℕ),
      (∀ {depth tag : ℕ} {wt : WireType} {bs rest : List (BitVec 8)},
        skipField fuel depth tag wt bs = some rest →
        ∃ k, k ≤ bs.length ∧ rest = bs.drop k) ∧
      (∀ {depth tag : ℕ} {bs rest : List (BitVec 8)},
        skipGroup fuel depth tag bs = some rest →
        ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
  | 0 => ⟨fun h => by simp [skipField] at h, fun h => by simp [skipGroup] at h⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := skipField_skipGroup_suffix fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs rest h
      simp only [skipField] at h
      split_ifs at h
      cases wt <;> try exact skipScalar_suffix h
      · exact ihG h
      · simp at h
    · intro depth tag bs rest h
      simp only [skipGroup] at h
      cases hk : decodeKey bs with
      | none => simp [hk] at h
      | some p =>
        rcases p with ⟨⟨itag, iwt⟩, r1⟩
        simp only [hk] at h
        obtain ⟨k1, _, hk1, hr1, _, _⟩ := decodeKey_suffix hk
        have hr1_len : r1.length = bs.length - k1 := by simp [hr1]
        cases iwt <;> simp only at h
        · cases hs : skipField fuel (depth - 1) itag .varint r1 with
          | none => simp [hs] at h
          | some r2 =>
            simp only [hs] at h
            obtain ⟨k2, hk2, hr2⟩ := ihF hs
            obtain ⟨k3, hk3, hr3⟩ := ihG h
            have hr2_len : r2.length = r1.length - k2 := by simp [hr2]
            exact ⟨k1 + k2 + k3, by omega, by rw [hr3, hr2, hr1, List.drop_drop, List.drop_drop, Nat.add_assoc]⟩
        · cases hs : skipField fuel (depth - 1) itag .sixtyFourBit r1 with
          | none => simp [hs] at h
          | some r2 =>
            simp only [hs] at h
            obtain ⟨k2, hk2, hr2⟩ := ihF hs
            obtain ⟨k3, hk3, hr3⟩ := ihG h
            have hr2_len : r2.length = r1.length - k2 := by simp [hr2]
            exact ⟨k1 + k2 + k3, by omega, by rw [hr3, hr2, hr1, List.drop_drop, List.drop_drop, Nat.add_assoc]⟩
        · cases hs : skipField fuel (depth - 1) itag .lengthDelimited r1 with
          | none => simp [hs] at h
          | some r2 =>
            simp only [hs] at h
            obtain ⟨k2, hk2, hr2⟩ := ihF hs
            obtain ⟨k3, hk3, hr3⟩ := ihG h
            have hr2_len : r2.length = r1.length - k2 := by simp [hr2]
            exact ⟨k1 + k2 + k3, by omega, by rw [hr3, hr2, hr1, List.drop_drop, List.drop_drop, Nat.add_assoc]⟩
        · cases hs : skipField fuel (depth - 1) itag .startGroup r1 with
          | none => simp [hs] at h
          | some r2 =>
            simp only [hs] at h
            obtain ⟨k2, hk2, hr2⟩ := ihF hs
            obtain ⟨k3, hk3, hr3⟩ := ihG h
            have hr2_len : r2.length = r1.length - k2 := by simp [hr2]
            exact ⟨k1 + k2 + k3, by omega, by rw [hr3, hr2, hr1, List.drop_drop, List.drop_drop, Nat.add_assoc]⟩
        · split_ifs at h
          simp only [Option.some.injEq] at h
          exact ⟨k1, hk1, h.symm.trans hr1⟩
        · cases hs : skipField fuel (depth - 1) itag .thirtyTwoBit r1 with
          | none => simp [hs] at h
          | some r2 =>
            simp only [hs] at h
            obtain ⟨k2, hk2, hr2⟩ := ihF hs
            obtain ⟨k3, hk3, hr3⟩ := ihG h
            have hr2_len : r2.length = r1.length - k2 := by simp [hr2]
            exact ⟨k1 + k2 + k3, by omega, by rw [hr3, hr2, hr1, List.drop_drop, List.drop_drop, Nat.add_assoc]⟩

theorem skipField_suffix {fuel depth tag : ℕ} {wt : WireType} {bs rest : List (BitVec 8)}
    (h : skipField fuel depth tag wt bs = some rest) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k :=
  (skipField_skipGroup_suffix fuel).1 h

theorem mergeField_suffix {m m' : ProtoSignalMessage} {tag : ℕ} {wt : WireType}
    {bs rest : List (BitVec 8)} (h : mergeField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold mergeField at h
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag7 <;>
    simp only [Option.map_eq_some_iff] at h
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; exact mergeUint32_suffix hm
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; exact mergeUint32_suffix hm
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs

/-- Bridge from `sliceCursorAfter slot ptr bs rest` to `sliceCursorAt` at the advanced pointer,
framing the consumed prefix `bs.take (bs.length - rest.length)`. -/
theorem sliceCursorAfter_eq_take_cursorAt (slot ptr : BitVec 64) (bs rest : List (BitVec 8))
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) :
    sliceCursorAfter slot ptr bs rest =
      (ptr ↦ₛ bs.take (bs.length - rest.length)) ∗
        sliceCursorAt slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest := by
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  unfold sliceCursorAfter sliceCursorAt
  rw [hk]
  have hsplit : (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs]
    rw [pointsToBytes_append, List.length_take_of_le hkl]
  rw [hsplit]
  ac_nf

theorem decodeVarint_cons_of_le (b0 : BitVec 8) (bs : List (BitVec 8)) (hb0 : b0.toNat ≤ 0x7F) :
    decodeVarint (b0 :: bs) = some (b0.zeroExtend 64, bs) := by
  unfold decodeVarint decodeVarintAux
  have hb0' : b0 ≤ 0x7f#8 := by simpa [BitVec.le_def] using hb0
  simp [hb0]
  bv_kernel

theorem pointsToBytes_split_last (ptr : BitVec 64) (bs : List (BitVec 8)) (hne : bs ≠ []) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.dropLast) ∗
        ((ptr + BitVec.ofNat 64 (bs.length - 1)) ↦₈ bs.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [pointsToBytes_append, List.length_dropLast, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsToBytes_take_drop (ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ)
    (hk : k ≤ bs.length) :
    (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) = (ptr ↦ₛ bs) := by
  conv_rhs => rw [← List.take_append_drop k bs]
  rw [pointsToBytes_append, List.length_take_of_le hk]

/-! ## `SepWPp` combinators for `try_from` -/

/-- The panic postcondition of `tryFromSpec` in `SepWPp` form, polymorphic over the outer frame. -/
def tryFromQp (s0 : Arm64.State) : Arm64.State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem tryFromQp_of_call {s0 s sf : Arm64.State} {F : SepProp} (htr : s.trace = s0.trace) :
    tryFromQp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
  rw [allocFailedIn, htr] at ha
  rw [htr] at hp
  exact ⟨ha, hp⟩

theorem tryFromQp_of_noPanic {s0 sf : Arm64.State} {F : SepProp} :
    tryFromQp s0 sf (⌜False⌝ ∗ F) := by
  intro R hm
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

theorem tryFromQp_frame {s0 sf : Arm64.State} {P_f F : SepProp}
    (h : tryFromQp s0 sf P_f) :
    tryFromQp s0 sf (P_f ∗ F) := by
  intro R hm
  rw [sepConj_assoc] at hm
  have h1 := h (F ∗ R) hm
  rw [← sepConj_assoc] at h1
  exact allowPanic_frame id h1

/-- Typeclass witnessing that `calleeSavedVRegs s = calleeSavedVRegs s0` across straight-line
instruction steps. -/
class VRegsAt (s0 s : Arm64.State) : Prop where
  eq : calleeSavedVRegs s = calleeSavedVRegs s0

theorem calleeSavedVRegs_applyWriteback (s : Arm64.State) (wb : Option (Reg × BitVec 64)) :
    calleeSavedVRegs (ProofLib.applyWriteback s wb) = calleeSavedVRegs s := by
  cases wb with
  | none => rfl
  | some p => exact calleeSavedVRegs_writeReg64 s p.1 p.2

instance (s : Arm64.State) : VRegsAt s s := ⟨rfl⟩
instance (priority := 100) {s0 sm : Arm64.State} [hv : VRegsAt s0 sm] : VRegsAt s0.advancePC sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_advancePC s0).symm⟩
instance (priority := 100) {s0 sm : Arm64.State} (pc : BitVec 64) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setPC pc) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setPC s0 pc).symm⟩
instance (priority := 100) {s0 sm : Arm64.State} (m : Memory) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setMem m) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setMem s0 m).symm⟩
instance (priority := 100) {s0 sm : Arm64.State} (ps : PState) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setPState ps) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setPState s0 ps).symm⟩
instance (priority := 100) {s0 sm : Arm64.State} (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.writeReg64 r val) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_writeReg64 s0 r val).symm⟩
instance (priority := 100) {s0 sm : Arm64.State} (r : Reg) (val : BitVec 32) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.writeReg32 r val) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_writeReg32 s0 r val).symm⟩
instance {s0 s : Arm64.State} [hv : VRegsAt s0 s] : VRegsAt s0 s.advancePC :=
  ⟨(calleeSavedVRegs_advancePC s).trans hv.eq⟩
instance {s0 s : Arm64.State} (pc : BitVec 64) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setPC pc) :=
  ⟨(calleeSavedVRegs_setPC s pc).trans hv.eq⟩
instance {s0 s : Arm64.State} (m : Memory) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setMem m) :=
  ⟨(calleeSavedVRegs_setMem s m).trans hv.eq⟩
instance {s0 s : Arm64.State} (ps : PState) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setPState ps) :=
  ⟨(calleeSavedVRegs_setPState s ps).trans hv.eq⟩
instance {s0 s : Arm64.State} (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg64 r val) :=
  ⟨(calleeSavedVRegs_writeReg64 s r val).trans hv.eq⟩
instance {s0 s : Arm64.State} (r : Reg) (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg32 r val) :=
  ⟨(calleeSavedVRegs_writeReg32 s r val).trans hv.eq⟩
instance {s0 s : Arm64.State} (w : Width) (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg w r val) :=
  ⟨(calleeSavedVRegs_writeReg s w r val).trans hv.eq⟩
instance {s0 s : Arm64.State} (wb : Option (Reg × BitVec 64)) [hv : VRegsAt s0 s] :
    VRegsAt s0 (ProofLib.applyWriteback s wb) :=
  ⟨(calleeSavedVRegs_applyWriteback s wb).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 7#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 7#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : Arm64.State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 7#5 val rfl).trans hv.eq⟩

theorem SepWP.done {prog : Program} {target_pc : BitVec 64} {s0 s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop}
    [hv : VRegsAt s0 s]
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hpost : post s P) :
    ProofLib.SepWP prog target_pc s P (fun sf Pf => VRegsAt s0 sf ∧ post sf Pf) :=
  ProofLib.SepWP.done hpc hrun ⟨hv, hpost⟩

/-- Panic-aware weakest precondition that also threads `calleeSavedVRegs sf = calleeSavedVRegs s`
on the normal return branch. -/
def SepWPp (prog : Program) (ret : BitVec 64) (s : Arm64.State) (P : SepProp)
    (Q Qp : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ProofLib.SepWPp prog ret s P (fun sf Pf => Q sf Pf ∧ calleeSavedVRegs sf = calleeSavedVRegs s) Qp oom

theorem SepWPp.of_sepWP {prog : Program} {ret mid : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧ SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.of_sepWP_frozen {prog : Program} {ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    {mid : BitVec 64} {img : Obj.Image}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧
      (img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp oom)) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · have hfz_m := hsteps.frozenLoaded hfz
    have hsym_m := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext hfz_m hsym_m R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.panic {prog : Program} {ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPp prog ret s P Q Qp oom :=
  ProofLib.SepWPp.panic hrun hext hqp

/-- Frame an invariant `F` around a `SepWPp` computation with `tryFromQp s0`. -/
theorem SepWPp.frame_tryFrom {prog : Program} {ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Q Q' : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q' (tryFromQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨hpan, P_f, hmp, hqp⟩ | ⟨_, hoom⟩⟩ := h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · rw [← sepConj_assoc] at hmp
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmp, tryFromQp_frame hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Sequence two `SepWPp` segments via an intermediate PC `mid`. -/
theorem SepWPp.bind {prog : Program} {mid ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Qm Q Qp : Arm64.State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hvm⟩ | hpan⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      h2 sm Pm hpc hrun hqm R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hvm⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

/-- Call a panicking callee whose `onPanic` is `⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap`
and whose `onExit` is `⌜False⌝`, threading `img.FrozenLoaded`, `symtab`, and `spAligned`. -/
theorem SepWPp.call_tryFrom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by
      intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  refine ProofLib.SepWPp.call_wpp_frozen hcall hF hsym hpc hrun hsp hlr
    (x := x) (F := F)
    (fun R' hm => by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF, hsym⟩, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sm code _ _ hpost => by
      dsimp only [Spec.inImage] at hpost
      rw [hexit sm code] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ => by
      dsimp only [Spec.inImage]
      rw [hpan sm]
      exact tryFromQp_of_call htr)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm R' hpost hLm => ?_)
    (fun sm _ _ hoom => by
      dsimp only [Spec.inImage] at hoom
      rw [hoom_eq sm] at hoom
      exact (not_satisfies_false_sepConj hoom).elim)
  have hspm_align : sm.spAligned = true := by
    rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
  obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
    hnext sm hpcm hrunm hspm hspm_align hFm hsymm hcsm R' hpost hLm
  · exact ⟨sf, hsteps',
      Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
  · exact ⟨sf, hsteps', Or.inr hpanf⟩

/-- Run a `SepWP` segment that reaches `ret` directly, threading `img.FrozenLoaded` and `symtab`. -/
theorem SepWPp.of_sepWP_end {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s0 s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      VRegsAt s sf ∧
      (img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf Pf))) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hsteps.frozenLoaded hF) (hsteps.symtab_eq.trans hsym), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Sequence a `SepWPp` segment whose postcondition entails `Qm sm` with a continuation from `Qm sm`. -/
theorem SepWPp.bind_entails {prog : Program} {mid ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Qm : Arm64.State → SepProp} {φm : Arm64.State → Prop}
    {Q Qp : Arm64.State → SepProp → Prop}
    (h1 : SepWPp prog mid s P (fun sm Pm => φm sm ∧ (Pm ⊢ Qm sm)) Qp)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φm sm → SepWPp prog ret sm (Qm sm) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.bind h1 (fun sm Pm hpc hrun ⟨hφ, hent⟩ R hmm hL => ?_)
  exact h2 sm hpc hrun hφ R (Satisfies.mono (sepConj_mono_left hent) hmm) hL

/-- Extract a pure fact from the precondition of `SepWPp`. -/
theorem SepWPp.pure_pre {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {φ : Prop} {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

/-- Extract an existential witness from the precondition of `SepWPp`. -/
theorem SepWPp.exists_pre {α : Type} {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (h : ∀ x, SepWPp prog ret s (P x) Q Qp) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx hL

/-- Rewrite the precondition of `SepWPp` along a `SepEntails` implication `P ⊢ P'`. -/
theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P P' : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.weaken_pre hent h

/-! ## Loop register and memory invariants -/

/-- Callee-saved and frame-pointer registers invariant across the protobuf decode loop
(`+0x0d0..+0x3b0`). -/
structure LoopRegs (sp' x19 x20 x21 x23 : BitVec 64) (s : Arm64.State) : Prop where
  sp : s.sp = sp'
  x29 : s.readReg64 .x29 = sp' + 352#64
  x26 : s.readReg64 .x26 = 0x8000000000000002#64
  x25 : s.readReg64 .x25 = 1#64
  x23_eq : s.readReg64 .x23 = x23
  x22 : s.readReg64 .x22 = sp' + 176#64
  x21_eq : s.readReg64 .x21 = x21
  x20_eq : s.readReg64 .x20 = x20
  x19_eq : s.readReg64 .x19 = x19

theorem LoopRegs.of_calleeSaved {sp' x19 x20 x21 x23 : BitVec 64} {s sf : Arm64.State}
    (h : LoopRegs sp' x19 x20 x21 x23 s) (hsp : sf.sp = s.sp) (hcs : CalleeSavedPreserved s sf) :
    LoopRegs sp' x19 x20 x21 x23 sf where
  sp := hsp.trans h.sp
  x29 := (hcs.2.2.2.2.2.2.2.2.2.2.1).trans h.x29
  x26 := (hcs.2.2.2.2.2.2.2.1).trans h.x26
  x25 := (hcs.2.2.2.2.2.2.1).trans h.x25
  x23_eq := (hcs.2.2.2.2.1).trans h.x23_eq
  x22 := (hcs.2.2.2.1).trans h.x22
  x21_eq := (hcs.2.2.1).trans h.x21_eq
  x20_eq := (hcs.2.1).trans h.x20_eq
  x19_eq := hcs.1.trans h.x19_eq

/-- Memory state at the loop exit `+0x3b0` (`0x25c18`) for `res = decodeLoop fuel m bs`:
* `sp' + 160 .. 176`: `memRegion (sp' + 160#64) 16` (the cursor slot);
* `ptr ↦ₛ bs`: the full input slice passed to this loop suffix;
* `sp' + 288 .. 296`: `(sp' + 288#64) ↦₆₄ (sp' + 160#64)` (`bufRef`);
* `sp' + 296 .. 344`: `memRegion (sp' + 296#64) 48` (varint/error scratch);
* `stackAt sp' (skipFieldStack 100)`: callee stack budget below `sp'`;
* `sp' + 176 .. 288`: `wireSignalMessageOf A (sp' + 176#64) m'` on `some m'`, or
  `decodeErrorAt A x24 ∗ (∃∗ mErr, wireSignalMessageOf A (sp' + 176#64) mErr)` on `none`. -/
def loopExitMem (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (res : Option ProtoSignalMessage) : SepProp :=
  memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
    ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ memRegion (sp' + 296#64) 48 ∗
    A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
    match res with
    | some m' => ⌜x24 = 0#64⌝ ∗ wireSignalMessageOf A (sp' + 176#64) m'
    | none =>
      ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A x24 ∗
        (∃∗ mErr, wireSignalMessageOf A (sp' + 176#64) mErr)

/-- State predicate at `+0x3b0` (`0x25c18`). -/
def LoopExitState (img : Obj.Image) (s0 : Arm64.State)
    (sp' x19 x20 x21 x23 : BitVec 64) (sf : Arm64.State) : Prop :=
  LoopRegs sp' x19 x20 x21 x23 sf ∧
  sf.spAligned = true ∧
  img.FrozenLoaded sf ∧
  sf.symtab = img.symtab ∧
  sf.trace = s0.trace

/-- Full state + memory postcondition at `+0x3b0` (`0x25c18`). -/
def loopExitPost (img : Obj.Image) (A : RustAlloc) (s0 : Arm64.State)
    (sp' x19 x20 x21 x23 ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option ProtoSignalMessage) (sf : Arm64.State) (P : SepProp) : Prop :=
  LoopExitState img s0 sp' x19 x20 x21 x23 sf ∧
  (P ⊢ loopExitMem A sp' ptr bs (sf.readReg64 .x24) res)

theorem loopExitMem_append_prefix (A : RustAlloc) (sp' ptr : BitVec 64)
    (bs : List (BitVec 8)) (k : ℕ) (hk : k ≤ bs.length)
    (x24 : BitVec 64) (res : Option ProtoSignalMessage) :
    loopExitMem A sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) x24 res ∗ (ptr ↦ₛ bs.take k) =
      loopExitMem A sp' ptr bs x24 res := by
  unfold loopExitMem
  have hsplit := pointsToBytes_take_drop ptr bs k hk
  rw [← hsplit]
  ac_nf

theorem loopExitPost_append_prefix {img : Obj.Image} {A : RustAlloc} {s0 sf : Arm64.State}
    {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)} {k : ℕ} (hk : k ≤ bs.length)
    {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPost img A s0 sp' x19 x20 x21 x23 (ptr + BitVec.ofNat 64 k) (bs.drop k) res sf Pm) :
    loopExitPost img A s0 sp' x19 x20 x21 x23 ptr bs res sf (Pm ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  rw [← loopExitMem_append_prefix A sp' ptr bs k hk (sf.readReg64 .x24) res]
  exact sepConj_mono_left hent

/-! ## Stack and entailment helpers for loop steps -/

theorem stackAt_sub_split (sp : BitVec 64) (M N : ℕ)
    (hMN : (N - M) + M = N := by decide)
    (hle : N ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - M) ∗ stackAt sp M := by
  unfold stackAt
  refine memRegion_split' (n := N - M) (k := M) hMN.symm ?_ hle
  have hN : BitVec.ofNat 64 N = BitVec.ofNat 64 (N - M) + BitVec.ofNat 64 M := by
    rw [← BitVec.ofNat_add, hMN]
  rw [hN, BitVec.add_comm (BitVec.ofNat 64 (N - M)), ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem sepExists_intro {α : Type} (P : α → SepProp) (x : α) :
    P x ⊢ ∃∗ y, P y :=
  Entails.sepExists_intro x

theorem pointsTo64_pair_entails_memRegion16 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [memRegion_split' (n := 8) (k := 8) rfl rfl (by decide), memRegion_eight, memRegion_eight]
  exact sepConj_mono (sepExists_intro _ w0) (sepExists_intro _ w1)

theorem decodeErrorWith_entails_at (A : RustAlloc) (e : BitVec 64) (n : ℕ) :
    decodeErrorAtStackLen A e n ⊢ decodeErrorAt A e :=
  sepExists_intro _ n

theorem wireSignalMessageAt_entails_of (A : RustAlloc) (g : WireSignalMessageGhost)
    (a : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g a m ⊢ wireSignalMessageOf A a m :=
  sepExists_intro (fun g' => wireSignalMessageAt A g' a m) g

theorem wireSignalMessageOf_entails_exists_of (A : RustAlloc)
    (a : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageOf A a m ⊢ ∃∗ mErr, wireSignalMessageOf A a mErr :=
  sepExists_intro _ m

theorem wireSignalMessageAt_entails_exists_of (A : RustAlloc) (g : WireSignalMessageGhost)
    (a : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g a m ⊢ ∃∗ mErr, wireSignalMessageOf A a mErr :=
  Entails.trans (wireSignalMessageAt_entails_of A g a m)
    (wireSignalMessageOf_entails_exists_of A a m)

theorem pure_true_emp {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  rw [propext ⟨fun _ => trivial, fun _ => h⟩, Arm64.pure_true]

theorem loopExitMem_err_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n : ℕ) (mErr : ProtoSignalMessage) :
    memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ memRegion (sp' + 296#64) 48 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wireSignalMessageOf A (sp' + 176#64) mErr ⊢
      loopExitMem A sp' ptr bs x24 none := by
  unfold loopExitMem
  dsimp only
  rw [pure_true_emp hx24, emp_sepConj]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact sepConj_mono (decodeErrorWith_entails_at A x24 n)
    (wireSignalMessageOf_entails_exists_of A (sp' + 176#64) mErr)

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := h ▸ Entails.refl P

/-- Shared tail `+0x2bc..+0x2cc` (`0x25b24..0x25b34` → `+0x3b0`): stores `x8` at `sp' + 296`,
calls `DecodeError::from(sp' + 296)`, moves `x0` into `x24`, and jumps to `+0x3b0`. -/
theorem decodeErrorFrom_tail_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x2bc#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ w0) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A (sp' + 176#64) mErr)
      (loopExitPost img A s0 sp' x19 x20 x21 x23 ptr bs none)
      (tryFromQp s0) := by
  have hcall := decodeErrorFrom_ok_at_tripleRatchet hS (ctl := ctl)
    (name := tryFromName) (k := num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
  let H := Rust.withPanics abs
  tryFrom_fetches img.base H 700 20
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr tryFromName + 944#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr tryFromName + 700#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr tryFromName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr tryFromName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_tryFrom (sp' + 296#64, s.readReg64 (Reg.gpr 8#5)) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hF1 hsym1
    (ret_pc := entry + bv% (712)) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (sp' + 304#64) 40 ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)))
    (by simp_all [decodeErrorFromSpecWithStack, arm64_norm])
    hkind
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun ⟨hx0_ne, htr2⟩ => ?_)
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hF3, hsym3,
    by simp_all [arm64_norm]⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_ (loopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 mErr)
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl

theorem memRegion48_split8 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 48 =
      memRegion (sp' + 296#64) 8 ∗ memRegion (sp' + 304#64) 40 := by
  have hs := memRegion_split (sp' + 296#64) 8 40 (by decide)
  have ha : sp' + 296#64 + 8#64 = sp' + 304#64 := by bv_omega
  rw [ha] at hs
  exact hs

theorem pointsTo64_memRegion40_entails_memRegion48 (sp' v : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ v) ∗ memRegion (sp' + 304#64) 40 ⊢ memRegion (sp' + 296#64) 48 := by
  rw [memRegion48_split8 sp']
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 296#64) v)

/-- Shared tail `+0x3a8..+0x3ac` (`0x25c10..0x25c14` → `+0x3b0`): calls `DecodeError::push`,
loads `x24 := [sp' + 296] = err`, and falls through to `+0x3b0`. -/
theorem decodeErrorPush_tail_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr err : BitVec 64}
    {n : Nat}
    {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3a8#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 296#64)
    (herr : err ≠ 0#64)
    (hn : n < 2 ^ 32) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ err) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A err n ∗
        wireSignalMessageOf A (sp' + 176#64) mErr)
      (loopExitPost img A s0 sp' x19 x20 x21 x23 ptr bs none)
      (tryFromQp s0) := by
  have hcall := decodeErrorPush_ok_at_tripleRatchet hS (ctl := ctl)
    (name := tryFromName) (k := num% (ls_off% "<prost::error::DecodeError>::push" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
  let H := Rust.withPanics abs
  tryFrom_fetches img.base H 936 8
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr tryFromName + 944#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr tryFromName + 936#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr tryFromName + bv% (ls_off% "<prost::error::DecodeError>::push" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr tryFromName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "<prost::error::DecodeError>::push" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_tryFrom (sp' + 296#64, err, n) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hF1 hsym1
    (ret_pc := entry + bv% (940)) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp_all [decodeErrorPushExternSpecWithStack, arm64_norm])
    ⟨herr, hn⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre (fun herr' => ?_)
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hF3, hsym3,
    by simp_all [arm64_norm]⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 296#64) err')) ?_
  refine Entails.trans ?_ (loopExitMem_err_intro A sp' ptr bs err' herr' (n + 1) mErr)
  apply entails_of_eq
  simp only [hstack, hsp_eq, memRegion48_split8 sp', arm64_norm]
  ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Loop Combinators and Shared Error Tails (Block `85`) -/

structure TryFromDepsPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  intoBoxed : IntoBoxedSliceOkPlaced A H
  tryClone : TryCloneFromRefOkPlaced A H
  varintSlice : DecodeVarintSliceOkWPlaced A H
  int32Merge : Int32MergeOkWPlaced A H
  skipField : SkipFieldOkWPlaced A H
  dropDecodeError : DropDecodeErrorOkWPlaced A H
  bytesMerge : BytesMergeOkWPlaced A H
  dropSpe : DropSpeOkWPlaced A H

theorem SepWPp.of_sepWP_placed [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : Arm64.State} {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧ (LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom)) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.call_tryFrom_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf → SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [← sepConj_assoc, hpan sm] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, tryFromQp_of_call htr⟩)⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.of_sepWP_end_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → Q sf Pf))) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq (hcl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

def LoopExitStatePlaced [LibsignalPlacement] (s0 : Arm64.State)
    (sp' x19 x20 x21 x23 : BitVec 64) (sf : Arm64.State) : Prop :=
  LoopRegs sp' x19 x20 x21 x23 sf ∧ sf.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace

def loopExitPostPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : Arm64.State)
    (sp' x19 x20 x21 x23 ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option ProtoSignalMessage) (sf : Arm64.State) (P : SepProp) : Prop :=
  LoopExitStatePlaced s0 sp' x19 x20 x21 x23 sf ∧ (P ⊢ loopExitMem A sp' ptr bs (sf.readReg64 .x24) res)

theorem loopExitPostPlaced_append_prefix [LibsignalPlacement] {A : RustAlloc} {s0 sf : Arm64.State}
    {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)} {k : ℕ} (hk : k ≤ bs.length)
    {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPostPlaced A s0 sp' x19 x20 x21 x23 (ptr + BitVec.ofNat 64 k) (bs.drop k) res sf Pm) :
    loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res sf (Pm ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩; refine ⟨hst, ?_⟩
  rw [← loopExitMem_append_prefix A sp' ptr bs k hk (sf.readReg64 .x24) res]
  exact sepConj_mono_left hent

theorem decodeErrorFrom_tail_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H) {s0 s : State} {sp' x19 x20 x21 x23 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x2bc#64) (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ w0) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ wireSignalMessageOf A (sp' + 176#64) mErr)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs none) (tryFromQp s0) := by
  have hcall := hS.decodeErrorFrom
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeErrorFromName) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_tryFrom_placed (sp' + 296#64, s.readReg64 (Reg.gpr 8#5)) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hcl1
    (ret_pc := (blkPl_85).base + 712#64) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (sp' + 304#64) 40 ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)))
    (by simp_all [decodeErrorFromSpecWithStack, arm64_norm]) hkind (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]; rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun ⟨hx0_ne, htr2⟩ => ?_)
  refine SepWPp.of_sepWP_end_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hcl3, by simp_all [arm64_norm]⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_ (loopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 mErr)
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl

theorem decodeErrorPush_tail_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H) {s0 s : State} {sp' x19 x20 x21 x23 ptr err : BitVec 64}
    {n : Nat} {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x3a8#64) (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 296#64) (herr : err ≠ 0#64) (hn : n < 2 ^ 32) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ err) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A err n ∗
        wireSignalMessageOf A (sp' + 176#64) mErr)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs none) (tryFromQp s0) := by
  have hcall := hS.decodeErrorPush
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeErrorPushName) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_tryFrom_placed (sp' + 296#64, err, n) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hcl1
    (ret_pc := (blkPl_85).base + 940#64) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp_all [decodeErrorPushExternSpecWithStack, arm64_norm]) ⟨herr, hn⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]; rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre (fun herr' => ?_)
  refine SepWPp.of_sepWP_end_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hcl3, by simp_all [arm64_norm]⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 296#64) err')) ?_
  refine Entails.trans ?_ (loopExitMem_err_intro A sp' ptr bs err' herr' (n + 1) mErr)
  apply entails_of_eq; simp only [hstack, hsp_eq, memRegion48_split8 sp', arm64_norm]; ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Wire
