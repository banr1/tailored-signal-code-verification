/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Phase 2 and Phase 3 Proofs for `prost::encoding::bytes::merge`

Payload-reservation arithmetic bounds, phase 2/3 symbolic execution lemmas, and `[LibsignalPlacement]`
extern adapters for `prost::encoding::bytes::merge`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge_fnOff
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

def L1_BytesMergeXPhase2 : Unit := ()

theorem fnAddr_offset_eq_HX {b : BitVec 64} {H : String → Option (State → State)}
    {name callee : String} {k : BitVec 64}
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff name) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee) := by fnoff_eq) :
    (libsignalSessionCode.rebase b H).fnAddr name + k =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hk]

/-- `mergeBytes` consumes at least one varint byte plus the payload. -/
theorem mergeBytes_length_sumX {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length 0 0 bs len rest0 hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

/-- With `bs.length < 2 ^ 62` the `reserve(len)` growth `max (len, 2 * cap, 8)` stays `< 2 ^ 63`
whenever `cap < len ≤ bs.length`. -/
theorem reserveCap_bound_of_lt62 {cap vLen bsLen : Nat} (hult : cap < vLen) (hv : vLen ≤ bsLen)
    (hbs : bsLen < 2 ^ 62) :
    reserveCap cap 0 vLen ≤ 9223372036854775807 := by
  dsimp [reserveCap]
  omega

private theorem mergePanicX_of_allocFailed {A : RustAlloc} {x : BytesMergeGhost}
    {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpecW A).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpecW, allocFailedIn] at hm ⊢
  rw [htr] at hm
  exact allowPanic_frame id hm

theorem sliceCursorAfter_advance_foldW (slot ptr : BitVec 64) (bs pfx rest0 : List (BitVec 8))
    (n : Nat) (hpfx : bs = pfx ++ rest0) (hle : n ≤ rest0.length) (hbs : bs.length < 2 ^ 63) :
    let v := rest0.take n
    let rest := rest0.drop n
    let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest0.length)
    ((slot ↦₆₄ (ptr1 + BitVec.ofNat 64 v.length)) ∗
      ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 rest0.length - BitVec.ofNat 64 v.length)) ∗
      (ptr ↦ₛ pfx) ∗ (ptr1 ↦ₛ v) ∗ ((ptr1 + BitVec.ofNat 64 v.length) ↦ₛ rest)) ⊢
      sliceCursorAfter slot ptr bs rest := by
  dsimp only [sliceCursorAfter]
  have hpfx_len : bs.length - rest0.length = pfx.length := by
    rw [hpfx, List.length_append, Nat.add_sub_cancel]
  have hv_len : (rest0.take n).length = n := List.length_take_of_le hle
  have hrest_len : (rest0.drop n).length = rest0.length - n := List.length_drop
  have hbs_len : bs.length = pfx.length + rest0.length := by rw [hpfx, List.length_append]
  have hsub_len : bs.length - (rest0.drop n).length = (bs.length - rest0.length) + (rest0.take n).length := by
    omega
  have hptr_eq :
      ptr + BitVec.ofNat 64 (bs.length - rest0.length) + BitVec.ofNat 64 (rest0.take n).length =
        ptr + BitVec.ofNat 64 (bs.length - (rest0.drop n).length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsub_len]
  have hrem_eq :
      BitVec.ofNat 64 rest0.length - BitVec.ofNat 64 (rest0.take n).length =
        BitVec.ofNat 64 (rest0.drop n).length := by
    rw [hv_len, hrest_len]
    apply BitVec.eq_of_toNat_eq
    have h1 : rest0.length < 2 ^ 64 := by omega
    have h2 : n < 2 ^ 64 := by omega
    have h3 : rest0.length - n < 2 ^ 64 := by omega
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]
      omega
  have hrest0 : rest0 = rest0.take n ++ rest0.drop n := (List.take_append_drop n rest0).symm
  have hbs_eq : bs = pfx ++ (rest0.take n ++ rest0.drop n) := by rw [← hrest0, hpfx]
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 (bs.length - rest0.length)) ↦ₛ rest0.take n) ∗
        ((ptr + BitVec.ofNat 64 (bs.length - rest0.length) + BitVec.ofNat 64 (rest0.take n).length) ↦ₛ rest0.drop n) := by
    conv => lhs; rw [hbs_eq, pointsToBytes_append, pointsToBytes_append]
    rw [← hpfx_len, ← sepConj_assoc]
  rw [← hpts, hptr_eq, hrem_eq]
  exact Entails.refl _

theorem fold_vecU8Buf_nonemptyW (A : RustAlloc) (tmpPtr : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) (hv_len : v.length < 2 ^ 63)
    (htmp : tmpPtr ≠ 0#64) :
    A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ⊢
      bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v := by
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 v.length ≠ 0#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat, BitVec.toNat_ofNat, Nat.zero_mod] at h2
    omega
  unfold bm_vecU8Buf
  simp only [hlen_toNat, hcap_ne, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨le_refl _, by omega, htmp⟩ (Entails.refl _)

@[local arm64_norm, local simp]
theorem bitvec_msb_false_of_lt63 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  exact Nat.testBit_lt_two_pow (by omega)

@[local arm64_norm, local simp]
theorem bitvec_getLsbD_63_of_lt63 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false :=
  bitvec_msb_false_of_lt63 hn

/-- `__rust_no_alloc_shim_is_unstable_v2` contract with `decodeVarintSliceStackW` (`24656` bytes). -/
def sessionShimSpecBMX : Spec Unit where
  pre := fun _ s => ⌜True⌝ ∗ stackAt s.sp decodeVarintSliceStackW
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp decodeVarintSliceStackW

/-! ## Relocatable `[LibsignalPlacement]` Phase 2 & 3 Extern Adapters -/

section Placed

open CryptoVerification

theorem sessionShimSpecBMX_eq_gen :
    sessionShimSpecBMX = bmShimSpecGen decodeErrorHookStackW := rfl

theorem mergePlacedPanicW_of_allocFailed [LibsignalPlacement] {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergePlacedSpecW A).onPanic x s0 sf ∗ R :=
  mergePanicX_of_allocFailed (A := A) (x := x) htr hm

/-- Lift `AllocContractsPlaced.shim` (`extHookStack = 16384`) to `sessionShimSpecBMX`
(`decodeVarintSliceStackW = 24656`) on any caller block program. -/
theorem bm_shim_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCl lsmpl sessionShimSpecBMX) := by
  have h0 := hA.shim (callerProg := callerProg)
  have h1 := subroutine_ok_withLsCl_withHookStack_mono
    (s1 := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (s2 := decodeVarintSliceStackW) (by decide) (by decide) h0
  refine subroutine_ok_withLsCl_map' h1 (fun x R s0 hpre => ?_)
  refine ⟨x, R, ?_, fun sf hpost => hpost⟩
  dsimp only [Spec.withHookStack, sessionShimSpec, sessionShimSpecBMX] at hpre ⊢
  simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre

/-- Lift `sessionMemcpySpec extHookStack` (`16384` bytes) to `sessionMemcpySpecBMX`
(`decodeVarintSliceStackW = 24656` bytes) on any caller block program. -/
theorem bm_memcpy_placed_ok_cl [LibsignalPlacement]
    {callerProg : Program}
    (hMemcpy : subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl sessionMemcpySpecBMX) := by
  refine subroutine_ok_withLsCl_map' hMemcpy (fun ⟨dst, src, bs⟩ R s0 hpre => ?_)
  have hstack : stackAt s0.sp decodeVarintSliceStackW =
      memRegion (s0.sp - BitVec.ofNat 64 decodeVarintSliceStackW) 8272 ∗
        stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack :=
    ProofLib.stackAt_split_bottom s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack 8272 (by decide)
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 decodeVarintSliceStackW) 8272 ∗ R, ?_, ?_⟩
  · dsimp only [sessionMemcpySpecBMX, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec] at hpre ⊢
    rw [hstack] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [sessionMemcpySpecBMX, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec] at hpost ⊢
    rw [hstack]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
