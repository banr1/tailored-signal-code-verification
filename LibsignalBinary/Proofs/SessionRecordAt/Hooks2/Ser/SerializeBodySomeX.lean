/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize` (`0x1857c`): `Some` Branch

Verifies `SessionRecord::serialize` (`0x1857c`, Block `52`) on a `SessionRecord` with an active
session (`serializeSomeSpecX A`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local wp_norm] serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq

theorem L1_SerializeBodySomeX : True := trivial

/-! ## `Some`-branch specification -/

structure SerializeSomeGhostX where
  self : BitVec 64
  out : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : LibsignalSessionApi.Session (List (BitVec 8))

/-- `serialize` on a record with a current session (`serializeSomeSpec` at `serializeStackX`). -/
def serializeSomeSpecX (A : RustAlloc) : Spec SerializeSomeGhostX where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (lenField 1 (encSessionMem x.G x.sess)).length < 2 ^ 32⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      A.pool ∗ memRegion x.out 32 ∗ stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (lenField 1 (encSessionMem x.G x.sess)) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Pure and separation-logic helpers -/

theorem sessionAt_pack_776X (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8)))
    {bs336 : List (BitVec 8)}
    (hinl : SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)) :
    (((sp - 776#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 768#64) ↦ₛ bs336) ∗ sessionAtHeap A G s) ⊢
      sessionStateReprAt A (sp - 776#64) G s := by
  have h := sessionAt_pack_head_tail A (sp - 776#64) G s hinl
  have e : sp - 776#64 + 8#64 = sp - 768#64 := bv_sub_add_lit sp 776 8
  rwa [e] at h

theorem sessionAt_unpack_800X (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A (sp - 800#64) G s ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        ((sp - 800#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 792#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  have h := sessionAt_unpack_head_tail A (sp - 800#64) G s
  have e : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  rwa [e] at h

theorem memRegion_out32_stack_someX (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStackX =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        stackAt (sp - 800#64) serializeSubStackX ∗
        memRegion (sp - 800#64) 344 ∗
        memRegion (sp - 456#64) 24 ∗
        memRegion (sp - 432#64) 336 ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [memRegion_out32_cellsX, stackAt_serialize_some_preX]

theorem repack_stack_some_cellsX (sp w0 w1 w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStackX ∗
      ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
  have hp : ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) =
      ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) := pointsTo64_pair_sub sp 432 w0 w1
  have hv := vecHeader_cells_800X sp
  have hpull :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₆₄ w0) ∗
        ((sp - 424#64) ↦₆₄ w1) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) ∗
        memRegion (sp - 776#64) 344 ∗
        (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull, hv, hp]
  exact repack_stack_someX sp (w1 ++ w0) w2

theorem memRegion_split_init_byteX (ptr : BitVec 64) {n : Nat}
    (hpos : 1 ≤ n) (hlt : n < 2 ^ 63) :
    memRegion ptr n =
      (∃∗ b0 : BitVec 8, (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) := by
  have h1 : n = 1 + (n - 1) := by omega
  conv => lhs; rw [h1]
  rw [memRegion_split ptr 1 (n - 1) (by omega),
    memRegion_eq_exists_bytes ptr 1 (by decide)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro hlen
    rcases bs with _ | ⟨b0, _ | _⟩ <;> simp at hlen
    rw [pointsToBytes_singleton]
    exact Entails.sepExists_right b0 (Entails.refl _)
  · apply Entails.sepExists_elim; intro b0
    rw [← pointsToBytes_singleton]
    exact Entails.sepExists_right [b0] (Entails.pure_right rfl (Entails.refl _))

theorem vecU8At_unpack_cells_432X (A : RustAlloc) (sp cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A (sp - 432#64) cap ptr bs =
      (((sp - 432#64) ↦₆₄ cap) ∗ ((sp - 424#64) ↦₆₄ ptr) ∗
        ((sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
  unfold vecU8At RustHeap.vecU8Buf vecHeader
  have e1 : sp - 432#64 + 8#64 = sp - 424#64 := bv_sub_add_lit sp 432 8
  have e2 : sp - 432#64 + 16#64 = sp - 416#64 := bv_sub_add_lit sp 432 16
  rw [e1, e2]
  ac_rfl

theorem lenField_one_bv_toNatX {bs : List (BitVec 8)}
    (h : (lenField 1 bs).length < 2 ^ 32) :
    (BitVec.ofNat 64 (lenField 1 bs).length).toNat = (lenField 1 bs).length := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem cap_lt_not_noneCapX {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_ult_zeroX (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  simp [BitVec.ult]

theorem lenField_one_branch_condsX {bs : List (BitVec 8)}
    (h : (lenField 1 bs).length < 2 ^ 32) :
    BitVec.ule (BitVec.ofNat 64 (lenField 1 bs).length)
      (BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length) = false ∧
    (BitVec.ofNat 64 (lenField 1 bs).length).getLsbD 63 = false ∧
    (BitVec.ofNat 64 (lenField 1 bs).length == 0#64) = false := by
  have hlen := lenField_one_length bs
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.ule, BitVec.toNat_ofNat]
    have h1 : (lenField 1 bs).length % 2 ^ 64 = (lenField 1 bs).length :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (encodeVarint (BitVec.ofNat 64 bs.length)).length % 2 ^ 64 =
        (encodeVarint (BitVec.ofNat 64 bs.length)).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    exact decide_eq_false (by omega)
  · rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  · apply beq_false_of_ne
    intro heq
    have h1 : (BitVec.ofNat 64 (lenField 1 bs).length).toNat = 0 :=
      congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    omega

theorem vecU8At_init_byte_432X (A : RustAlloc) (sp ptr : BitVec 64) (n : Nat) (b0 : BitVec 8)
    (hpos : 1 ≤ n) (hlt : n < 2 ^ 32) (hptr : ptr ≠ 0) :
    (((sp - 432#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ((sp - 424#64) ↦₆₄ ptr) ∗
      ((sp - 416#64) ↦₆₄ 1#64) ∗
      A.live ptr n 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) ⊢
      vecU8At A (sp - 432#64) (BitVec.ofNat 64 n) ptr [b0] := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e1 : sp - 432#64 + 8#64 = sp - 424#64 := bv_sub_add_lit sp 432 8
  have e2 : sp - 432#64 + 16#64 = sp - 416#64 := bv_sub_add_lit sp 432 16
  have h := vecU8At_init_byte A (sp - 432#64) (BitVec.ofNat 64 n) ptr b0
    (htoNat.symm ▸ hpos) (by omega) hptr
  rwa [htoNat, e1, e2] at h

theorem lenField_one_cons_eqX {bs bs' : List (BitVec 8)} (h : bs = bs') :
    10#8 :: (encodeVarint (BitVec.ofNat 64 bs'.length) ++ bs) = lenField 1 bs' := by
  subst h
  exact (lenField_one_eq bs).symm

theorem serialize_panic_at_handle_errorX {b : BitVec 64} {ext : String → Option (State → State)} :
    (SP2Ext b ext).externAt?
      ((SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) =
      some Rust.panicked := by
  exact panic_at_panicSymbol_ext (b := b) (ext := ext)
    (name := serializeName) (hname := "alloc::raw_vec::handle_error")
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    (stub := num% (ls_off% "alloc::raw_vec::handle_error"))
    libsignalSessionCode_fnOff_serialize (by simp only [arm64_norm]) (by decide)
    (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

/-! ## Stack-pointer normalization tactics -/

open Lean Meta Elab Tactic in
/-- `wppin_sp_norm`: rewrite the `SepWPpIn` precondition (arg 5) with every local `_.sp = _`
hypothesis (chains `sf_k.sp = sf_j.sp = … = s0.sp - c` left by successive calls). -/
elab "wppin_sp_norm" : tactic => do
  let g ← getMainGoal
  let ids ← g.withContext do
    let mut acc : Array Ident := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
      let ty ← instantiateMVars decl.type
      if let some (_, lhs, _) := ty.eq? then
        if lhs.isAppOfArity ``Arm64.State.sp 1 then
          acc := acc.push (mkIdent decl.userName)
    pure acc
  for _ in [0:4] do
    for i in ids do
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| conv => arg 5; rw [$i:ident])))

/-- `wppin_callc h S ghost`: refold `h : subroutine_ok _ _ <unfolded S.inImage img>` (the stepping
tactics unfold specs in hypotheses) to `S` and call it with `wppin_call`, then normalize `sp`. -/
macro "wppin_callc " h:ident S:term:max g:term:max : tactic =>
  `(tactic| (change subroutine_ok _ _ $S at $h:ident; wppin_call $h $g; try wppin_sp_norm))

/-! ## `Some`-branch verification on `SP2Ext` -/

set_option maxHeartbeats 800000 in
theorem serialize_some_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hClone : SessionCloneOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (hDrop : DropSessionStructureLocal1OkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName)
      ((serializeSomeSpecX A).inImage img) := by
  have hfn : libsignalSessionCode.fnOff serializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  have hmemcpy := memcpy_sub_okX (img := img) (A := A) (ext := ext) hC
  have hshim := shim_sub_okX (img := img) (A := A) (ext := ext) hC
  have halloc := alloc_sub_okX (img := img) (A := A) (ext := ext) hC
  have hpanic := serialize_panic_at_handle_errorX (b := img.base) (ext := ext)
  have hclone := sessionClone_sub_okX hClone
  have hvv := vecVecClone_sub_okX img.base ext
  have hlen := sessionLen_sub_okX A img.base ext
  have hev := encodeVarint_sub_okX hEV
  have hraw := encodeRaw_sub_okX hRaw
  have hdrop := dropLocal1_sub_okX hDrop
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0 196
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x10c 160
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x1bc 4
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x2b4 48
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x310 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x32c 32
  unfold serializeSomeSpecX
  simp only [okTagVec, memRegion_out32_stack_someX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wppin_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr, G, sess⟩ := x
  dsimp only at *
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_frame) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc hclone ((sessionCloneSubSpecX A).inImage img) ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  clear hclone hpre hinl_self
  generalize sessionStateReprAt A (self + 24#64) G sess = ssSelf
  have heq_enc : encSessionMem w sess = encSessionMem G sess := hpost
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  refine SepWP.fold (sessionAt_unpack_800X A s0.sp w sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wppin_callc hmemcpy (memcpySubSpecX.inImage img) (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_frame) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wp_steps
  wp_call hvv ⟨s0.sp - 800#64, prevPtr⟩
  clear hvv
  generalize ((self + 8#64) ↦₆₄ prevPtr) = pSelf8
  generalize ((self + 16#64) ↦₆₄ 0#64) = pSelf16
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wppin_callc hmemcpy (memcpySubSpecX.inImage img) (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  apply SepWPpIn.of_sepWP
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  refine SepWP.fold (sessionAt_pack_776X A s0.sp w sess hinl_clone) (by sep_frame) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_steps
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by
    assumption
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbs_lt_w : (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  have hlen_w : subroutine_ok (SP2Ext img.base ext)
      (entry + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      { pre := fun (_ : Unit) s =>
          ⌜s.readReg64 Reg.x0 = s0.sp - 776#64⌝ ∗
            sessionStateReprAt A (s0.sp - 776#64) w sess ∗ stackAt s.sp serializeSubStackX
        post := fun _ s0' sf =>
          ⌜sf.readReg64 Reg.x0 = BitVec.ofNat 64 (encSessionMem G sess).length ∧ sf.trace = s0'.trace⌝ ∗
            sessionStateReprAt A (s0.sp - 776#64) w sess ∗ stackAt s0'.sp serializeSubStackX } := by
    refine subroutine_ok_outcome_intro fun _ R' s_in hpc_in hrun_in hm_in hal_in => ?_
    have hm_in' : s_in.mem ⊨
        (⌜s_in.readReg64 Reg.x0 = s0.sp - 776#64 ∧ (encSessionMem w sess).length < 2 ^ 32⌝ ∗
          sessionStateReprAt A (s0.sp - 776#64) w sess ∗ stackAt s_in.sp serializeSubStackX) ∗ R' := by
      rw [sepConj_assoc] at hm_in ⊢
      obtain ⟨hx0, hrest⟩ := (satisfies_pure_sepConj _ _ _).1 hm_in
      exact (satisfies_pure_sepConj _ _ _).2 ⟨⟨hx0, hbs_lt_w⟩, hrest⟩
    exact (hlen.to_outcome ⟨s0.sp - 776#64, w, sess⟩ R' s_in hpc_in hrun_in hm_in' hal_in).mono_outcome
      fun sf hout => by unfold SubroutineOutcome at hout ⊢; dsimp only at hout ⊢; rwa [heq_enc] at hout
  clear hlen
  wp_call hlen_w ()
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc hshim (shimSubSpecX.inImage img) ()
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hsz_pos : 0 < (lenField 1 (encSessionMem G sess)).length := by omega
  have hsz_le : (lenField 1 (encSessionMem G sess)).length + 1 ≤ 2 ^ 63 := by omega
  wppin_callc halloc ((rustAllocSubSpecX A).inImage img) ((lenField 1 (encSessionMem G sess)).length, 1)
  by_cases hp0 : sf_6.readReg64 .x0 = 0#64
  · -- allocation failure: `handle_error` panics
    conv => arg 5; simp only [hp0, sepConj_assoc]
    refine SepWPpIn.pure_elim fun htr_fail => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpIn.panic (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : sf_6.readReg64 .x0 ≠ 0 := hp0
    have hp0_beq : (sf_6.readReg64 .x0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    rw [memRegion_split_init_byteX (sf_6.readReg64 .x0) hlf_pos_G hlf_lt63_G]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wp_steps
    wp_call hlen_w ()
    clear hlen_w
    wp_steps
    refine SepWP.fold (vecU8At_init_byte_432X A s0.sp (sf_6.readReg64 .x0)
      (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0')
      (by dsimp only [Reg.x0]; sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wppin_callc hev ((encodeVarintSubSpecX A).inImage img)
      ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
        BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
        sf_6.readReg64 .x0, [0x0a#8]⟩
    clear hev
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hraw_lt_w : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_enc]; exact hraw_lt_G
    wppin_callc hraw ((encodeRawSubSpecX A).inImage img) ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    clear hraw
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    rw [lenField_one_cons_eqX heq_enc, vecU8At_unpack_cells_432X]
    wp_steps
    refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess) (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wppin_callc hdrop ((dropLocal1SubSpecX A).inImage img) ⟨s0.sp - 776#64, w, sess.state⟩
    clear hmemcpy hshim halloc hpanic hdrop heq_enc hinl_clone
    have htr10 : sf_10.trace = s0.trace := by
      rw [hpost_9, hpost_8, h_98, hpost_6, htr_alloc, hpost_5, hpost_4, hpost_3, hpost_2, hpost_1, h_13]
    have hv10 : calleeSavedVRegs sf_10 = calleeSavedVRegs s0 := by
      rw [hvregs_10, hvregs_9, hvregs_8, hvregs_7, hvregs_6, hvregs_5, hvregs_4, hvregs_3, hvregs_2, hvregs_1, hvregs]
    apply SepWPpIn.of_sepWP_ret
    wp_steps
    generalize lenField 1 (encSessionMem G sess) = lfBytes
    refine SepWP.fold (vecU8_from_out_cellsX A out _ _ lfBytes)
      (by sep_frame) ?_
    refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
    refine SepWP.fold (repack_stack_some_cellsX s0.sp _ _ _) (by sep_frame) ?_
    generalize stackAt s0.sp serializeStackX = stkFinal
    generalize vecU8 A (out + 8#64) lfBytes = vecFinal
    generalize A.pool = poolFinal
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨fun hm => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
    · simp only [wp_norm, arm64_norm, htr10, pure_true, emp_sepConj]
      have hP_eq :
          ((stkFinal ∗ vecFinal ∗ poolFinal ∗ ssSelf ∗ pSelf8 ∗ pSelf16 ∗ (out ↦₆₄ okTagVec)) ∗ R) =
          (pSelf8 ∗ pSelf16 ∗ ssSelf ∗ (out ↦₆₄ okTagVec) ∗ vecFinal ∗ poolFinal ∗ stkFinal ∗ R) := by
        ac_rfl
      dsimp only [okTagVec] at hP_eq
      rwa [← hP_eq]
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm, hv10, and_self]

/-! ## Relocatable `[LibsignalPlacement]` `Some`-branch proof (Block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem L1_SerializeBodySomeX_Placed : True := trivial

open Lean Meta Elab Tactic in
/-- `wpplscl_sp_norm`: rewrite the `SepWPpLsCl` precondition (arg 5) with every local `_.sp = _`
hypothesis (chains `sf_k.sp = sf_j.sp = … = s0.sp - c` left by successive calls). -/
elab "wpplscl_sp_norm" : tactic => do
  let g ← getMainGoal
  let ids ← g.withContext do
    let mut acc : Array Ident := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
      let ty ← instantiateMVars decl.type
      if let some (_, lhs, _) := ty.eq? then
        if lhs.isAppOfArity ``Arm64.State.sp 1 then
          acc := acc.push (mkIdent decl.userName)
    pure acc
  for _ in [0:4] do
    for i in ids.reverse do
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| conv => arg 5; rw [$i:ident])))

/-- `wpplscl_callc h S ghost`: refold `h : subroutine_ok _ _ <unfolded withLsCodeLoaded lsmpl S>`
to `S` and call it with `wpplscl_call`, then normalize `sp`. -/
macro "wpplscl_callc " h:ident S:term:max g:term:max : tactic =>
  `(tactic| (change subroutine_ok _ _ $S at $h:ident; wpplscl_call $h $g; try wpplscl_sp_norm))

private abbrev lhsOfNe_serX {α : Type} {x y : α} (_ : x ≠ y) : α := x

private theorem sepWPpLsCl_split_x0_serX {pl : MultiPlacement} {prog : Program}
    {ret_pc : BitVec 64} {s : State}
    {P : SepProp} {Qp Q : State → SepProp → Prop}
    (h0 : s.readReg64 .x0 = 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q)
    (hn : s.readReg64 .x0 ≠ 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q) :
    SepWPpLsCl pl prog ret_pc s P Qp Q := by
  by_cases h : s.readReg64 .x0 = 0#64
  · exact h0 h
  · exact hn h

set_option maxHeartbeats 800000 in
theorem serialize_some_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSomeSpecX A)) := by
  have hmemcpy := memcpy_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_okX (callerProg := lsProg_52 H) hC
  have halloc := alloc_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hpanic := hC.alloc.externAt_handle_error (callerProg := lsProg_52 H)
  have hclone : subroutine_ok (lsProg_52 H) (lsmpl.base 80)
      (withLsCodeLoaded lsmpl (sessionCloneSubSpecX A)) :=
    sessionClone_placed_sub_okX (callerProg := lsProg_52 H) hClone
  have hvv : subroutine_ok (lsProg_52 H) (lsmpl.base 117)
      (withLsCodeLoaded lsmpl vecVecCloneSubSpecX) :=
    vecVecClone_placed_sub_okX (callerProg := lsProg_52 H)
  have hlen : subroutine_ok (lsProg_52 H) (lsmpl.base 86)
      (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) :=
    sessionLen_placed_sub_okX (callerProg := lsProg_52 H) (A := A)
  have hev : subroutine_ok (lsProg_52 H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSubSpecX A)) :=
    encodeVarint_placed_sub_okX (callerProg := lsProg_52 H) hEV
  have hraw : subroutine_ok (lsProg_52 H) (lsmpl.base 14)
      (withLsCodeLoaded lsmpl (encodeRawSubSpecX A)) :=
    encodeRaw_placed_sub_okX (callerProg := lsProg_52 H) hRaw
  have hdrop : subroutine_ok (lsProg_52 H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) :=
    dropLocal1_placed_sub_okX (callerProg := lsProg_52 H) hDrop
  unfold serializeSomeSpecX
  simp only [okTagVec, memRegion_out32_stack_someX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpplscl_init x s0
  obtain ⟨self, out, prevPtr, G, sess⟩ := x
  dsimp only at *
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_frame) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hclone (withLsCodeLoaded lsmpl (sessionCloneSubSpecX A)) ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  have heq_encF : ∀ s', s' = sess → encSessionMem w s' = encSessionMem G s' :=
    fun _ h => h ▸ hpost
  have heq_enc : encSessionMem w sess = encSessionMem G sess := heq_encF sess rfl
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  refine SepWP.fold (sessionAt_unpack_800X A s0.sp w sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpySubSpecX) (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 117)
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_frame) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hvv (withLsCodeLoaded lsmpl vecVecCloneSubSpecX) ⟨s0.sp - 800#64, prevPtr⟩
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpySubSpecX) (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
  refine SepWP.fold (sessionAt_pack_776X A s0.sp w sess hinl_clone) (by sep_frame) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_steps
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by
    assumption
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbs_lt_w : (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) ⟨s0.sp - 776#64, w, sess⟩
  simp only [heq_enc] at *
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hsz_pos : 0 < (lenField 1 (encSessionMem G sess)).length := by omega
  have hsz_le : (lenField 1 (encSessionMem G sess)).length + 1 ≤ 2 ^ 63 := by omega
  wpplscl_callc halloc (withLsCodeLoaded lsmpl (rustAllocSubSpecX A)) ((lenField 1 (encSessionMem G sess)).length, 1)
  refine sepWPpLsCl_split_x0_serX (fun hp0 => ?_) (fun hp0 => ?_)
  · -- allocation failure: `handle_error` panics
    conv => arg 5; simp only [hp0, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htr_fail => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpLsCl.panic (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : lhsOfNe_serX hp0 ≠ 0 := hp0
    have hp0_beq : (lhsOfNe_serX hp0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
    rw [memRegion_split_init_byteX (lhsOfNe_serX hp0) hlf_pos_G hlf_lt63_G]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) ⟨s0.sp - 776#64, w, sess⟩
    try simp only [heq_encF sess rfl] at *
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    refine SepWP.fold (vecU8At_init_byte_432X A s0.sp (lhsOfNe_serX hp0)
      (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0')
      (by dsimp only [lhsOfNe_serX, Reg.x0]; sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpplscl_callc hev (withLsCodeLoaded lsmpl (encodeVarintSubSpecX A))
      ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
        BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
        lhsOfNe_serX hp0, [0x0a#8]⟩
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 14)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hraw_lt_w : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_encF sess rfl]; exact hraw_lt_G
    wpplscl_callc hraw (withLsCodeLoaded lsmpl (encodeRawSubSpecX A)) ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 6)
    rw [lenField_one_cons_eqX (heq_encF sess rfl), vecU8At_unpack_cells_432X]
    wp_steps
    refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess) (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpplscl_callc hdrop (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) ⟨s0.sp - 776#64, w, sess.state⟩
    apply SepWPpLsCl.of_sepWP_ret
    wp_steps
    refine SepWP.fold (vecU8_from_out_cellsX A out _ _ (lenField 1 (encSessionMem G sess)))
      (by sep_frame) ?_
    refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
    refine SepWP.fold (repack_stack_some_cellsX s0.sp _ _ _) (by sep_frame) ?_
    wp_done

end Placed

end CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
