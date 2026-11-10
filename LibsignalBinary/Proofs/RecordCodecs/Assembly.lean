/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortized
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge -- shake: keep

/-!
# Record Decoder Assembly and Top-Level Run Theorems

Discharges `DecodeDeps` and `PortDepsPlaced` from proved callee contracts and lifts
`PreKeyRecord::deserialize` (Block `65`), `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`
(Block `84`), and `IdentityKey::decode` (Block `18`) to `Program.ofImage` and relocatable
`[LibsignalPlacement]` hooks (`CodecHooksPlaced`), including `<prost::error::DecodeError>::push`
(Block `257`).
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.RecordCodecsBinary.Assembly

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- The callee contracts of the record decoders, from the hooks and the image loading. -/
theorem decodeDeps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    DecodeDeps img A ext where
  varintSlice := Prost.decodeVarintSlice_ok_ext_x hC
  int32Merge := Prost.int32Merge_ok_ext_x hC
  skipField := Prost.skipField_ok_ext_x hC
  dropDecodeError := Prost.dropDecodeError_ok_ext_x hC.toAllocContractsX
  bytesMerge := Prost.bytes_merge_ok_ext_x himg hC.toAllocContractsX
    hC.decode_error_from hC.decode_varint_slow
    (Prost.decodeVarintSlice_ok_ext_x hC)
    (bytesFromVecOk_ext himg rfl)
    (do_reserve_ok_ext_x hC.toAllocContractsX)
    bytesVtableSlotLoaded
    (fun p v => bytesVtableDropOk_ext_x p v v.length hC.toAllocContractsX himg rfl)
  pkTryFrom := pkTryFrom_ok_ext img ext himg

/-- `PreKeyRecord::deserialize` in the loaded image `img` (any base): `preKeyDeserializeSpec`. -/
theorem preKeyDeserialize_run_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img preKeyDeserializeName) (preKeyDeserializeSpec A img) :=
  root_of_tripleRatchetProgAtExt himg
    (PreKeyDeserialize.preKeyDeserialize_ok_of_deps hC (decodeDeps hC himg)
      (Wire.base_aligned himg))

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` in the loaded image `img` (any base):
`identityKeyPairTryFromSpec`. -/
theorem identityKeyPairTryFrom_run_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img identityKeyPairTryFromName) (identityKeyPairTryFromSpec A img) :=
  root_of_tripleRatchetProgAtExt himg
    (IdentityKeyPairTryFrom.identityKeyPairTryFrom_ok_of_deps hC (decodeDeps hC himg)
      (Wire.base_aligned himg))

/-- `IdentityKey::decode` in the loaded image `img` (any base, any hooks): `identityKeyDecodeSpec`.
It calls only the in-image `PublicKey::try_from`, so it needs no hook contract. -/
theorem identityKeyDecode_run_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img identityKeyDecodeName) (identityKeyDecodeSpec A img) :=
  root_of_tripleRatchetProgAtExt himg
    (IdentityKeyDecode.identityKeyDecode_ok_of_pkTryFrom (pkTryFrom_ok_ext img ext himg)
      (Wire.base_aligned himg))

/-! ## Relocatable `[LibsignalPlacement]` Assembly & Hook-Only Corollaries -/

section Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open CryptoVerification CryptoVerification.RecordCodecs.Placed
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem stackAt_push_growOne (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      memRegion (sp - 8192#64) 3920 ∗
      stackAt (sp - 64#64) SpqrV1.Alloc.growOneStrPairStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_bottom sp 4272 3920 (by decide)
  change stackAt sp decodeErrorHookStack = memRegion (sp - 8192#64) 3920 ∗ stackAt sp 4272 at h1
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 4208 8 (by decide)
  change stackAt sp 4272 =
    stackAt (sp - 64#64) SpqrV1.Alloc.growOneStrPairStack ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushSpec A)`, calling `SpqrV1.Alloc.grow_one_str_pair_placed_ok`
(Block `258`) on the slow path. -/
theorem decode_error_push_spec_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)) := by
  have hgrow0 := SpqrV1.Alloc.grow_one_str_pair_placed_ok (A := A) (H := H)
    h_panic hshim halloc hrealloc
  have hgrow := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_257).rebase (blkPl_257).base H) hgrow0
  change subroutine_ok ((blkPC_257).rebase (blkPl_257).base H) (lsmpl.base 258)
    (withLsCl lsmpl (SpqrV1.Alloc.growOneStrPairSpec A)) at hgrow
  clear hgrow0 h_panic hshim halloc hrealloc
  unfold lsProg_257 withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeErrorPushSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
    simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right]
    simp only [stackAt_push_growOne]
  wpp_init x s0
  obtain ⟨d, e, n⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hptr_ne0 : v_stk_2 ≠ 0#64 := by assumption
  obtain ⟨_hkind1, _hkind2⟩ : KindNoHeap v_stk := by assumption
  have hn_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  conv =>
    arg 4
    simp only [BitVec.ofNat_eq_ofNat,
      InImage.DecodeErrorPush.vecBuf_stackEntryAt_memRegion A n v_stk_1 v_stk_2
        (by omega) (by omega)]
  by_cases heq : BitVec.ofNat 64 n = v_stk_1
  · subst v_stk_1
    have hcap_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by rw [hn_toNat]; exact hn_lt32
    have hnew_toNat : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [SpqrV1.Alloc.newCap32_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply Prost.SepWPp.of_sepWP_lscl (mid := lsmpl.base 258) hcl0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    refine Prost.SepWPp.call_frame_lscl (spec := SpqrV1.Alloc.growOneStrPairSpec A)
      (x := (e, BitVec.ofNat 64 n, v_stk_2))
      (T := (e ↦₆₄ BitVec.ofNat 64 n) ∗ ((e + 8#64) ↦₆₄ v_stk_2) ∗
        (if BitVec.ofNat 64 n = 0#64 then emp
         else A.live v_stk_2 ((BitVec.ofNat 64 n).toNat * 32) 8 ∗
           memRegion v_stk_2 ((BitVec.ofNat 64 n).toNat * 32)) ∗
        A.pool ∗ stackAt (s0.sp - 64#64) SpqrV1.Alloc.growOneStrPairStack)
      hgrow hcl1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, wp_norm, arm64_norm]; exact hsp_align)
      (show _ = (blkPl_257).base + bv% (108) by wp_norm_goal)
      (by dsimp only [SpqrV1.Alloc.growOneStrPairSpec]; congr 1)
      (by exact ⟨by wp_norm_goal, hcap_lt, hptr_ne0⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => allowPanic_frame id hm)
      (fun sf hpc_sf hrun_sf hsp_sf hcs_sf _hcl_sf => ?_)
    rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    simp only [wp_norm, arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hsp_sf
    dsimp only [SpqrV1.Alloc.growOneStrPairSpec]
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, wp_norm, arm64_norm]
    apply SepWPp.exists_elim; intro p'
    refine SepWPp.pure_elim fun ⟨hp', _halign, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [InImage.DecodeErrorPush.memRegion_split_entry p' n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists p'
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      InImage.DecodeErrorPush.vecBuf_stackEntryAt_memRegion A (n + 1)
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)) p' hn1_le_new hnew_bound,
      InImage.DecodeErrorPush.memRegion_split_entry p' n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
    wp_done
  · have hbeq : (BitVec.ofNat 64 n == v_stk_1) = false := beq_eq_false_iff_ne.mpr heq
    have hne_nat : n ≠ v_stk_1.toNat := by
      intro hnat
      apply heq
      apply BitVec.eq_of_toNat_eq
      rw [hn_toNat, hnat]
    have hn_lt_cap : n < v_stk_1.toNat := by omega
    have hn1_le_cap : n + 1 ≤ v_stk_1.toNat := by omega
    have hcap_ne0 : v_stk_1 ≠ 0#64 := by
      intro h0
      subst h0
      change n < 0 at hn_lt_cap
      omega
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [hcap_ne0, ite_false,
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false,
      InImage.DecodeErrorPush.vecBuf_stackEntryAt_memRegion A (n + 1) v_stk_1 v_stk_2
        hn1_le_cap (by omega),
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

/-- Lift `withLsCodeLoaded pl (decodeErrorPushSpec A)` to
`withLsCodeLoaded pl (decodeErrorPushExternSpecWithStack A hookStack)` for any
`decodeErrorHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem decodeErrorPushExternWithStack_lscl_of_spec {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {hookStack : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorPushSpec A)))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorPushExternSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [decodeErrorPushExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn⟩, hmem⟩
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp decodeErrorHookStack
      (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre_raw : s0.mem ⊨ (decodeErrorPushSpec A).pre (d, e, n) s0 ∗ R' := by
    dsimp only [decodeErrorPushSpec, R']
    rw [hsplit] at hmem
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn⟩, by ac_nf at hmem ⊢⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (decodeErrorPushSpec A)).pre (d, e, n) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre_raw⟩
  refine h.mono_outcome (d, e, n) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    simp only [decodeErrorPushSpec, decodeErrorPushExternSpecWithStack, R',
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    refine ⟨hpost.1, e, he_ne, ?_⟩
    rw [hsplit]
    have hm := hpost.2
    ac_nf at hm ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, decodeErrorPushSpec, decodeErrorPushExternSpecWithStack, R'] at hpost ⊢
    have hent : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc _ anyHeap _, ← sepConj_assoc anyHeap _ R, sepConj_assoc _ anyHeap R]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono hent hpost
  · dsimp only [withLsCodeLoaded, decodeErrorPushSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [withLsCodeLoaded, decodeErrorPushSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack))`. -/
theorem decode_error_push_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack))) :=
  decodeErrorPushExternWithStack_lscl_of_spec
    (decode_error_push_spec_placed_ok h_panic hshim halloc hrealloc)

section PrivateDropsPlaced

open ProofLib.ProgramReflection SepProp

private theorem stackAt_add_48_asm {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hstack

private theorem stackAt_add_48_comm_asm {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt sp hookStack := by
  unfold stackAt
  have h0 : hookStack + 48 = 48 + hookStack := Nat.add_comm hookStack 48
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + hookStack)) 48 hookStack (by omega)
  have h1 : sp - BitVec.ofNat 64 (48 + hookStack) =
      sp - BitVec.ofNat 64 hookStack - 48#64 := by
    rw [BitVec.ofNat_add]
    bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + hookStack) + 48#64 =
      sp - BitVec.ofNat 64 hookStack := by
    rw [BitVec.ofNat_add]
    bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists_asm (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single_asm (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells_asm (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists_asm _ v0
    (pointsTo64_entails_exists_asm _ v1
      (pointsTo64_entails_exists_asm _ v2
        (pointsTo64_entails_exists_asm _ v3
          (pointsTo64_entails_exists_asm _ v4
            (pointsTo64_entails_exists_single_asm _ v5)))))

private abbrev DeallocTailGhostAsm :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocTailSpecWithStackAsm (A : RustAlloc) (hookStack : Nat) :
    Spec DeallocTailGhostAsm where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk bs.length align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) hookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp (hookStack + 48)

@[local simp, local arm64_norm]
private theorem getLsbD_or_one_asm (ptr : BitVec 64) : (ptr ||| 1#64).getLsbD 0 = true := by
  bv_bits

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem or_one_and_not_one_asm {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_add_asm {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_false_asm {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

private theorem dealloc_tail_placed_ok_withStack {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64)
    (hdealloc : subroutine_ok P addr (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok P addr (rustDeallocTailSpecWithStackAsm A hookStack) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells_asm (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre' : s0.mem ⊨
      (rustDeallocExternSpecWithStack A hookStack).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) := by
    unfold rustDeallocTailSpecWithStackAsm at hpre
    unfold rustDeallocExternSpecWithStack
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) hookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48_asm hstack, stackAt_add_48_comm_asm hstack] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R))) ▸ h1
  refine hdealloc.mono_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTailSpecWithStackAsm
    unfold rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_add_48_comm_asm hstack]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R)) ▸ hpost
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

private theorem promotableEvenDrop_placed_ok_withStack [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack A hookStack) := by
  unfold promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_placed_ok_withStack hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_asm hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one_asm heven
  refine ProofLib.SepWP.seq (mid := lsρ lsBytesRustDeallocSym) ?_ fun _ _ _ _ hnext => hnext
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add_asm hoff,
      ult_ofNat_false_asm hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add_asm hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

private theorem promotableOddDrop_placed_ok_withStack [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack A hookStack) := by
  unfold promotableOddDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_placed_ok_withStack hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_asm hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  refine ProofLib.SepWP.seq (mid := lsρ lsBytesRustDeallocSym) ?_ fun _ _ _ _ hnext => hnext
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add_asm hoff,
      ult_ofNat_false_asm hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add_asm hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

end PrivateDropsPlaced

private theorem bytes_merge_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpecX A)) :=
  Prost.bytes_merge_placed_ok_of_contracts_x
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_error_from_placed_ok_x hshim halloc hpanic_alloc))
    (Prost.bmMemcpy_placed_of_frameless (ls_hook_ok_of_mem hmc))
    (Prost.bmShim_placed_of_noAllocShim (ls_hook_ok_of_mem hshim))
    (Prost.subroutine_ok_withLsCl_of_plain
      (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide)))
    ((ls_externAt?_of_mem (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_varint_slow_placed_ok_with_stack_of_hooks hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_varint_slice_placed_ok_x hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (do_reserve_placed_ok_x hshim halloc hrealloc hpanic_raw))
    (fun tmpPtr v =>
      Prost.subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok_of_drops
          (promotableEvenDrop_placed_ok_withStack (by decide)
            (rustDeallocExternWithStack_of_rustDealloc
              (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide)))
          (promotableOddDrop_placed_ok_withStack (by decide)
            (rustDeallocExternWithStack_of_rustDealloc
              (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide)))
          (by decide) tmpPtr v v.length))

/-- Discharge all `PortDepsPlaced` callee contracts from external `CodecHooksPlaced`. -/
theorem portDepsPlaced_of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : CodecHooksPlaced A H) :
    PortDepsPlaced A H where
  varintSlice := Prost.decode_varint_slice_placed_ok_x hH.shim hH.alloc hH.panic_alloc
  int32Merge := Prost.int32_merge_placed_ok_x hH.shim hH.alloc hH.panic_alloc
  skipField := Prost.skipField_placed_ok_x hH.shim hH.alloc hH.panic_alloc
  dropDecodeError := Prost.drop_decode_error_placed_ok_x hH.dealloc
  bytesMerge := bytes_merge_placed_ok_x hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy
    hH.panic_alloc hH.panic_raw
  pkTryFrom := pkTryFrom_placed_ok H
  varintSlow := Prost.decode_varint_slow_placed_ok_with_stack_of_hooks hH.shim hH.alloc
    hH.panic_alloc
  decodeErrorFrom := Prost.decode_error_from_placed_ok_gen hH.shim hH.alloc hH.panic_alloc
  decodeErrorPush := decode_error_push_placed_ok hH.panic_raw hH.shim hH.alloc hH.realloc
  dealloc := hH.dealloc

/-- `PreKeyRecord::deserialize` (Block `65`) under `[LibsignalPlacement]` from external hooks
`CodecHooksPlaced A H`. -/
theorem preKeyRecord_deserialize_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A) :=
  PreKeyDeserialize.preKeyRecord_deserialize_placed_ok (portDepsPlaced_of_hooks hH)

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`) under `[LibsignalPlacement]`
from external hooks `CodecHooksPlaced A H`. -/
theorem identityKeyPair_tryFrom_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A) :=
  IdentityKeyPairTryFrom.identityKeyPair_tryFrom_placed_ok (portDepsPlaced_of_hooks hH)

/-- `IdentityKey::decode` (Block `18`) under `[LibsignalPlacement]` for any hooks `H`. -/
theorem identityKey_decode_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  IdentityKeyDecode.identityKey_decode_placed_ok H

end Placed

end CryptoVerification.RecordCodecsBinary.Assembly
