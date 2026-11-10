/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Top
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Top
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Contract Wiring, `.rodata` Extraction, and Composition

**Checked by Lean.** Stack-slot non-null bounds (`DEV-SPQR4`), `.rodata` jump-table extraction
and restoration (`spqrRecvRoAt`), `SpqrRecvContracts` assembly from verified callee contracts, and
top-level composition (`spqrRecv_ok_of_tails`) for `spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack-Pointer Non-Null Helpers (`DEV-SPQR4`) -/

/-- When `sp.toNat ≥ N > n > 0` (with `N < 2 ^ 64` implicitly bounded by `sp.toNat < 2 ^ 64`),
    the stack slot address `sp - BitVec.ofNat 64 n` is strictly positive and therefore non-null
    (`≠ 0#64`). -/
theorem sp_sub_ne_zero_of_le {n N : Nat} {sp : BitVec 64}
    (hn : 0 < n) (hlt : n < N) (hle : N ≤ sp.toNat) :
    sp - BitVec.ofNat 64 n ≠ 0#64 := by
  have hsp_lt : sp.toNat < 18446744073709551616 := sp.isLt
  intro hzero
  have htoNat := congrArg BitVec.toNat hzero
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at htoNat
  change (18446744073709551616 - n % 18446744073709551616 + sp.toNat) % 18446744073709551616 = 0 at htoNat
  omega

/-- The stack slot `s0.sp - 4992#64` (`sp + 192` in the `5184`-byte `spqr::recv` frame) is
    non-null whenever `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem sp_sub_4992_ne_zero {sp : BitVec 64} (hle : spqrRecvStack ≤ sp.toNat) :
    sp - 4992#64 ≠ 0#64 :=
  sp_sub_ne_zero_of_le (n := 4992) (N := spqrRecvStack) (by decide) (by decide) hle

/-- The stack slot `s0.sp - 4640#64` (`sp + 544` in the `5184`-byte `spqr::recv` frame) is
    non-null whenever `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem sp_sub_4640_ne_zero {sp : BitVec 64} (hle : spqrRecvStack ≤ sp.toNat) :
    sp - 4640#64 ≠ 0#64 :=
  sp_sub_ne_zero_of_le (n := 4640) (N := spqrRecvStack) (by decide) (by decide) hle

/-! ## 2. `.rodata` Extraction and Restoration for `spqrRecvRoAt` -/

theorem rodata_optProtoInnerStateJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ optProtoInnerStateJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "220036000561663b870a")) (n := 10) (bs := optProtoInnerStateJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_v1StateJumpTables {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ v1StateJumpTablesAt img.base ∗ P := by
  have h1 := rodata_optProtoInnerStateJumpTable himg hF hP
  have h2 := rodata_v1StateMergeJumpTableExpanded himg hF h1
  refine Satisfies.mono (Entails.of_eq ?_) h2
  dsimp only [v1StateJumpTablesAt]
  ac_rfl

theorem rodata_statesFromPbJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesFromPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000ed0058008600170029014701e100")) (n := 22) (bs := statesFromPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_statesIntoPbJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000c7005d0098000a00fc001d01b600")) (n := 22) (bs := statesIntoPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract `spqrRecvRoAt img.base` from `logOff img ∗ TokenInit img` under `Obj.Loads
    libsignalSessionImage img` and `img.FrozenLoaded s`. -/
theorem rodata_spqrRecvRoAt {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp}
    (hP : s.mem ⊨ logOff img ∗ TokenInit img ∗ P) :
    s.mem ⊨ spqrRecvRoAt img.base ∗ P := by
  have hP' : s.mem ⊨ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt img.base ∗ P := hP
  have h1 := rodata_statesRecvRoAt himg hF hP'
  have h2 := rodata_v1StateJumpTables himg hF h1
  have h3 := rodata_statesFromPbJumpTable himg hF h2
  have h4 := rodata_statesIntoPbJumpTable himg hF h3
  refine Satisfies.mono (Entails.of_eq ?_) h4
  dsimp only [spqrRecvRoAt]
  ac_rfl

/-- Discard the read-only `.rodata` slices in `spqrRecvRoAt img.base`, recovering `logOff img ∗
    TokenInit img ∗ P`. -/
theorem spqrRecvRoAt_restore {img : Obj.Image} {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrRecvRoAt img.base ∗ P) :
    m ⊨ logOff img ∗ TokenInit img ∗ P := by
  have hm' :
      m ⊨ (Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
           statesFromPbJumpTableAt img.base ∗
           statesRecvJumpTableAt img.base ∗
           ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
           reduceTableAt img.base ∗
           statesIntoPbJumpTableAt img.base) ∗
          (logOff img ∗ TokenInit img ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    have hlog : (img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64 = logOff img := rfl
    dsimp only [spqrRecvRoAt, statesRecvRoAt, unchunkedSendCt2RoAt]
    rw [hlog, tokenInitAt_eq_TokenInit]
    ac_rfl
  exact Satisfies.of_sep_right hm'

/-! ## 3. Constructing `SpqrRecvContracts` from Verified Callee Theorems -/

/-- Assemble `SpqrRecvContracts canonicalV1InnerHeap img A F K ext` from the already-proved
    callee `OkX` theorems and remaining leaf contracts. -/
theorem spqrRecvContracts_of_okX
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDecodeState : DecodeStateOkX canonicalV1InnerHeap img A ext)
    (hAuthNew : AuthNewOkX img F A ext)
    (hChainNew : ChainNewOkX img (spqrHkdfWith F) A ext)
    (hChainAddEpoch : ChainAddEpochOkX img (spqrHkdfWith F) A ext)
    (hChainRecvKey : ChainRecvKeyOkX img (spqrHkdfWith F) A ext)
    (hMsgDeser : MessageDeserializeOkX spqrPolyApi img A ext)
    (hStatesFromPb : StatesFromPbOkX img A F ext)
    (hStatesRecv : StatesRecvOkX img A F K ext) :
    SpqrRecvContracts canonicalV1InnerHeap img A F K ext where
  base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
  himg := himg
  hA := hA
  decodeState_ok := hDecodeState
  initInner_ok := init_inner_ok_x himg hA hAuthNew
  chainFrom_ok :=
    chainFrom_ok_of_contracts_x
      (chain_from_pb_ok hA.dealloc)
      hChainNew
  chainFromPb_ok := chain_from_pb_ok hA.dealloc
  chainNew_ok := hChainNew
  chainAddEpoch_ok := hChainAddEpoch
  chainRecvKey_ok := hChainRecvKey
  chainIntoPb_ok := chain_into_pb_ok hA
  messageDeserialize_ok := hMsgDeser
  statesFromPb_ok := hStatesFromPb
  statesRecv_ok := hStatesRecv
  statesIntoPb_ok := states_into_pb_ok_x hA
  encodeToVec_ok := pqRatchetStateEncodeToVec_okX hA himg
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A

/-- Construct `Prost.MessageMerge.BytesMerge3Contracts img A ext` from `Obj.Loads
    libsignalSessionImage img` and `Stage2Contracts img.base C A ctl uuidTryParse S ext`. -/
theorem bytesMerge3Contracts_of_stage2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    Prost.MessageMerge.BytesMerge3Contracts img A ext where
  loads := himg
  alloc := hC.toAllocContracts
  decode_error_from := hC.decode_error_from
  decode_varint2 := subroutine_ok_inImage_of_subroutine_ok img (Varint.decodeVarint2_ok_ext hC)
  bytes_from_vec := bytesFromVecOk_ext himg rfl
  reserve7 := do_reserve_7_ok_ext hC.toAllocContracts
  vtable_slot := bytesVtableSlotLoaded
  vtable_drop := fun p v => bytesVtableDropOk_ext p v v.length hC.toAllocContracts himg rfl

/-- `spqr::decode_state` (`0x5349c`) meets `DecodeStateOkX canonicalV1InnerHeap img A ext`. -/
theorem decode_state_ok_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext :=
  spqr_decode_state_ok_of_bytes_contracts
    (ProofLib.base_aligned_of_loads himg) hC
    (bytesMerge3Contracts_of_stage2 himg hC)

/-- `<Authenticator>::update` (`0x69dbc`) meets `AuthUpdateOkX img F A ext`. -/
theorem auth_update_ok_x {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthUpdateOkX img F A ext :=
  authUpdate_ok_of_hook_x himg (slice_concat_2_ok_x hA hRO) hhkdf
    (AllocContractsX.of_AllocContracts hA) hZero

/-- `<Authenticator>::new` (`0x69994`) meets `AuthNewOkX img F A ext`. -/
theorem auth_new_ok_x {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthNewOkX img F A ext :=
  authNew_ok_of_hook_x himg (auth_update_ok_x himg hhkdf hA hRO hZero)
    (AllocContractsX.of_AllocContracts hA) hZero

/-- Lift `SpqrHooks C A K abs` to `tripleRatchetExterns C ctl abs`. -/
theorem spqrHooks_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (tripleRatchetExterns C ctl abs) where
  fromSeed := hSH.fromSeed
  pk1 := hSH.pk1
  pk2 := hSH.pk2
  encaps1 := hSH.encaps1
  encaps2 := hSH.encaps2
  decaps := hSH.decaps
  validatePk := hSH.validatePk
  hmac := hSH.hmac

/-- Lift `HookSat abs allocZeroedName (rustAllocZeroedSpec A)` to `tripleRatchetExterns C ctl
    abs`. -/
theorem hookSat_allocZeroed_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (tripleRatchetExterns C ctl abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hZero

/-- Assemble `SpqrRecvContracts canonicalV1InnerHeap img A C.F K (tripleRatchetExterns C ctl
    abs)` from `TripleRatchetHooks C A (spqrV1 C.F K) abs`, `SpqrHooks C A K abs`, `Obj.Loads
    libsignalSessionImage img`, `StatesFromPbOkX`, and `StatesRecvOkX` (matching
    `spqrSendContracts_of_hooks` in `Top/Send/Contracts.lean`). -/
theorem spqrRecvContracts_of_hooks
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (_hSH : SpqrHooks C A K abs)
    (hFromPb : StatesFromPbOkX img A C.F (tripleRatchetExterns C ctl abs))
    (hStatesRecv : StatesRecvOkX img A C.F K (tripleRatchetExterns C ctl abs)) :
    SpqrRecvContracts canonicalV1InnerHeap img A C.F K (tripleRatchetExterns C ctl abs) := by
  let ext := tripleRatchetExterns C ctl abs
  have hStage2 : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hStage2.toAllocContracts
  have hAX : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hA
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg
      (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs)
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_tripleRatchetExterns C ctl abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_tripleRatchetExterns hTH.allocZeroed
  exact spqrRecvContracts_of_okX himg hA
    (decode_state_ok_x himg hStage2)
    (auth_new_ok_x himg hhkdf hA hRO hZero)
    (chainNew_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainAddEpoch_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainRecvKey_ok_alloc_x himg (slice_concat_2_ok_x hA hRO) hhkdf hA)
    (messageDeserialize_spqrPolyApi_ok_of_contracts_x img A ext hA hStage2.format_inner)
    hFromPb
    hStatesRecv

/-! ## 4. Top-Level `spqr::recv` Composition from Prologue, Decode/Dispatch, and Tails -/

/-- `SepWPpI` execution of `spqr::recv` (`0x5462c`) from entry to `s0.readReg64 .x30` combining
    `step_prologue_to_312` (`Part4.lean`), `step_decode_and_dispatch` (`Part5.lean`), and the 3
    version-branch tail contracts (`V0ChainTail`, `InitInnerTail`, `V1RatchetTailI`). -/
theorem spqrRecv_sepWPpI_of_tails
    (H_inner : V1InnerHeapPred)
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hv0 : V0ChainTail img A F K ext st msg ret s0 R)
    (hinit : InitInnerTail img A F K ext st msg ret s0 R)
    (hv1 : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_prologue_to_312 A F K ext st msg ret s0 P R hpc hrun hsp_align hx0 hx1 hx8 hP
    (fun pre msgPtr s1 P1 hpre hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1 =>
      step_decode_and_dispatch H_inner hC st msg ret pre msgPtr hst_len hpre hvalid
        s0 s1 P1 R hv0 hinit hv1 hsp_align
        hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1)

/-- `spqr::recv` (`0x5462c`) satisfies `spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img` on
    `tripleRatchetProgAtExt img.base ext` given `SpqrRecvContracts` and the 3 version-branch
    tails (`V0ChainTail`, `InitInnerTail`, `V1RatchetTailI`). -/
theorem spqrRecv_ok_of_tails
    (H_inner : V1InnerHeapPred)
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (hv0 : ∀ st msg ret s0 R, V0ChainTail img A F K ext st msg ret s0 R)
    (hinit : ∀ st msg ret s0 R, InitInnerTail img A F K ext st msg ret s0 R)
    (hv1 : ∀ st msg ret s0 R, V1RatchetTailI img A F K ext st msg ret s0 R) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) := by
  refine subroutine_ok_of_sepWPp fun ⟨st, msg, ret⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecExactKey, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hst_len, hmsg_len⟩, hpre⟩
  have hpre1 :
      s0.mem ⊨ ⌜ImgCallInv img s0⌝ ∗
        (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
          (logOff img ∗ TokenInit img ∗
            (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R))) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [ImgCallInv]; ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨hinv0, hpre2⟩
  rw [satisfies_pure_sepConj] at hpre2
  rcases hpre2 with ⟨⟨hx0, hx1, hx8⟩, hmem0⟩
  have hmem_ro :
      s0.mem ⊨ spqrRecvRoAt img.base ∗
        (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
    rodata_spqrRecvRoAt hC.himg hinv0.1 hmem0
  let P0 :=
    spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  have hP0 : s0.mem ⊨ P0 ∗ R :=
    Satisfies.mono (Entails.of_eq (by dsimp only [P0]; ac_rfl)) hmem_ro
  have hwp :=
    spqrRecv_sepWPpI_of_tails H_inner hC st msg ret s0 P0 R hst_len
      (hv0 st msg ret s0 R) (hinit st msg ret s0 R) (hv1 st msg ret s0 R)
      hpc hrun hsp_align hx0 hx1 hx8 rfl hinv0
  refine ⟨P0, R, hP0, fun R' hm' hL => ?_⟩
  obtain ⟨sf, hsteps, hout⟩ := hwp R' hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨hq, hspf, hcsf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom
  · refine Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨fun hmR => ?_, hspf, hcsf⟩⟩
    have hcore := hq hmR
    have hro :
        sf.mem ⊨ spqrRecvRoAt img.base ∗
          (⌜sf.trace = s0.trace ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
            recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
            A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by dsimp only [spqrRecvCorePost]; ac_rfl)) hcore
    have hlt := spqrRecvRoAt_restore hro
    dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecExactKey, Spec.inImage]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hlt
  · exact Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp⟩)
  · exact Or.inr (Or.inr hoom)

/-- Lift `spqrRecv_ok_of_tails` from `tripleRatchetProgAtExt img.base ext` to `Program.ofImage
    img (Rust.withPanics ext)` at `entryOf img spqrRecvName` (matching `tripleRatchetProg img C
    ctl abs` when `ext = tripleRatchetExterns C ctl abs`). -/
theorem spqrRecv_inImage_ok_of_tails
    (H_inner : V1InnerHeapPred)
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (hv0 : ∀ st msg ret s0 R, V0ChainTail img A F K ext st msg ret s0 R)
    (hinit : ∀ st msg ret s0 R, InitInnerTail img A F K ext st msg ret s0 R)
    (hv1 : ∀ st msg ret s0 R, V1RatchetTailI img A F K ext st msg ret s0 R) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  root_of_tripleRatchetProgAtExt hC.himg (spqrRecv_ok_of_tails H_inner hC hv0 hinit hv1)

end CryptoVerification.SpqrV1.Top.Recv
