/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# Relocatable Cryptographic Primitive Bridge (`[LibsignalPlacement]`)

Proves relocatable `[LibsignalPlacement]` contracts for `<PrivateKey>::calculate_agreement` (Block
`207`) and `pqxdhHkdfExpandCellsPlacedSpec` (`k = 8`, `k = 10`, and `k ∉ {8, 10, 12}` on Block
`53`).
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.E2E.Pqxdh.Initiator

/-! ## 1. Relocatable `<PrivateKey>::calculate_agreement` (Block `207`) -/

/-- Base `Spec` (without image layout pins) for `<PrivateKey>::calculate_agreement` (Block `207`)
at the `Initiator.Primitives` abstraction level. -/
def pqxdhCalculateAgreementPlacedBaseSpec (P : Primitives) (A : RustAlloc) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Frozen-invariant variant of `pqxdhCalculateAgreementPlacedBaseSpec` carrying
`Keys.LsFrozenInv pl s` in `pre` for direct calls inside `SepWPp.of_sepWP_lscro` segments. -/
def pqxdhCalculateAgreementPlacedFrozenSpec (P : Primitives) (A : RustAlloc)
    (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜Keys.LsFrozenInv pl s ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStack
  post := (pqxdhCalculateAgreementPlacedBaseSpec P A).post
  onPanic := (pqxdhCalculateAgreementPlacedBaseSpec P A).onPanic

/-- Target predicate for `<PrivateKey>::calculate_agreement` (Block `207`) wrapped in
`withLsCodeRoLoaded lsmpl`. -/
def PqxdhCalculateAgreementPlacedOk [LibsignalPlacement] (P : Primitives) (A : RustAlloc)
    (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (withLsCodeRoLoaded lsmpl (pqxdhCalculateAgreementPlacedBaseSpec P A))

/-- Target predicate for `<PrivateKey>::calculate_agreement` (Block `207`) carrying
`Keys.LsFrozenInv lsmpl` in `pre`. -/
def PqxdhCalculateAgreementPlacedFrozenOk [LibsignalPlacement] (P : Primitives) (A : RustAlloc)
    (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (pqxdhCalculateAgreementPlacedFrozenSpec P A lsmpl)

/-- Relocatable `<PrivateKey>::calculate_agreement` (Block `207`) bridged from
`Keys.calculateAgreement_placed_ok` and `ConsumeMessageKeyTransfer.ct_eq_ro_placed_ok_withLsCodeLoaded`. -/
theorem pqxdhCalculateAgreement_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H Keys.lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H Keys.lsSharedDropSym zeroizeSecretSpec)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H Keys.lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    PqxdhCalculateAgreementPlacedOk P A ((blkPC_207).rebase (blkPl_207).base H) := by
  unfold PqxdhCalculateAgreementPlacedOk
  have hct_213 := ConsumeMessageKeyTransfer.ct_eq_ro_mem_placed_ok_withLsCodeLoaded (H := H) h_bb
  have hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec) :=
    ls_subroutine_ok_of_block hct_213
  have hraw := Keys.calculateAgreement_placed_ok' h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic
  refine subroutine_ok_outcome_intro ?_
  rintro ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [pqxdhCalculateAgreementPlacedBaseSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec C.X A)).pre xg s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret⌝ ∗
          (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion xg.ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStack) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret⌝ ∗
            ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion xg.ret 24 ∗ (A.pool ∗ (stackAt sp calculateAgreementStack ∗ R)))))) := by
      ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hfr, ⟨hx0, hx1, hx8⟩, by ac_nf at hpre ⊢⟩
  refine (hraw.to_outcome xg R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with
    ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec,
      pqxdhCalculateAgreementPlacedBaseSpec] at hq ⊢
    rw [hour_list, htheir_list, hsp_eq] at hq
    have hE := calculateAgreementResultAt_entails_pqxdh hP A ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A ret (calculateAgreement C.X xg.their xg.our) ∗
          (⌜sf.trace = s0.trace⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool ∗ stackAt sp calculateAgreementStack ∗ R) := by
      ac_nf at hq ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Cross-block transfer of `pqxdhCalculateAgreement_placed_ok` to any caller block `i < 619`
(including mutated caller blocks such as Block `79`). -/
theorem pqxdhCalculateAgreement_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H Keys.lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H Keys.lsSharedDropSym zeroizeSecretSpec)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H Keys.lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H Keys.lsHandleAllocErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  keys_ls_subroutine_ok_of_block_cro
    (pqxdhCalculateAgreement_placed_ok hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop hpanic)
    hi (by decide) (by decide)

/-- Lift `PqxdhCalculateAgreementPlacedOk` (`withLsCodeRoLoaded`) to
`PqxdhCalculateAgreementPlacedFrozenOk` (`Keys.LsFrozenInv`). -/
theorem pqxdhCalculateAgreement_placed_frozen_of_cro [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {prog : Program}
    (h : PqxdhCalculateAgreementPlacedOk P A prog) :
    PqxdhCalculateAgreementPlacedFrozenOk P A prog := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  rintro ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hp
  dsimp only [pqxdhCalculateAgreementPlacedFrozenSpec, withLsCodeRoLoaded,
    pqxdhCalculateAgreementPlacedBaseSpec] at hp ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hF, hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hsep⟩
  have hcomm :
      ((⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
          s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
        (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
        memRegion ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStack) ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
            s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((theirA ↦ₛ bytesToBv8 theirPk32) ∗
            (memRegion ret 24 ∗ (A.pool ∗ (stackAt sp calculateAgreementStack ∗ R)))))) := by
    ac_rfl
  rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨⟨hF.code, hF.ro⟩, ⟨hx0, hx1, hx8, hsp_eq, hour, htheir⟩, by ac_nf at hsep ⊢⟩

/-- Cross-block `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem pqxdhCalculateAgreement_placed_frozen_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H Keys.lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H Keys.lsSharedDropSym zeroizeSecretSpec)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H Keys.lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H Keys.lsHandleAllocErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_of_cro
    (pqxdhCalculateAgreement_placed_ok_of_block hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop
      hpanic hi)

/-! ## 2. Relocatable `pqxdhHkdfExpandCellsPlacedSpec` for `k = 8`, `k = 10`, and `k ∉ {8, 10, 12}` -/

private theorem satisfies_withLsCodeLoaded_intro {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by ac_rfl
  rw [hcomm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

/-- `pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8` (`64` B, `info = INFO_RATCHET`) on Block `53`
from `Expand.expand_multi_info_placed_ok`. -/
theorem pqxdhHkdfExpand_8_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8) := by
  have hexp := expand_multi_info_placed_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_RATCHET := by
    rcases hcases with ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
    · exact hinfo
    · omega
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 14 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 64⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, expandMultiInfoSpec, pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- `pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10` (`80` B, `info = INFO_MSG_KEYS`) on Block `53`
from `Expand.expand_multi_info_placed_ok`. -/
theorem pqxdhHkdfExpand_10_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10) := by
  have hexp := expand_multi_info_placed_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 10 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_MSG_KEYS := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩
    · omega
    · exact hinfo
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 18 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 80⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, expandMultiInfoSpec, pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- For any `k ∉ {8, 10, 12}`, `pqxdhHkdfExpandCellsPlacedSpec P lsmpl k` has a contradictory
precondition on any program `prog`. -/
theorem pqxdhHkdfExpand_other_placed_ok [LibsignalPlacement]
    (P : Primitives) (prog : Program) (k : Nat)
    (hk8 : k ≠ 8) (hk10 : k ≠ 10) (hk12 : k ≠ 12) :
    subroutine_ok prog (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl k) := by
  refine subroutine_ok_outcome_intro ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 _ _ hpre _
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.2.2.2.2.2.2.2 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact (hk8 rfl).elim
  · exact (hk10 rfl).elim
  · exact (hk12 rfl).elim

end CryptoVerification.E2E.Pqxdh.ResponderCore
