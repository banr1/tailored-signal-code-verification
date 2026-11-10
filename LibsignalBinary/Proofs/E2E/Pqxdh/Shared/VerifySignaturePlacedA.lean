/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureA
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# Relocatable `VerifySignature` — Hook Bundles, SHA-512 IVs, and Segments 2–3 (Block `204`)

Defines minimal primitive and hook bundles (`VerifySignaturePrims`, `VerifySignaturePlacedHooks`)
decoupled from Block `202` (`PublicKey::is_canonical`), proves `.rodata` SHA-512 IV lemmas under
`LibsignalRoLoaded`, and proves Segments 2 and 3 of unmutated Block `204` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open SignalPqxdh SignalPqxdh.Model

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem calleeSavedVRegs_setPC_pre_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc

private theorem calleeSavedVRegs_setMem_setPC_pre_placed (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_placed calleeSavedVRegs_setMem_setPC_pre_placed

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

/-! ## External Hook and `.rodata` Symbols -/

abbrev lsVerifyMemsetSym : String :=
  "memset"

abbrev lsVerifyMontToEdSym : String :=
  "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"

abbrev lsDalekCompressSym : String :=
  "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress"

abbrev lsDalekEdNegSym : String :=
  "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg"

abbrev lsSha512CompressSym : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512"

abbrev lsDalekScalarWideSym : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide"

abbrev lsDalekScalarModSym : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order"

abbrev lsDalekDoubleMulSym : String :=
  "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint"

abbrev lsVerifySha512IVRoSym : String :=
  "libsignal_core:.rodata..Lanon.2"

/-! ## Minimal Primitive and Hook Bundles -/

/-- Minimal primitive length and reference-equivalence laws required by Blocks `203`
    (`verify_signature`) and `204` (`verify_signature_for_multipart_message`).
    Deliberately omits `isCanonical_eq_isCanonicalRef` so small-subgroup disproofs can
    instantiate `verify_signature` even when `isCanonical` is mutated. -/
structure VerifySignaturePrims (P : Primitives) : Prop where
  sha512Compress_len           : ∀ st blk, (P.sha512Compress st blk).length = 64
  sha512_eq_ref                : ∀ m, P.sha512 m = sha512Ref P m
  sigVerify_eq_xeddsaVerifyRef : ∀ pk m sig, P.sigVerify pk m sig = xeddsaVerifyRef P pk m sig
  scalarFromBytesModOrder_len  : ∀ b, (P.scalarFromBytesModOrder b).length = 32
  scalarFromWide_len           : ∀ b, (P.scalarFromWide b).length = 32
  montToEd_len                 : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160
  edNeg_len                    : ∀ pt, (P.edNeg pt).length = 160
  doubleScalarMulBasepoint_len : ∀ h a s, (P.doubleScalarMulBasepoint h a s).length = 160
  compress_len                 : ∀ pt, (P.compress pt).length = 32

theorem VerifySignaturePrims.of_structuralPrims {P : Primitives}
    (hWF : StructuralPrims P) : VerifySignaturePrims P where
  sha512Compress_len           := hWF.sha512Compress_len
  sha512_eq_ref                := hWF.sha512_eq_ref
  sigVerify_eq_xeddsaVerifyRef := hWF.sigVerify_eq_xeddsaVerifyRef
  scalarFromBytesModOrder_len  := hWF.scalarFromBytesModOrder_len
  scalarFromWide_len           := hWF.scalarFromWide_len
  montToEd_len                 := hWF.montToEd_len
  edNeg_len                    := hWF.edNeg_len
  doubleScalarMulBasepoint_len := hWF.doubleScalarMulBasepoint_len
  compress_len                 := hWF.compress_len

/-- Relocatable external hook contracts required by Blocks `203` and `204` (independent of
    `is_torsion_free` / Block `202`). -/
structure VerifySignaturePlacedHooks (P : Primitives) (H : LibsignalHooks) : Prop where
  memcpy         : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memset         : HookSat H lsVerifyMemsetSym (sessionMemsetSpec pqxdhHookStack)
  blackBox       : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook
  montToEd       : HookSat H lsVerifyMontToEdSym (dalekMontToEdStubSpec P)
  compress       : HookSat H lsDalekCompressSym (cryptoLeafStubSpec P.compress 160 32)
  edNeg          : HookSat H lsDalekEdNegSym (cryptoLeafStubSpec P.edNeg 160 160)
  sha512Compress : HookSat H lsSha512CompressSym
                     (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128)
  scalarWide     : HookSat H lsDalekScalarWideSym (cryptoLeafStubSpec P.scalarFromWide 64 32)
  scalarMod      : HookSat H lsDalekScalarModSym
                     (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32)
  doubleMul      : HookSat H lsDalekDoubleMulSym (dalekDoubleMulStubSpec P)

structure VerifySignaturePlacedHooks' (P : Primitives) (H : LibsignalHooks) : Prop where
  memcpy         : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memset         : HookSat H lsVerifyMemsetSym (sessionMemsetSpec pqxdhHookStack)
  blackBox       : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook
  montToEd       : HookSat H lsVerifyMontToEdSym (dalekMontToEdStubSpecPlaced P)
  compress       : HookSat H lsDalekCompressSym (cryptoLeafStubSpec P.compress 160 32)
  edNeg          : HookSat H lsDalekEdNegSym (cryptoLeafStubSpec P.edNeg 160 160)
  sha512Compress : HookSat H lsSha512CompressSym
                     (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128)
  scalarWide     : HookSat H lsDalekScalarWideSym (cryptoLeafStubSpec P.scalarFromWide 64 32)
  scalarMod      : HookSat H lsDalekScalarModSym
                     (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32)
  doubleMul      : HookSat H lsDalekDoubleMulSym (dalekDoubleMulStubSpecPlaced P)

theorem VerifySignaturePlacedHooks'.of_hooks {P : Primitives} {H : LibsignalHooks}
    (h : VerifySignaturePlacedHooks P H) : VerifySignaturePlacedHooks' P H where
  memcpy         := h.memcpy
  memset         := h.memset
  blackBox       := h.blackBox
  montToEd       := h.montToEd
  compress       := h.compress
  edNeg          := h.edNeg
  sha512Compress := h.sha512Compress
  scalarWide     := h.scalarWide
  scalarMod      := h.scalarMod
  doubleMul      := h.doubleMul

/-! ## Relocatable `.rodata` SHA-512 IV Lemmas -/

private theorem sha512IV_lsroSliceCheck :
    lsroSliceCheck lsVerifySha512IVRoSym 0 sha512IVBytesLE = true := by
  decide

theorem sha512IV_placed_holdsBytes {pl : Obj.MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) :
    Obj.HoldsBytes m (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro) := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    lsro_slice_holds hro sha512IV_lsroSliceCheck

theorem sha512IV_placed_quad0 {pl : Obj.MultiPlacement} {m : Memory}
    (h : Obj.HoldsBytes m (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro)) :
    RoQuad64 m (pl.ρ lsVerifySha512IVRoSym)
      0x6a09e667f3bcc908#64 0xbb67ae8584caa73b#64
      0x3c6ef372fe94f82b#64 0xa54ff53a5f1d36f1#64 := by
  rw [sha512IVBytesLE_eq_unpack64] at h
  exact RoQuad64.of_holdsBytes (holdsBytes_append h).1 rfl

theorem sha512IV_placed_quad1 {pl : Obj.MultiPlacement} {m : Memory}
    (h : Obj.HoldsBytes m (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro)) :
    RoQuad64 m (pl.ρ lsVerifySha512IVRoSym + 32#64)
      0x510e527fade682d1#64 0x9b05688c2b3e6c1f#64
      0x1f83d9abfb41bd6b#64 0x5be0cd19137e2179#64 := by
  rw [sha512IVBytesLE_eq_unpack64] at h
  have h2 := (holdsBytes_append h).2
  have hlen :
      (unpack64 0x6a09e667f3bcc908#64 ++ unpack64 0xbb67ae8584caa73b#64 ++
       unpack64 0x3c6ef372fe94f82b#64 ++ unpack64 0xa54ff53a5f1d36f1#64).length = 32 := rfl
  rw [hlen] at h2
  exact RoQuad64.of_holdsBytes h2 rfl

/-! ## Block `204` Segments 2 and 3 -/

set_option maxHeartbeats 1600000 in
theorem verifySig_seg2_1569_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (_hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗
          ((fsp + 688#64) ↦ₛ bytesToBv8
            (sha512CompressOutBytes P (sha512CompressOutBytes P st0 (pre64 ++ m.take 64))
              ((m.drop 64).take 1408))) ∗
          ((fsp + 752#64) ↦₆₄ 12#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memcpy
  have hsha := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.sha512Compress
  clear hH
  have hlen_m64_bv : (bytesToBv8 (m.take 64)).length = 64 := by simp [bytesToBv8, hm]
  have hlen_m1408 : ((m.drop 64).take 1408).length = 128 * 11 := by simp [hm]
  have hlen_m1408_bv : (bytesToBv8 ((m.drop 64).take 1408)).length = 1408 := by
    simp [bytesToBv8, hm]
  have hlen_m97_bv : (bytesToBv8 (m.drop 1472)).length = 97 := by simp [bytesToBv8, hm]
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_blk0 : (pre64 ++ m.take 64).length = 128 * 1 := by simp [hpre64, hm]
  have hlen_blk0_bv : (bytesToBv8 (pre64 ++ m.take 64)).length = 128 := by
    simp [bytesToBv8, hpre64, hm]
  have hst1_len : (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hm_split : msgPtr ↦ₛ bytesToBv8 m =
      ((msgPtr ↦ₛ bytesToBv8 (m.take 64)) ∗
       ((msgPtr + 64#64) ↦ₛ bytesToBv8 ((m.drop 64).take 1408)) ∗
       ((msgPtr + 1472#64) ↦ₛ bytesToBv8 (m.drop 1472))) := by
    have h1 : m = m.take 64 ++ ((m.drop 64).take 1408 ++ m.drop 1472) := by
      have ha : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
        rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [ha, List.take_append_drop]
    conv => lhs; rw [h1, bytesToBv8_append, bytesToBv8_append]
    rw [pointsToBytes_append, pointsToBytes_append, hlen_m64_bv, hlen_m1408_bv]
    have h64 : BitVec.ofNat 64 64 = 64#64 := rfl
    have h1408 : 64#64 + BitVec.ofNat 64 1408 = 1472#64 := rfl
    rw [h64, BitVec.add_assoc, h1408]
  have hbuf64_in : memRegion (fsp + 624#64) 63 ∗ ((fsp + 687#64) ↦₈ 64#8) ⊢
      memRegion (fsp + 624#64) (bytesToBv8 (m.take 64)).length := by
    rw [hlen_m64_bv, ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 1)
      (b' := fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
    exact sepConj_mono_right (Entails.sepExists_intro 64#8)
  have hbuf128_weaken : ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) ⊢
      memRegion (fsp + 560#64) (bytesToBv8 (m.drop 1472)).length ∗ memRegion (fsp + 657#64) 30 ∗
      (∃∗ b687 : BitVec 8, (fsp + 687#64) ↦₈ b687) := by
    refine Entails.trans (Q := memRegion (fsp + 560#64) 128) ?_ (Entails.of_eq ?_)
    · rw [← hlen_blk0_bv]; exact pointsToBytes_entails_memRegion _ _
    · rw [hlen_m97_bv, ProofLib.memRegion_split' (b := fsp + 560#64) (n := 97) (k := 31)
        (b' := fsp + 657#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 657#64) (n := 30) (k := 1)
        (b' := fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf64_in) (by sep_frame)
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 (m.take 64)⟩
  have hmerge128 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 (m.take 64)) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge128) (by sep_frame)
  wp_steps
  wp_call hsha ⟨fsp + 688#64, st0, fsp + 560#64, pre64 ++ m.take 64, 1⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf128_weaken) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hsha ⟨fsp + 688#64, sha512CompressOutBytes P st0 (pre64 ++ m.take 64), msgPtr + 64#64,
    (m.drop 64).take 1408, 11⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  wp_steps
  wp_call hmemcpy ⟨fsp + 560#64, msgPtr + 1472#64, bytesToBv8 (m.drop 1472)⟩
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split.symm) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by rw [hsp_sf_1, hsp_sf, hsp]; ac_rfl), by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 1600000 in
theorem verifySig_seg2_33_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memcpy
  clear hH
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_m_bv : (bytesToBv8 m).length = 33 := by simp [bytesToBv8, hm]
  have hbuf63_split : memRegion (fsp + 624#64) 63 =
      memRegion (fsp + 624#64) (bytesToBv8 m).length ∗ memRegion (fsp + 657#64) 30 := by
    rw [hlen_m_bv]
    exact ProofLib.memRegion_split' (b := fsp + 624#64) (n := 33) (k := 30) (b' := fsp + 657#64)
      rfl (by bv_omega) (by decide)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf63_split) (by sep_frame)
  wp_steps
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 m⟩
  have hmerge97 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 m) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge97) (by sep_frame)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
/-- Segment 3a of Block `204` (`+548 .. +992`, SHA-512 final padding & `from_bytes_mod_order_wide`)
    under `[LibsignalPlacement]`. -/
theorem verifySig_seg3a_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ fitBv8 32 (P.scalarFromWide (revWords64 (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))))) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemset := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memset
  have hsha := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.sha512Compress
  have hwide := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.scalarWide
  clear hH
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, _p12, _p13, hp1, hp2, hp3⟩ :=
    exists_pad97_cells htail97
  have hst_bv : (bytesToBv8 st).length = 64 := by simp [bytesToBv8, hst]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hw_st⟩ := exists_unpack64_of_length_64 hst_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hp1 (fsp + 560#64))) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hw_st (fsp + 688#64))) (by sep_frame)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply ProofLib.SepWP.replace_pre
    (hPQ := blockBuf_tail32_pack (fsp + 656#64) ((bytesToBv8 tail97).getD 96 0#8) 97#8)
    (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro b12
  apply SepWP.exists_left; intro b13
  apply SepWP.exists_left; intro b14
  apply SepWP.exists_left; intro b15
  apply SepWP.pure_elim; rintro ⟨hb12, hb15⟩
  wp_steps
  have hsp7 : ((fsp + 920#64) ↦₆₄ b15) =
      (((fsp + 920#64) ↦ₛ first7 b15) ∗ ((fsp + 927#64) ↦₈ 97#8)) := by
    rw [cell_split7 (fsp + 920#64) b15, hb15, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7) (by sep_frame)
  wp_steps
  have hunpack32 := blockBuf_tail32_unpack (fsp + 896#64) b12 b13 b14 b15
    ((bytesToBv8 tail97).getD 96 0#8) 97#8 hb12
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunpack32
  apply ProofLib.SepWP.replace_pre (hPQ := hunpack32) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hmemset (fsp + 898#64, 0#8, 30)
  have hp2_896 := hp2 (fsp + 896#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2_896
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp2_896) (by sep_frame)
  wp_steps
  have hbithi : rev64 (BitVec.truncate 64 ((0#64 ++ blkCnt) >>> 54)) = 0#64 := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hbitlo : rev64 (blkCnt <<< 10 ||| 776#64) = rev64 (BitVec.ofNat 64 (8 * L)) := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hL_or : L = 97 ∨ L = 1633 := hblkL.imp And.right And.right
  have hp3_1008 := hp3 (fsp + 1008#64) hL_or
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp3_1008
  have hw_st_928 := (hw_st (fsp + 928#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw_st_928
  wp_simp_pre_fast [hbithi, hbitlo]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hw_st_928) (by sep_frame)
  have hpad_len :
      (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)).length = 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, htail97]
  wp_call hsha ⟨fsp + 928#64, st, fsp + 1008#64, tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L, 1⟩
  have hpad_norm :
      tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L) =
        tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L := by
    simp [List.append_assoc]
  wp_simp_pre_fast [fitBv8_64_sha512CompressOutBytes, hpad_norm]
  have hst_out_len :
      (sha512CompressOutBytes P st
        (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hu_st, hu_rev⟩ :=
    exists_unpack64_revWords64_of_length_64 hst_out_len
  have hu_st_928 := hu_st (fsp + 928#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_st_928
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_st_928) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008.symm) (by sep_frame)
  have hsp7_920 := cell_split7 (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L)))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp7_920
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7_920) (by sep_frame)
  wp_steps
  have hpk7_920 := first7_pack (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L))) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk7_920
  apply ProofLib.SepWP.replace_pre (hPQ := hpk7_920) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro _
  wp_steps
  have hu_rev_1008 := (hu_rev (fsp + 1008#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_rev_1008
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008) (by sep_frame)
  have hrev_len :
      (revWords64 (sha512CompressOutBytes P st
        (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)))).length = 64 :=
    revWords64_length (sha512CompressOutBytes_length P _ _)
  wp_call hwide ⟨fsp + 1008#64, revWords64 (sha512CompressOutBytes P st (tail97 ++ [0x80] ++
    List.replicate 14 0 ++ encodeBitLen128BE L)), fsp + 768#64⟩
  wp_simp_pre_fast [hpad_norm]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008.symm) (by sep_frame)
  have hm560 := cells_16_merge (fsp + 560#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm560
  apply ProofLib.SepWP.replace_pre (hPQ := hm560) (by sep_frame)
  have hm688 := cells_10_merge (fsp + 688#64) w0 w1 w2 w3 w4 w5 w6 w7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm688
  apply ProofLib.SepWP.replace_pre (hPQ := hm688) (by sep_frame)
  have hm800 := cells_16_merge (fsp + 800#64)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm800
  apply ProofLib.SepWP.replace_pre (hPQ := hm800) (by sep_frame)
  have hm928 := cells_10_merge (fsp + 928#64) u0 u1 u2 u3 u4 u5 u6 u7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm928
  apply ProofLib.SepWP.replace_pre (hPQ := hm928) (by sep_frame)
  have hm1008 := cells_16_merge (fsp + 1008#64)
    (rev64 u0) (rev64 u1) (rev64 u2) (rev64 u3) (rev64 u4) (rev64 u5) (rev64 u6) (rev64 u7)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1008
  apply ProofLib.SepWP.replace_pre (hPQ := hm1008) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

private def pqxdhCtEqMemSpec (m : Memory) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s0 =>
    ⌜s0.readReg64 .x0 = p1 ∧ s0.readReg64 .x1 = p2 ∧ s0.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32 ∧ s0.mem = m⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
  post := _root_.CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer.ctEqSliceCellsSpec.post

private theorem pqxdhCtEq_call_ok [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hbb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 213) (pqxdhCtEqMemSpec m) := by
  have hblk : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      _root_.CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer.ctEqSliceCellsSpec := by
    simpa only [ls_blockPlacement_base] using
      _root_.CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer.ct_eq_cells_placed_ok hbb
  exact subroutine_ok_mono (lscall_blk (callerProg := callerProg) hblk hcl hi (by decide) (by decide))
    (fun ⟨p1, k1, p2, k2, sp⟩ R s0 hp => by
      dsimp only [pqxdhCtEqMemSpec] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp with ⟨⟨hx0, hx1, hsp0, hk1, hk2, hm⟩, hspat⟩
      dsimp only [withMemEq, _root_.CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer.ctEqSliceCellsSpec]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hm, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hsp0, hk1, hk2⟩, hspat⟩)
    (fun _ _ _ _ hq => hq)

set_option maxHeartbeats 2400000 in
/-- Segment 3b of Block `204` (`+992 .. +1100`, scalar clamping, `from_bytes_mod_order`,
    `vartime_double_scalar_mul_basepoint`, `compress`, and in-image Block `213` `ct_eq`)
    under `[LibsignalPlacement]`. -/
theorem verifySig_seg3b_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) (s : State) (fsp sigPtr : BitVec 64)
    (sig minusCapA hScalar : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsig : sig.length = 64) (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint hScalar minusCapA sScalar)
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmod := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.scalarMod
  have hdmul := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.doubleMul
  have hcomp := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.compress
  have hbb := hH.blackBox
  clear hH
  apply sepWP_seq_lscl hcl (mid := (blkPl_204).base + 1072#64)
  obtain ⟨q0_lo, q0_hi, q1_lo, q1_hi, hsig_q0, hsig_q1, hbuf_q0, hbuf_q1⟩ :=
    exists_sig_capS_cells hsig
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i v0 v1 v2 v3
  have hsbuf := sClamped_buf_pre (fsp + 800#64) v0 v1 v2 v3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsbuf
  apply ProofLib.SepWP.replace_pre (hPQ := hsbuf) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q0 sigPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq ((hsig_q0 sigPtr).symm.trans (hsig_q1 sigPtr))) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q1 sigPtr).symm) (by sep_frame)
  have hbuf0 := hbuf_q0 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf0
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf0) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply SepWP.exists_left; intro _
  wp_steps
  wp_simp_pre_fast [truncate8_zeroExtend32_and7f]
  have hbuf1 := hbuf_q1 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf1
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf1) (by sep_frame)
  have hsClamped_len :
      ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]).length = 32 := by
    simp [hsig]
  wp_call hmod ⟨fsp + 800#64, (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F],
    fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.scalarFromBytesModOrder_len _)]
  wp_steps
  have hsClamped_bv_len :
      (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := by
    simp [bytesToBv8, hsig]
  have hm160 := pointsToBytes_32_merge_128 (fsp + 800#64) _ hsClamped_bv_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm160
  apply ProofLib.SepWP.replace_pre (hPQ := hm160) (by sep_frame)
  have hsScalar_len :
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 :=
    hWF.scalarFromBytesModOrder_len _
  wp_call hdmul ⟨hScalar, minusCapA,
    P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
      [(List.drop 32 sig).getD 31 0 &&& 127]),
    fsp + 768#64, fsp + 400#64, fsp + 1008#64, fsp + 800#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.doubleScalarMulBasepoint_len _ _ _)]
  wp_steps
  have hsScalar_bv_len :
      (bytesToBv8 (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 32 := by
    simp [bytesToBv8, hWF.scalarFromBytesModOrder_len]
  have hm32_1008 := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hsScalar_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_1008) (by sep_frame)
  have hdmul_len :
      (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 160 :=
    hWF.doubleScalarMulBasepoint_len _ _ _
  wp_call hcomp ⟨fsp + 800#64,
    P.doubleScalarMulBasepoint hScalar minusCapA
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])),
    fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _)]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_call
  have hcteq := pqxdhCtEq_call_ok (callerProg := (blkPC_204).rebase (blkPl_204).base H)
    hbb hcl_call
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_2, hsp_sf_1, hsp_sf, hsp, stackAt_hook_split_48]
  have hcapR_bv_len :
      (bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127]))))).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  have hsig32_bv_len : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  wp_call hcteq (fsp + 1008#64,
    bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])))),
    sigPtr, bytesToBv8 (sig.take 32), fsp)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig).symm)
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_hook_split_48 fsp).symm)
    (by sep_frame)
  have hdmul_bv_len :
      (bytesToBv8 (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127])))).length = 160 := by
    simp [bytesToBv8, hWF.doubleScalarMulBasepoint_len]
  have hm160_800 := pointsToBytes_entails_memRegion_n (fsp + 800#64) _ hdmul_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_800) (by sep_frame)
  have hm32_capR := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hcapR_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_capR) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
    by wp_norm_goal, by wp_norm_goal⟩
  wp_norm_goal
  exact x0_cteq_simplify _ _

end CryptoVerification.E2E.Pqxdh.Shared
