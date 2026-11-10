/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64Ext

/-!
# Separation-Logic Contracts for `spqr::kdf::hkdf_to_slice` and `hkdf_to_vec`

Bridges the `RunsTo` and `RunsToE` execution theorems for `spqr::kdf::hkdf_to_slice` (`0x63284`) to
`subroutine_ok` contracts (in-image, `CliExternsOk`, and `[LibsignalPlacement]`), and discharges
the tail call in `spqr::kdf::hkdf_to_vec` (`0x631c8`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.ChainProofs

export CryptoVerification.SpqrV1.Kdf (hkdfToSliceSpqrSpec HkdfToSliceSpqrOkX)

private theorem ro_outside_rw {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hQPR : m ⊨ Q ∗ (P ∗ R) := by rwa [sepConj_left_comm]
  have hperm : m.perm a = some Perm.rw := hrw.perm_rw hQPR ha_rw
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    hrw.update (IsBlock.memRegion b_rw n_rw) (Nat.le_refl _) hQPR
      (AgreesOutside.rfl' m b_rw n_rw) trivial
  have hm_lf := Satisfies.madvFreeNonFrozen hm_reg
  rw [sepConj_left_comm] at hm_lf
  have hfalse := hro.isLazyFree_false hm_lf ha_ro
  rw [Memory.isLazyFree_madvFreeNonFrozen] at hfalse
  have hin : (a - b_rw).toNat < n_rw := ha_rw
  have hcond : ((some Perm.rw).mapped && !(some Perm.rw).frozen) = true := rfl
  simp only [hin, hperm, decide_true, Bool.true_and, hcond, ↓reduceIte] at hfalse
  cases hfalse

private theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro
  · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

private theorem disjointRegions_of_outside {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨h1, h2⟩
    have h_out := hout a h1
    rw [outsideRegion_iff_not_inRegion] at h_out
    exact h_out h2
  constructor
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₂ ⟨by simp only [InRegion]; omega,
      by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₁ ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
      by simp only [InRegion]; omega⟩

private theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : ℕ} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha
    have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd
    unfold InRegion at ha
    unfold OutsideRegion
    bv_omega
  · exact ro_outside_rw (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

private theorem stackAt_hkdfToSlice (s₀ : State) :
    stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ memRegion (hsp s₀ - 544#64) 1232 := by
  have h1 : stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ stackAt s₀.sp 1232 :=
    ProofLib.stackAt_split_bottom s₀.sp 1232 15152 (by decide)
  have h2 : stackAt s₀.sp 1232 = memRegion (hsp s₀ - 544#64) 1232 := by
    simp only [stackAt, hsp]
    congr 1
    bv_lin
  rw [h1, h2]

theorem hkdfToSlice_fnAddr_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr ChainProofs.hkdfToSliceName = b + 0x5de8c#64 := by
  unfold tripleRatchetProgAtExt ChainProofs.hkdfToSliceName
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x5de8c]

/-- `spqr::kdf::hkdf_to_slice` (`0x63284`, 473 instructions) meets
    `(hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem hkdf_to_slice_spqr_ok_ext (img : Obj.Image) (C : Crypto)
    {abs ext : String → Option (State → State)} [HkdfHooks C.F ext]
    (himg : Obj.Loads libsignalSessionImage img)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f) :
    HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext := by
  unfold HkdfToSliceSpqrOkX
  rw [hkdfToSlice_fnAddr_ext]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  rw [Spec.inImage, hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := NewFromSlice3Proof.rodata_sha256IV_0x837d8 himg hF.roData
  have hread_iv : s0.mem.Readable (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hout_salt_stk : ∀ a, InRegion x.saltA x.salt.length a →
      OutsideRegion (hsp s0 - 544#64) 1232 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have h_hpre : HPre img.base x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pc_eq         := hpc
      status        := hrun
      x0_eq         := hx0
      x1_eq         := hx1
      x2_eq         := hx2
      x3_eq         := hx3
      x4_eq         := hx4
      x5_eq         := hx5
      x6_eq         := hx6
      x7_eq         := hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := ProofLib.base_aligned_of_loads himg
      ro_iv_bytes   := hiv_eq
      ro_iv_read    := hread_iv
      disj_iv_stk   := LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
                         (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
                         (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_okm
      rw_stack      := hrw_stk
      disj_okm_stk  := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned] using hsp_al }
  have hNfs : Nfs3GenRunsToExt img.base C.F ext :=
    fun hpc hstat hlen hiv hb hread_iv hdisj_iv h_out h_stk h_out_stk h_key_stk h_key_out hal =>
      new_from_slice3_gen_runsTo_ext hle hpc hstat hlen hiv hb hread_iv hdisj_iv h_out h_stk h_out_stk h_key_stk h_key_out hal
  refine (hkdf_to_slice_runsTo_ext hNfs h_hpre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [Spec.inImage, hkdfToSliceSpqrSpec, hkdfToSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, Expand.t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [Expand.t1_length, Expand.t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HFrame at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `spqr::kdf::hkdf_to_vec` (`0x631c8`, 47 instructions) meets
    `(hkdfToVecSpec A (spqrHkdfWith C.F)).inImage img`, discharging the `hkdf_to_slice` tail call
    directly via `hkdf_to_slice_spqr_ok_ext`. -/
theorem hkdf_to_vec_spqr_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    {abs ext : String → Option (State → State)} [HkdfHooks C.F ext]
    (himg : Obj.Loads libsignalSessionImage img)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    HkdfToVecOkX img A (spqrHkdfWith C.F) ext :=
  hkdf_to_vec_ok_ext img A (spqrHkdfWith C.F) ext hA hZero
    (hkdf_to_slice_spqr_ok_ext img C himg hle)

/-! ## Contract-Backed (`*Ext`) `subroutine_ok` Proofs (`hkdfToSliceStackExt = 17616` B) -/

export CryptoVerification.SpqrV1.ChainProofs
  (hkdfToSliceStackExt hkdfToSliceSpecExt hkdfToSliceSpqrSpecExt
   HkdfToSliceSpqrOkExt HkdfToSliceOkExt)
export CryptoVerification.SpqrV1.Kdf
  (hkdfToVecStackExt hkdfToVecSpecExt hkdfToVecSpqrSpecExt
   HkdfToVecOkExt HkdfToVecSpqrOkExt)

private theorem bytesAt_readable {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.Readable p bs.length := by
  cases ro
  · exact fun a ha => by
      have hp := (IsBlock.pointsToBytes p bs).permNoLazy_rw hsep ha
      obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hp
      exact ⟨by rw [hrw]; rfl, hlf⟩
  · have hb := IsBlockRO.pointsToBytesRO p bs hle
    exact fun a ha => ⟨hb.perm_r hsep ha, hb.isLazyFree_false hsep ha⟩

private theorem bytesAt_rw_of_false {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hsep : m ⊨ bytesAt false p bs ∗ R) :
    m.RW p bs.length :=
  fun _a ha => (IsBlock.pointsToBytes p bs).permNoLazy_rw hsep ha

private theorem bytesAt_true_outside_false {ro₁ ro₂ : Bool} {p₁ p₂ : BitVec 64}
    {bs₁ bs₂ : List (BitVec 8)} {R : SepProp} {m : Memory}
    (hro₁ : ro₁ = true) (hro₂ : ro₂ = false) (hle₁ : bs₁.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro₁ p₁ bs₁ ∗ (bytesAt ro₂ p₂ bs₂ ∗ R)) :
    ∀ a, InRegion p₁ bs₁.length a → OutsideRegion p₂ bs₂.length a := by
  subst hro₁; subst hro₂
  exact ro_outside_rw (IsBlockRO.pointsToBytesRO p₁ bs₁ hle₁) (IsBlock.pointsToBytes p₂ bs₂) hsep

private def sliceROReg (ro : Bool) (p : BitVec 64) (n : ℕ) : List (BitVec 64 × ℕ) :=
  if ro then [(p, n)] else []

private theorem mem_sliceROReg {r : BitVec 64 × ℕ} {ro : Bool} {p : BitVec 64} {n : ℕ} :
    r ∈ sliceROReg ro p n ↔ ro = true ∧ r = (p, n) := by
  cases ro <;> simp [sliceROReg]

/-- `spqr::kdf::hkdf_to_slice` (473 instructions) meets
    `(hkdfToSliceSpecExt (spqrHkdfWith F)).inImage img` (`HkdfToSliceSpqrOkExt`) on
    `tripleRatchetProgAtExt img.base ext` under `SpqrKdfHooksExt img F ext`. -/
theorem hkdf_to_slice_spqr_ok_of_hooks_ext (img : Obj.Image)
    {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hHooks : SpqrKdfHooksExt img F ext) :
    HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext := by
  have hs : HkdfToSliceExtProof.HkdfStubsExt img F ext :=
    ⟨hHooks, new_from_slice3_gen_runsToE_ext hHooks, finalize_fixed3_gen_runsToE_ext img F ext hHooks⟩
  unfold HkdfToSliceSpqrOkExt
  rw [HkdfToSliceExtProof.hkdfToSlice_fnAddr_lsoff]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  rw [Spec.inImage, hkdfToSliceSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len, hsalt_rw, hikm_rw⟩, hsep⟩
  rw [HkdfToSliceExtProof.stackAt_hkdfToSlice_ext s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 16928#64) 17616
  let roRegs : List (BitVec 64 × ℕ) :=
    sliceROReg x.saltRO x.saltA x.salt.length ++
      sliceROReg x.ikmRO x.ikmA x.ikm.length ++
      sliceROReg x.infoRO x.infoA x.info.length
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ R
  have hro_R : ∀ ro ∈ roRegs, SpqrKdfExt.HasROAt ro R_inv := by
    intro ro hmem
    simp only [roRegs, List.mem_append, mem_sliceROReg] at hmem
    rcases hmem with (⟨hro, rfl⟩ | ⟨hro, rfl⟩) | ⟨hro, rfl⟩
    · dsimp only [R_inv]; rw [hro, bytesAt_true]
      exact SpqrKdfExt.HasROAt.sepConj_left (SpqrKdfExt.HasROAt.pointsToBytesRO (by omega))
    · dsimp only [R_inv]; rw [hro, bytesAt_true]
      exact SpqrKdfExt.HasROAt.sepConj_right
        (SpqrKdfExt.HasROAt.sepConj_left (SpqrKdfExt.HasROAt.pointsToBytesRO (by omega)))
    · dsimp only [R_inv]; rw [hro, bytesAt_true]
      exact SpqrKdfExt.HasROAt.sepConj_right (SpqrKdfExt.HasROAt.sepConj_right
        (SpqrKdfExt.HasROAt.sepConj_left (SpqrKdfExt.HasROAt.pointsToBytesRO (by omega))))
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 16928#64) 17616 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 16928#64) 17616 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 16928#64) 17616 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 16928#64) 17616 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 16928#64) 17616 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 16928#64) 17616 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 16928#64) 17616 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 16928#64) 17616 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_salt : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (bytesAt x.saltRO x.saltA x.salt ∗
        (bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_salt : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (bytesAt x.saltRO x.saltA x.salt ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_ikm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (bytesAt x.ikmRO x.ikmA x.ikm ∗
        (bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_ikm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (bytesAt x.ikmRO x.ikmA x.ikm ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_info : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (bytesAt x.infoRO x.infoA x.info ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_info : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (bytesAt x.infoRO x.infoA x.info ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ memRegion x.okmA x.okmLen ∗
          memRegion (hsp s0 - 16928#64) 17616 ∗ R)) := by ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 16928#64) 17616 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := NewFromSlice3Proof.rodata_sha256IV_0x837d8 himg hF.roData
  have hread_iv : s0.mem.Readable (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    intro a ha; exact ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hout_salt_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hout_salt_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
  have hout_ikm_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
  have hout_ikm_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
  have hout_info_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
  have hout_info_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
  have h_salt_inv : SpqrKdfExt.KdfSliceInv x.saltRO roRegs s0.mem x.saltA x.salt
      (hsp s0 - 16928#64) 17616 x.okmA x.okmLen :=
    { bytes_eq := bytesAt_read (by omega) hsep_salt_stk
      readable := bytesAt_readable (by omega) hsep_salt_stk
      perm_inv := by
        cases hro : x.saltRO
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨bytesAt_rw_of_false (by rwa [hro] at hsep_salt_stk), fun r hr a ha => ?_⟩
          simp only [roRegs, List.mem_append, mem_sliceROReg] at hr
          rcases hr with (⟨h1, rfl⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩
          · rw [hro] at h1; cases h1
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_ikm_salt a ha
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_info_salt a ha
        · simp only [↓reduceIte]
          exact fun a ha => ⟨(x.saltA, x.salt.length),
            by simp [roRegs, mem_sliceROReg, hro], ha⟩
      out_stk := hout_salt_stk
      out_okm := hout_salt_okm }
  have h_ikm_inv : SpqrKdfExt.KdfSliceInv x.ikmRO roRegs s0.mem x.ikmA x.ikm
      (hsp s0 - 16928#64) 17616 x.okmA x.okmLen :=
    { bytes_eq := bytesAt_read (by omega) hsep_ikm_stk
      readable := bytesAt_readable (by omega) hsep_ikm_stk
      perm_inv := by
        cases hro : x.ikmRO
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨bytesAt_rw_of_false (by rwa [hro] at hsep_ikm_stk), fun r hr a ha => ?_⟩
          simp only [roRegs, List.mem_append, mem_sliceROReg] at hr
          rcases hr with (⟨h1, rfl⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_salt_ikm a ha
          · rw [hro] at h1; cases h1
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_info_ikm a ha
        · simp only [↓reduceIte]
          exact fun a ha => ⟨(x.ikmA, x.ikm.length),
            by simp [roRegs, mem_sliceROReg, hro], ha⟩
      out_stk := hout_ikm_stk
      out_okm := hout_ikm_okm }
  have h_info_inv : SpqrKdfExt.KdfSliceInv x.infoRO roRegs s0.mem x.infoA x.info
      (hsp s0 - 16928#64) 17616 x.okmA x.okmLen :=
    { bytes_eq := bytesAt_read (by omega) hsep_info_stk
      readable := bytesAt_readable (by omega) hsep_info_stk
      perm_inv := by
        cases hro : x.infoRO
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨bytesAt_rw_of_false (by rwa [hro] at hsep_info_stk), fun r hr a ha => ?_⟩
          simp only [roRegs, List.mem_append, mem_sliceROReg] at hr
          rcases hr with (⟨h1, rfl⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_salt_info a ha
          · exact bytesAt_true_outside_false h1 hro (by omega) hsep_ikm_info a ha
          · rw [hro] at h1; cases h1
        · simp only [↓reduceIte]
          exact fun a ha => ⟨(x.infoA, x.info.length),
            by simp [roRegs, mem_sliceROReg, hro], ha⟩
      out_stk := hout_info_stk
      out_okm := hout_info_okm }
  have h_hpre : HkdfToSliceExtProof.HPreExt img.base x.saltRO x.ikmRO x.infoRO roRegs
      x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pc_eq        := hpc
      status       := hrun
      x0_eq        := hx0
      x1_eq        := hx1
      x2_eq        := hx2
      x3_eq        := hx3
      x4_eq        := hx4
      x5_eq        := hx5
      x6_eq        := hx6
      x7_eq        := hx7
      salt_lt      := hsalt_lt
      ikm_len      := hikm_len
      info_ge      := hinfo_ge
      info_lt      := hinfo_lt
      okm_len      := hokm_len
      base_al      := ProofLib.base_aligned_of_loads himg
      ro_iv_bytes  := hiv_eq
      ro_iv_read   := hread_iv
      disj_iv_stk  := LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
                        (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm  := LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
                        (by decide) hokm_pos hro_iv hrw_okm
      salt_inv     := h_salt_inv
      salt_ro_le   := fun ht => hsalt_rw.resolve_left (by simp [ht])
      ikm_inv      := h_ikm_inv
      ikm_ro_lt    := fun ht => hikm_rw.resolve_left (by simp [ht])
      info_inv     := h_info_inv
      rw_okm       := hrw_okm
      rw_stack     := hrw_stk
      disj_okm_stk := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      ro_out_stk   := by
        intro r hr a ha
        simp only [roRegs, List.mem_append, mem_sliceROReg] at hr
        rcases hr with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
        · exact hout_salt_stk a ha
        · exact hout_ikm_stk a ha
        · exact hout_info_stk a ha
      ro_out_okm   := by
        intro r hr a ha
        simp only [roRegs, List.mem_append, mem_sliceROReg] at hr
        rcases hr with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
        · exact hout_salt_okm a ha
        · exact hout_ikm_okm a ha
        · exact hout_info_okm a ha
      sp_aligned   := by simpa [State.spAligned] using hsp_al }
  refine (HkdfToSliceExtProof.hkdf_to_slice_runsToE_ext hs hF hsym h_hpre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [Spec.inImage, hkdfToSliceSpecExt]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith F x.salt x.ikm x.info x.okmLen =
      hkdfExpand F (hkdfExtractBytes F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, Expand.t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [Expand.t1_length, Expand.t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HkdfToSliceExtProof.HFrameExt at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 16928#64) 17616 ∗ R_inv) :=
    SpqrKdfExt.S2FrameRO.update_two_blocks_ro hb_okm hb_okm' hb_stk hb_stk hro_R hsep_okm_stk
      hframe_sf ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [HkdfToSliceExtProof.stackAt_hkdfToSlice_ext s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `spqr::kdf::hkdf_to_slice` meets `HkdfToSliceSpqrOkExt` on raw `ext` under `CliExternsOk P A ext`. -/
theorem hkdf_to_slice_spqr_ok_of_externsOk_raw (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P A ext) :
    HkdfToSliceSpqrOkExt img (spqrHkdfWith P.C.F) ext :=
  hkdf_to_slice_spqr_ok_of_hooks_ext img himg (SpqrKdfHooksExt.of_externsOk_raw img hOk)

/-- `spqr::kdf::hkdf_to_slice` meets `HkdfToSliceSpqrOkExt` on `cliExternsWith ext` under
`CliExternsOk P A ext`. -/
theorem hkdf_to_slice_spqr_ok_ext' (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P A ext) :
    HkdfToSliceSpqrOkExt img (spqrHkdfWith P.C.F) (SignalSession.cliExternsWith ext) :=
  hkdf_to_slice_spqr_ok_of_hooks_ext img himg (SpqrKdfHooksExt.of_externsOk img hOk)

private theorem hookSat_allocZeroed_cliExternsWith {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (SignalSession.cliExternsWith ext) allocZeroedName (rustAllocZeroedSpec A) := by
  obtain ⟨f, hf, hok⟩ := hZero
  have hn : E2E.isImagePanicSymbol allocZeroedName = false := by
    simp [E2E.isImagePanicSymbol, allocZeroedName, Rust.isPanicSymbol, E2E.extraImagePanicNames]
  have heq : SignalSession.cliExternsWith ext allocZeroedName = ext allocZeroedName := by
    simp [SignalSession.cliExternsWith, E2E.withImagePanics, hn]
  exact ⟨f, heq.trans hf, hok⟩

/-- `spqr::kdf::hkdf_to_vec` (47 instructions) meets `(hkdfToVecSpecExt A (spqrHkdfWith F)).inImage img`
    (`HkdfToVecOkExt`) under `SpqrKdfHooksExt`, `AllocContractsX`, and `HookSat` for `alloc_zeroed`. -/
theorem hkdf_to_vec_spqr_ok_of_hooks_ext (img : Obj.Image)
    {F : ShaState → List (BitVec 8) → ShaState} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hHooks : SpqrKdfHooksExt img F ext)
    (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    HkdfToVecOkExt img A (spqrHkdfWith F) ext :=
  hkdf_to_vec_ok_extX img A (spqrHkdfWith F) ext hA hZero
    (hkdf_to_slice_spqr_ok_of_hooks_ext img himg hHooks)

/-- `spqr::kdf::hkdf_to_vec` meets `HkdfToVecOkExt` on raw `ext` under `CliExternsOk P A ext`. -/
theorem hkdf_to_vec_spqr_ok_of_externsOk_raw (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P A ext)
    (hA : AllocContractsX img A ext) :
    HkdfToVecOkExt img A (spqrHkdfWith P.C.F) ext :=
  hkdf_to_vec_spqr_ok_of_hooks_ext img A himg
    (SpqrKdfHooksExt.of_externsOk_raw img hOk) hA hOk.allocZeroed

/-- `spqr::kdf::hkdf_to_vec` meets `HkdfToVecOkExt` on `cliExternsWith ext` under
`CliExternsOk P A ext`. -/
theorem hkdf_to_vec_spqr_ok_ext' (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P A ext)
    (hA : AllocContractsX img A (SignalSession.cliExternsWith ext)) :
    HkdfToVecOkExt img A (spqrHkdfWith P.C.F) (SignalSession.cliExternsWith ext) :=
  hkdf_to_vec_spqr_ok_of_hooks_ext img A himg
    (SpqrKdfHooksExt.of_externsOk img hOk) hA (hookSat_allocZeroed_cliExternsWith hOk.allocZeroed)

/-! ## Multi-Placed `[LibsignalPlacement]` Separation Logic Bridges (Blocks `379` & `428`) -/

theorem rodata_sha256IV_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) :
    m.RO NewFromSlice3Proof.spqrSha256IVAddr 32 ∧
    m.readBytes NewFromSlice3Proof.spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
  have hp : lsroPlain NewFromSlice3Proof.spqrSha256IVSym = true := by decide
  have hbs : lsroBytes NewFromSlice3Proof.spqrSha256IVSym =
      (NewFromSlice3Proof.roSecSlice3.drop 64).take 32 := by decide
  obtain ⟨hro32, hrd32⟩ := lsro_read hro hp
  rw [hbs, NewFromSlice3Proof.rodata_sha256IV_0x837d8_bytes] at hro32 hrd32
  have hlen : (shaStateBytes sha256IV).length = 32 :=
    LibsignalSession.CryptoHmacSha256.shaStateBytes_length sha256IV
  rw [hlen] at hro32 hrd32
  exact ⟨hro32, hrd32⟩

/-- Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
    `withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))` on
    `(blkPC_379).rebase (blkPl_379).base H`. -/
theorem hkdf_to_slice_spqr_placed_ok [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable (NewFromSlice3Proof.nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [NewFromSlice3Proof.nfs3PlacedFakeB_add_iv]
    exact fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hout_salt_stk : ∀ a, InRegion x.saltA x.salt.length a →
      OutsideRegion (hsp s0 - 544#64) 1232 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have h_hpre : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0
      NewFromSlice3Proof.nfs3PlacedFakeB (LibsignalCodeLoaded lsmpl s0.mem) :=
    { pc_eq         := by
        rw [hkdfCodeFakeB, bv_sub_add_lit_ge _ 0x5de8c 0x5de8c (by decide)]
        simpa using hpc
      status        := hrun
      x0_eq         := hx0
      x1_eq         := hx1
      x2_eq         := hx2
      x3_eq         := hx3
      x4_eq         := hx4
      x5_eq         := hx5
      x6_eq         := hx6
      x7_eq         := hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := hcl
      ro_iv_bytes   := by rw [NewFromSlice3Proof.nfs3PlacedFakeB_add_iv]; exact hiv_eq
      ro_iv_read    := hread_iv
      disj_iv_stk   := by
        rw [NewFromSlice3Proof.nfs3PlacedFakeB_add_iv]
        exact LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
          (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [NewFromSlice3Proof.nfs3PlacedFakeB_add_iv]
        exact LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
          (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_okm
      rw_stack      := hrw_stk
      disj_okm_stk  := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned] using hsp_al }
  have hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      NewFromSlice3Proof.nfs3PlacedFakeB (blkPl_402).base (LibsignalCodeLoaded lsmpl) C.F := by
    intro s_nfs hpc_nfs hstat_nfs hlen_nfs hiv_nfs hcl_nfs hread_iv_nfs hdisj_iv_nfs
      h_out_nfs h_stk_nfs h_out_stk_nfs h_key_stk_nfs _ hal_nfs
    rw [NewFromSlice3Proof.nfs3PlacedFakeB_add_iv] at hiv_nfs hread_iv_nfs hdisj_iv_nfs
    exact new_from_slice3_gen_placed_runsTo_of_other_block C H hcl_nfs hpc_nfs hstat_nfs
      hlen_nfs hiv_nfs hread_iv_nfs hdisj_iv_nfs h_out_nfs h_stk_nfs h_out_stk_nfs
      h_key_stk_nfs hal_nfs
  refine (hkdf_to_slice_placed_runsTo hH.memcpy hH.memset hH.compress256 hNfs h_hpre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeRoLoaded]
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, Expand.t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [Expand.t1_length, Expand.t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HFrame at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- Any caller block `i < 619` can invoke Block `379` (`spqr::kdf::hkdf_to_slice`) at
`lsmpl.base 379` under `withLsCodeRoLoaded lsmpl`. -/
theorem hkdf_to_slice_spqr_placed_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_placed_ok C) hi

/-- Block `378` (`spqr::kdf::hkdf_to_vec`, 47 instructions) meets
    `withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))`, discharging the
    `hkdf_to_slice` tail call directly via `hkdf_to_slice_spqr_placed_ok_of_other_block`. -/
theorem hkdf_to_vec_spqr_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (h_panic : H Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H Alloc.spqrRustNoAllocShimSym noAllocShimSpec)
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedSpec A)) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H) (blkPl_378).base
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))) :=
  hkdf_to_vec_placed_ok A (spqrHkdfWith C.F) h_panic hshim hZero
    (hkdf_to_slice_spqr_placed_ok_of_other_block C)

/-- Any caller block `i < 619` can invoke Block `378` (`spqr::kdf::hkdf_to_vec`) at
`lsmpl.base 378` under `withLsCodeRoLoaded lsmpl`. -/
theorem hkdf_to_vec_spqr_placed_ok_of_other_block [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (h_panic : H Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H Alloc.spqrRustNoAllocShimSym noAllocShimSpec)
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_vec_spqr_placed_ok C A h_panic hshim hZero) hi

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
