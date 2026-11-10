/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon

/-!
# Inner-Hash Segments of Contract-Backed `finalize_fixed` (`0x6ce50`)

Proves the inner-hash segments of `finalize_fixed3_gen_runsToE_ext` from `SpqrKdfHooksExt img C.F ext`
at `finalizeFixed3StackExt` (`16528` B), covering both `< 56` one-block and `[56, 64)` two-block
inner padding over `HmacStN`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout
open ProofLib.ProgramReflection
open SpqrKdfExt

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% finalizeFixed3Name) → (ls_off% finalizeFixed3Name + 444)]

namespace FinalizeFixed3ExtProof

@[local simp, local arm64_norm]
theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

/-- Bundled preconditions of `finalize_fixed [local#3]` (`hex:6ce50`) with `key.length ≤ 64`,
`tail.length < 64`, and `16528`-byte stack (`144 + 16384`). -/
structure FinPre3PfxGenExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 : State) : Prop where
  frz          : img.FrozenLoaded s0
  sym          : s0.symtab = img.symtab
  pc_eq        : s0.pc = img.base + bv% (ls_off% finalizeFixed3Name)
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  tail_lt      : tail.length < 64
  hmac_st      : HmacStN s0.mem (s0.readReg64 .x1) F key pfx tail
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 16528#64) 16528
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 16528#64) 16528
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 16528#64) 16528
  sp_aligned   : (s0.sp &&& 15#64) = 0#64

abbrev FinRegsExt (s0 : State) : List (BitVec 64 × ℕ) :=
  [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)]

structure FinCommonExt (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 64#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : S2Frame s0.mem s.mem (FinRegsExt s0)

theorem rw_fsp144_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.sp - 16528#64) 16528) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.sp - 144#64) 144 := by
  have hrw : RW m (s0.sp - 16528#64) 16528 := hf.rw_of_rw _ _ hrw0
  exact hrw.sub (by bv_omega)

theorem rw_hm_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.readReg64 .x1) 0x90) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.readReg64 .x1) 0x90 :=
  hf.rw_of_rw _ _ hrw0

theorem rw_out_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.readReg64 .x0) 32) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.readReg64 .x0) 32 :=
  hf.rw_of_rw _ _ hrw0

theorem s2frame_seg2a {s0 : State} {m1 m2 m3 m4 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.sp - 144#64) 64)
    (hag2 : AgreesOutside m2 m3 (s0.readReg64 .x1) 64)
    (hag3 : AgreesOutside m3 m4 (s0.sp - 144#64) 64) :
    S2Frame s0.mem m4 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside_sub hf (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  exact S2Frame.trans_agreesOutside_sub hf2 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag3

theorem s2frame_seg3a {s0 : State} {m1 m2 m3 m4 m5 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.readReg64 .x1) 64)
    (hag2 : AgreesOutside m2 m3 (s0.sp - 144#64) 64)
    (hag3 : AgreesOutside m3 m4 (s0.readReg64 .x1) 64)
    (hag4 : AgreesOutside m4 m5 (s0.sp - 144#64) 64) :
    S2Frame s0.mem m5 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside_sub hf (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  have hf3 := S2Frame.trans_agreesOutside_sub hf2 (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag3
  exact S2Frame.trans_agreesOutside_sub hf3 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag4

theorem s2frame_seg4a {s0 : State} {m1 m2 m3 m4 m5 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.readReg64 .x1) 0x90)
    (hag2 : AgreesOutside m2 m3 (s0.sp - 144#64) 64)
    (hag3 : AgreesOutside m3 m4 (s0.readReg64 .x1) 0x90)
    (hag4 : AgreesOutside m4 m5 (s0.readReg64 .x0) 32) :
    S2Frame s0.mem m5 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside hf (by simp [FinRegsExt]) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  have hf3 := S2Frame.trans_agreesOutside hf2 (by simp [FinRegsExt]) hag3
  exact S2Frame.trans_agreesOutside hf3 (by simp [FinRegsExt]) hag4

theorem s2frame_hook_hm_sub {s0 : State} {m1 m2 : Memory} {off : BitVec 64} {sz : ℕ}
    (hf1 : S2Frame s0.mem m1 (FinRegsExt s0))
    (hf2 : S2Frame m1 m2 [(s0.readReg64 .x1 + off, sz), ((s0.sp - 144#64) - 16384#64, 16384)])
    (hoff : off.toNat + sz ≤ 0x90) :
    S2Frame s0.mem m2 (FinRegsExt s0) := by
  refine hf1.trans (hf2.mono fun a ha r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have h_hm := ha (s0.readReg64 .x1, 0x90) (by simp [FinRegsExt])
    simp only [OutsideRegion] at h_hm ⊢; bv_omega
  · have h_stk := ha (s0.sp - 16528#64, 16528) (by simp [FinRegsExt])
    simp only [OutsideRegion] at h_stk ⊢; bv_omega

/-- Cut `F0p` at `img.base + hex:6ce6c` (7 steps after entry): prologue complete. -/
structure StateF0p (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 28)
  common  : FinCommonExt s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStN s.mem (s0.readReg64 .x1) F key pfx tail

theorem seg1a_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s0 (StateF0p img F key pfx tail s0) := by
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp.sub (by bv_omega)
  iterate 7 fin3_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s0.mem
      (((((((((s0.mem.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19))
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  have hd_fsp_hm : DisjointRegions (s0.sp - 144#64) 144 (s0.readReg64 .x1) 0x90 :=
    (hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩).symm
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg
          sp_eq := by fin3_reg
          x29_eq := by fin3_reg
          x26_eq := by fin3_reg
          x27_eq := by fin3_reg
          x28_eq := by fin3_reg
          saved := ⟨by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved⟩
          frame := by
            rw [mem_setMem]
            exact S2Frame.trans_agreesOutside_sub (S2Frame.refl s0.mem (FinRegsExt s0))
              (rbase := s0.sp - 16528#64) (rlen := 16528) (by simp [FinRegsExt]) (by bv_omega) hag }
      x0_eq := by fin3_reg
      x1_eq := by fin3_reg
      hmac_st := by rw [mem_setMem]; exact HmacStN.of_agreesOutside hpre.hmac_st hag hd_fsp_hm }

/-- Cut `F1` at `img.base + hex:6ce9c` (after `memset`): buffer `hm[0..64]` holds `innerPadBlock1 tail`. -/
structure StateF1 (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 76)
  common  : FinCommonExt s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - tail.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 = innerPadBlock1 tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem seg1b_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF0p img F key pfx tail s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF1 img F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hpfx_mod, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  have h12 : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "memset") ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .lr = img.base + bv% (ls_off% finalizeFixed3Name + 76) ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64 ∧
      (s_bl.readReg64 .x1).truncate 8 = 0#8 ∧
      s_bl.readReg64 .x2 = BitVec.ofNat 64 (63 - tail.length) ∧
      s_bl.readReg64 .x19 = s0.readReg64 .x0 ∧
      s_bl.readReg64 .x20 = s0.readReg64 .x1 ∧
      s_bl.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64 ∧
      s_bl.readReg64 .x22 = 0x80#64 ∧
      s_bl.readReg64 .x23 = BitVec.ofNat 64 tail.length ∧
      s_bl.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64) ∧
      s_bl.readReg64 .x25 = BitVec.ofNat 64 (63 - tail.length) ∧
      s_bl.readReg64 .x26 = s0.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s0.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s0.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s0.sp - 144#64 + 64#64 ∧
      s_bl.mem = s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 128#8) := by
    iterate 12 fin3_step
    refine RunsTo.refl ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by simp (config := { decide := true }) only [State.readReg64_setMem, arm64_norm],
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      mem_setMem _ _⟩
  refine RunsToE.trans_frozen hfrz hsym (runsTo_toE h12) fun s_bl hfrz_bl hsym_bl hbl => ?_
  rcases hbl with ⟨hpc_bl, hstat_bl, hsp_bl, hlr_bl, hx0_bl, hx1_bl, hx2_bl,
    hx19_bl, hx20_bl, hx21_bl, hx22_bl, hx23_bl, hx24_bl, hx25_bl,
    hx26_bl, hx27_bl, hx28_bl, hx29_bl, hmem_bl⟩
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64
  set n := 63 - tail.length
  have hx2_nat : (s_bl.readReg64 .x2).toNat = n := by
    rw [hx2_bl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrw_dst : s_bl.mem.RW dst n := by
    rw [hmem_bl]
    refine Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    dsimp only [dst, n]; have := hpre.tail_lt; bv_omega
  have hrw_hstk : s_bl.mem.RW (s_bl.sp - 16384#64) 16384 := by
    rw [hmem_bl, hsp_bl]
    exact Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_stk.sub (by bv_omega))
  have hd_dst_hstk : DisjointRegions dst n (s_bl.sp - 16384#64) 16384 := by
    have hd_hm := hpre.disj_hm_fsp
    unfold DisjointRegions at hd_hm ⊢
    rw [hsp_bl]
    dsimp only [dst, n]
    have := hpre.tail_lt
    bv_omega
  have hal_bl : (s_bl.sp &&& 15#64) = 0#64 := by
    rw [hsp_bl]; exact fsp_aligned hpre.sp_aligned
  refine (memset_subroutine_runsTo hHooks.memset hfrz_bl hsym_bl hpc_bl hstat_bl hx0_bl hx1_bl hx2_nat
    hrw_dst hrw_hstk hd_dst_hstk hal_bl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hstat_sf, hcc_sf, _, hdst_sf, hframe_sf⟩
  rcases hcc_sf with ⟨hsp_cc, hx19_cc, hx20_cc, hx21_cc, hx22_cc, hx23_cc, hx24_cc, hx25_cc, hx26_cc, hx27_cc, hx28_cc, hx29_cc, _⟩
  have hag_w8 : AgreesOutside s.mem s_bl.mem (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 := by
    rw [hmem_bl]; agrees_outside_writes
  have hframe_bl : S2Frame s0.mem s_bl.mem (FinRegsExt s0) :=
    S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
      (by simp [FinRegsExt]) (by have := hpre.tail_lt; bv_omega) hag_w8
  have hframe_sf' : S2Frame s_bl.mem sf.mem
      [(s0.readReg64 .x1 + (BitVec.ofNat 64 tail.length + 1#64), n),
       ((s0.sp - 144#64) - 16384#64, 16384)] := by
    have heq_dst : dst = s0.readReg64 .x1 + (BitVec.ofNat 64 tail.length + 1#64) := by
      dsimp only [dst]; bv_lin
    rw [← heq_dst, ← hsp_bl]; exact hframe_sf
  have hframe_tot : S2Frame s0.mem sf.mem (FinRegsExt s0) := by
    refine s2frame_hook_hm_sub hframe_bl hframe_sf' ?_
    dsimp only [n]; have := hpre.tail_lt; bv_omega
  let m_ref := s_bl.mem.writeBytes dst (List.replicate n 0#8)
  have hlen_rep : (List.replicate n 0#8).length = n := List.length_replicate
  have hag_on : AgreesOn (fun a => ((s_bl.mem.perm a).r = true ∧ s_bl.mem.isLazyFree a = false) ∧
      OutsideRegion (s_bl.sp - 16384#64) 16384 a) sf.mem m_ref := by
    have hdst_sf' : sf.mem.readBytes dst (List.replicate n 0#8).length = List.replicate n 0#8 := by
      rw [hlen_rep]; exact hdst_sf
    have hfr' : S2Frame s_bl.mem sf.mem
        [(dst, (List.replicate n 0#8).length), (s_bl.sp - 16384#64, 16384)] := by
      rw [hlen_rep]; exact hframe_sf
    exact AgreesOn.of_s2Frame_writeBytes hdst_sf' hfr' (by rw [hlen_rep]; omega)
  have hP_hm : ∀ a, InRegion (s0.readReg64 .x1) 0x90 a →
      ((s_bl.mem.perm a).r = true ∧ s_bl.mem.isLazyFree a = false) ∧ OutsideRegion (s_bl.sp - 16384#64) 16384 a := by
    intro a ha
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_hm a ha)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hmem_bl, Memory.perm_write8, hperm_a]; rfl
    · rw [hmem_bl]; exact Memory.isLazyFree_write8_of_false _ _ hlf_a
    · rw [hsp_bl, show (s0.sp - 144#64) - 16384#64 = s0.sp - 16528#64 by bv_lin]
      exact (hpre.disj_hm_fsp.sub_right (s0.sp - 16528#64) ⟨by decide, by bv_omega⟩).symm.outside ha (by decide)
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      ((s_bl.mem.perm a).r = true ∧ s_bl.mem.isLazyFree a = false) ∧ OutsideRegion (s_bl.sp - 16384#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_stk a ha_stk)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hmem_bl, Memory.perm_write8, hperm_a]; rfl
    · rw [hmem_bl]; exact Memory.isLazyFree_write8_of_false _ _ hlf_a
    · rw [hsp_bl]; unfold InRegion at ha; unfold OutsideRegion; bv_omega
  have hag_ref : AgreesOutside s.mem m_ref (s0.readReg64 .x1) 64 := by
    dsimp only [m_ref, dst, n]; rw [hmem_bl]
    exact agreesOutside_pad_memset_lt64 s.mem (s0.readReg64 .x1) tail hpre.tail_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := hpc_sf.trans hlr_bl
      common :=
        { status := hstat_sf
          sp_eq := hsp_cc.trans hsp_bl
          x29_eq := hx29_cc.trans hx29_bl
          x26_eq := hx26_cc.trans hx26_bl
          x27_eq := hx27_cc.trans hx27_bl
          x28_eq := hx28_cc.trans hx28_bl
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_ref hd_hm64_fsp) hP_saved
          frame := hframe_tot }
      x19_eq := hx19_cc.trans hx19_bl
      x20_eq := hx20_cc.trans hx20_bl
      x21_eq := hx21_cc.trans hx21_bl
      x22_eq := hx22_cc.trans hx22_bl
      x23_eq := hx23_cc.trans hx23_bl
      x24_eq := hx24_cc.trans hx24_bl
      x25_eq := hx25_cc.trans hx25_bl
      buf_eq := (hag_on.readBytes_eq (s0.readReg64 .x1) 64 (by decide)
          (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
        (by dsimp only [m_ref, dst, n]; rw [hmem_bl]
            exact readBytes_64_after_pad_memset_lt64 s.mem (s0.readReg64 .x1) tail hmsg_eq hpre.tail_lt)
      ist_eq := (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x40#64) 32 (by decide)
          (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
        ((hag_ref.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x68#64) 32 (by decide)
          (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
        ((hag_ref.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (hag_on.read64_eq (s0.readReg64 .x1 + 0x88#64)
          (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
        ((hag_ref.read64_eq hd_hm64_obl).trans hobl_eq) }

/-! ### Unified Cut `F3Gen` at `hex:6cf04` (Shared Exit for `< 56` and `[56, 64)`) -/

structure StateF3Gen (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (h_in : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 180)
  common  : FinCommonExt s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes h_in
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem step_inner_compress256 {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {st : ShaState} {blk : List (BitVec 8)} {lr_off : BitVec 64} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hbl : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s_bl.readReg64 .lr = img.base + lr_off ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64 ∧
      s_bl.readReg64 .x1 = s0.sp - 144#64 ∧
      s_bl.readReg64 .x2 = 1#64 ∧
      s_bl.readReg64 .x19 = s.readReg64 .x19 ∧
      s_bl.readReg64 .x20 = s.readReg64 .x20 ∧
      s_bl.readReg64 .x21 = s.readReg64 .x21 ∧
      s_bl.readReg64 .x22 = s.readReg64 .x22 ∧
      s_bl.readReg64 .x23 = s.readReg64 .x23 ∧
      s_bl.readReg64 .x24 = s.readReg64 .x24 ∧
      s_bl.readReg64 .x26 = s.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s.readReg64 .x29 ∧
      s_bl.mem = s.mem))
    (hcom : FinCommonExt s0 s)
    (hist : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes st)
    (hblk : s.mem.readBytes (s0.sp - 144#64) 64 = blk)
    (hblk_len : blk.length = 64)
    (host : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hobl : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun sf =>
      sf.pc = img.base + lr_off ∧
      FinCommonExt s0 sf ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧
      sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = s.readReg64 .x23 ∧
      sf.readReg64 .x24 = s.readReg64 .x24 ∧
      sf.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (F st blk) ∧
      sf.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
      sf.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64) := by
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  refine RunsToE.trans_frozen hfrz hsym (runsTo_toE hbl) fun s_bl hfrz_bl hsym_bl hs_bl => ?_
  rcases hs_bl with ⟨hpc_bl, hlr_bl, hstat_bl, hsp_bl, hx0_bl, hx1_bl, hx2_bl,
    hx19_bl, hx20_bl, hx21_bl, hx22_bl, hx23_bl, hx24_bl, hx26_bl, hx27_bl, hx28_bl, hx29_bl, hmem_bl⟩
  have hrw_ist : s_bl.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := by
    rw [hmem_bl]; exact hrw_hm.sub (by bv_omega)
  have hrw_blk : s_bl.mem.RW (s0.sp - 144#64) 64 := by
    rw [hmem_bl]; exact hrw_stk.sub (by bv_omega)
  have hrw_hstk : s_bl.mem.RW (s_bl.sp - 16384#64) 16384 := by
    rw [hmem_bl, hsp_bl]; exact hrw_stk.sub (by bv_omega)
  have hd_ist_blk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_hstk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s_bl.sp - 16384#64) 16384 := by
    rw [hsp_bl]
    exact (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_blk_hstk : DisjointRegions (s0.sp - 144#64) 64 (s_bl.sp - 16384#64) 16384 := by
    rw [hsp_bl]; unfold DisjointRegions; bv_omega
  have hal_bl : (s_bl.sp &&& 15#64) = 0#64 := by
    rw [hsp_bl]; exact fsp_aligned hpre.sp_aligned
  have hist_bl : s_bl.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes st := by
    rw [hmem_bl]; exact hist
  have hblk_bl : s_bl.mem.readBytes (s0.sp - 144#64) 64 = blk := by
    rw [hmem_bl]; exact hblk
  refine (compress256_one_subroutine_runsTo hHooks.compress256 (by decide) hfrz_bl hsym_bl hpc_bl hstat_bl hx0_bl hx1_bl
    hx2_bl hist_bl hblk_bl hrw_ist hrw_blk hrw_hstk
    hd_ist_blk hd_ist_hstk hd_blk_hstk hal_bl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hstat_sf, hcc_sf, hist_sf, _, hframe_sf⟩
  rcases hcc_sf with ⟨hsp_cc, hx19_cc, hx20_cc, hx21_cc, hx22_cc, hx23_cc, hx24_cc, _, hx26_cc, hx27_cc, hx28_cc, hx29_cc, _⟩
  have hframe_s : S2Frame s.mem sf.mem
      [(s0.readReg64 .x1 + 0x40#64, 32), ((s0.sp - 144#64) - 16384#64, 16384)] := by
    rw [← hmem_bl, ← hsp_bl]; exact hframe_sf
  have hframe_tot : S2Frame s0.mem sf.mem (FinRegsExt s0) :=
    s2frame_hook_hm_sub hframe hframe_s (by bv_omega)
  set out_st := shaStateBytes (F st blk)
  have hlen_st : out_st.length = 32 := shaStateBytes_length _
  have hag_on : AgreesOn (fun a => ((s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false) ∧
      OutsideRegion ((s0.sp - 144#64) - 16384#64) 16384 a) sf.mem
      (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) out_st) := by
    have hist_sf' : sf.mem.readBytes (s0.readReg64 .x1 + 0x40#64) out_st.length = out_st := by
      rw [hlen_st]; exact hist_sf
    have hfr' : S2Frame s.mem sf.mem
        [(s0.readReg64 .x1 + 0x40#64, out_st.length), ((s0.sp - 144#64) - 16384#64, 16384)] := by
      rw [hlen_st]; exact hframe_s
    exact AgreesOn.of_s2Frame_writeBytes hist_sf' hfr' (by rw [hlen_st]; decide)
  have hag_wb : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) out_st)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    rw [← hlen_st]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ out_st
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      ((s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false) ∧ OutsideRegion ((s0.sp - 144#64) - 16384#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_stk a ha_stk)
    refine ⟨⟨?_, hlf_a⟩, by unfold InRegion at ha; unfold OutsideRegion; bv_omega⟩
    rw [hperm_a]; rfl
  have hP_hm : ∀ a, InRegion (s0.readReg64 .x1) 0x90 a →
      ((s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false) ∧ OutsideRegion ((s0.sp - 144#64) - 16384#64) 16384 a := by
    intro a ha
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_hm a ha)
    refine ⟨⟨by rw [hperm_a]; rfl, hlf_a⟩, ?_⟩
    rw [show (s0.sp - 144#64) - 16384#64 = s0.sp - 16528#64 by bv_lin]
    exact (hpre.disj_hm_fsp.sub_right (s0.sp - 16528#64) ⟨by decide, by bv_omega⟩).symm.outside ha (by decide)
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨hpc_sf.trans hlr_bl,
    { status := hstat_sf
      sp_eq := hsp_cc.trans hsp_bl
      x29_eq := hx29_cc.trans (hx29_bl.trans hx29)
      x26_eq := hx26_cc.trans (hx26_bl.trans hx26)
      x27_eq := hx27_cc.trans (hx27_bl.trans hx27)
      x28_eq := hx28_cc.trans (hx28_bl.trans hx28)
      saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_wb hd_ist_saved) hP_saved
      frame := hframe_tot },
    hx19_cc.trans hx19_bl,
    hx20_cc.trans hx20_bl,
    hx21_cc.trans hx21_bl,
    hx22_cc.trans hx22_bl,
    hx23_cc.trans hx23_bl,
    hx24_cc.trans hx24_bl,
    hist_sf,
    (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x68#64) 32 (by decide)
      (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
      ((hag_wb.readBytes_eq hd_ist_ost (by decide)).trans host),
    (hag_on.read64_eq (s0.readReg64 .x1 + 0x88#64)
      (fun a ha => hP_hm a (by unfold InRegion at ha ⊢; bv_omega))).trans
      ((hag_wb.read64_eq hd_ist_obl).trans hobl)⟩

/-! ### `< 56` One-Block Inner Path (`hex:6ce9c → hex:6cf04`) -/

structure StateF2 (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 176)
  common  : FinCommonExt s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlockN (1 + pfx.length / 64) tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem seg2a_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hlt56 : tail.length < 56)
    (hs : StateF1 img F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF2 img F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hlt56
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq (b := 1 + pfx.length / 64) hlt56
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 fin3_step
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 fin3_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by rw [mem_setMem]; exact s2frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        have hbuf' : s.mem.readBytes (s0.readReg64 .x1) 64 =
            tail ++ [0x80#8] ++ List.replicate (63 - tail.length) 0#8 := hbuf
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) tail hbuf' hlt56]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

theorem seg2b_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hlt56 : tail.length < 56)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF2 img F key pfx tail s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateF3Gen img F key
        (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
          (innerLastBlockN (1 + pfx.length / 64) tail)) s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  have hstat := hcom.status
  have hsp := hcom.sp_eq
  have hbl : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s_bl.readReg64 .lr = img.base + bv% (ls_off% finalizeFixed3Name + 180) ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64 ∧
      s_bl.readReg64 .x1 = s0.sp - 144#64 ∧
      s_bl.readReg64 .x2 = 1#64 ∧
      s_bl.readReg64 .x19 = s.readReg64 .x19 ∧
      s_bl.readReg64 .x20 = s.readReg64 .x20 ∧
      s_bl.readReg64 .x21 = s.readReg64 .x21 ∧
      s_bl.readReg64 .x22 = s.readReg64 .x22 ∧
      s_bl.readReg64 .x23 = s.readReg64 .x23 ∧
      s_bl.readReg64 .x24 = s.readReg64 .x24 ∧
      s_bl.readReg64 .x26 = s.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s.readReg64 .x29 ∧
      s_bl.mem = s.mem) := by
    fin3_step
    exact RunsTo.refl ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, rfl⟩
  refine (step_inner_compress256 hHooks hpre hfrz hsym hbl hcom hist hblk
    (innerLastBlockN_length hlt56) host hobl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hcom_sf, hx19_sf, hx20_sf, hx21_sf, hx22_sf, _, _, hist_sf, host_sf, hobl_sf⟩
  exact ⟨hpc_sf, hcom_sf, hx19_sf.trans hx19, hx20_sf.trans hx20,
    hx21_sf.trans hx21, hx22_sf.trans hx22, hist_sf, host_sf, hobl_sf⟩

/-! ### `[56, 64)` Two-Block Inner Path (`hex:6ce9c → hex:6cf04`) -/

structure StateF2a (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 112)
  common  : FinCommonExt s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerPadBlock1 tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem seg2_two_a_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hge : 56 ≤ tail.length)
    (hs : StateF1 img F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF2a img F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_ge_56 hge hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 7 fin3_step
  have hread32 := fun u0 u1 u2 u3 =>
    read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 =>
    read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 =>
    read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 48#64 (by decide) hd_hm64_fsp64
  have hread56 := fun u0 u1 u2 u3 =>
    read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 56#64 (by decide) hd_hm64_fsp64
  iterate 2 fin3_step
  clear hread32 hread40 hread48 hread56
  refine RunsTo.refl ?_
  have hag : AgreesOutside s.mem
      ((((((((s.mem.write64 (s0.sp - 144#64) (s.mem.read64 (s0.readReg64 .x1))).write64
        (s0.sp - 144#64 + 8#64) (s.mem.read64 (s0.readReg64 .x1 + 8#64))).write64
        (s0.sp - 144#64 + 16#64) (s.mem.read64 (s0.readReg64 .x1 + 16#64))).write64
        (s0.sp - 144#64 + 24#64) (s.mem.read64 (s0.readReg64 .x1 + 24#64))).write64
        (s0.sp - 144#64 + 32#64) (s.mem.read64 (s0.readReg64 .x1 + 32#64))).write64
        (s0.sp - 144#64 + 40#64) (s.mem.read64 (s0.readReg64 .x1 + 40#64))).write64
        (s0.sp - 144#64 + 48#64) (s.mem.read64 (s0.readReg64 .x1 + 48#64))).write64
        (s0.sp - 144#64 + 56#64) (s.mem.read64 (s0.readReg64 .x1 + 56#64)))
      (s0.sp - 144#64) 64 := by
    agrees_outside_writes
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by rw [mem_setMem]; exact FinSaved.of_agreesOutside hsaved hag hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact S2Frame.trans_agreesOutside_sub hframe (rbase := s0.sp - 16528#64) (rlen := 16528)
              (by simp [FinRegsExt]) (by bv_omega) hag }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg,
      x23_eq := by fin3_reg, x24_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_copy _ _ _ _ _ _ _ _ _ _).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            readBytes_64_eq_append_8 s.mem (s0.readReg64 .x1), hbuf]
      ist_eq := by rw [mem_setMem]; exact (hag.readBytes_eq hd_fsp64_ist (by decide)).trans hist
      ost_eq := by rw [mem_setMem]; exact (hag.readBytes_eq hd_fsp64_ost (by decide)).trans host
      obl_eq := by rw [mem_setMem]; exact (hag.read64_eq hd_fsp64_obl).trans hobl }

structure StateF2b (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 116)
  common  : FinCommonExt s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem seg2_two_b_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF2a img F key pfx tail s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF2b img F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23, hx24, hblk, hist, host, hobl⟩
  have hstat := hcom.status
  have hsp := hcom.sp_eq
  have hbl : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s_bl.readReg64 .lr = img.base + bv% (ls_off% finalizeFixed3Name + 116) ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64 ∧
      s_bl.readReg64 .x1 = s0.sp - 144#64 ∧
      s_bl.readReg64 .x2 = 1#64 ∧
      s_bl.readReg64 .x19 = s.readReg64 .x19 ∧
      s_bl.readReg64 .x20 = s.readReg64 .x20 ∧
      s_bl.readReg64 .x21 = s.readReg64 .x21 ∧
      s_bl.readReg64 .x22 = s.readReg64 .x22 ∧
      s_bl.readReg64 .x23 = s.readReg64 .x23 ∧
      s_bl.readReg64 .x24 = s.readReg64 .x24 ∧
      s_bl.readReg64 .x26 = s.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s.readReg64 .x29 ∧
      s_bl.mem = s.mem) := by
    fin3_step
    exact RunsTo.refl ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, rfl⟩
  refine (step_inner_compress256 hHooks hpre hfrz hsym hbl hcom hist hblk
    (innerPadBlock1_length hpre.tail_lt) host hobl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hcom_sf, hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hist_sf, host_sf, hobl_sf⟩
  exact ⟨hpc_sf, hcom_sf, hx19_sf.trans hx19, hx20_sf.trans hx20,
    hx21_sf.trans hx21, hx22_sf.trans hx22, hx23_sf.trans hx23, hx24_sf.trans hx24,
    hist_sf, host_sf, hobl_sf⟩

structure StateF2c (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 176)
  common  : FinCommonExt s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerPadBlock2 (1 + pfx.length / 64) tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

theorem seg2_two_c_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hs : StateF2b img F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF2c img F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := 1 + pfx.length / 64) hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 8 fin3_step
  let mz := ((((((s.mem.write64 (s0.readReg64 .x1 + 48#64) 0#64).write64
    (s0.readReg64 .x1 + 16#64) 0#64).write64
    (s0.readReg64 .x1 + 24#64) 0#64).write64
    (s0.readReg64 .x1 + 32#64) 0#64).write64
    (s0.readReg64 .x1 + 40#64) 0#64).write64
    (s0.readReg64 .x1) 0#64).write64
    (s0.readReg64 .x1 + 8#64) 0#64
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 fin3_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  have hag0 : AgreesOutside s.mem mz (s0.readReg64 .x1) 64 := by
    dsimp only [mz]; agrees_outside_writes
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a mz (s0.readReg64 .x1) (s0.sp - 144#64)
    0#64 0#64 0#64 0#64 _ 0#64 0#64 0#64 _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hsaved0 : FinSaved s0 (s0.sp - 144#64) mz :=
    FinSaved.of_agreesOutside hsaved hag0 hd_hm64_saved
  have hframe0 : S2Frame s0.mem mz (FinRegsExt s0) :=
    S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
      (by simp [FinRegsExt]) (by bv_omega) hag0
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved0 hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by rw [mem_setMem]; exact s2frame_seg2a hframe0 hag1 hag2 hag3 }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 mz _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_zero_7, toLEBytes_8_rev64]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans
              ((hag0.readBytes_eq hd_hm64_ist (by decide)).trans hist)))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans
              ((hag0.readBytes_eq hd_hm64_ost (by decide)).trans host)))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans
              ((hag0.read64_eq hd_hm64_obl).trans hobl))) }

theorem seg2_two_d_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF2c img F key pfx tail s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateF3Gen img F key
        (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
          (innerPadBlock2 (1 + pfx.length / 64) tail)) s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  have hstat := hcom.status
  have hsp := hcom.sp_eq
  have hbl : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s_bl.readReg64 .lr = img.base + bv% (ls_off% finalizeFixed3Name + 180) ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64 ∧
      s_bl.readReg64 .x1 = s0.sp - 144#64 ∧
      s_bl.readReg64 .x2 = 1#64 ∧
      s_bl.readReg64 .x19 = s.readReg64 .x19 ∧
      s_bl.readReg64 .x20 = s.readReg64 .x20 ∧
      s_bl.readReg64 .x21 = s.readReg64 .x21 ∧
      s_bl.readReg64 .x22 = s.readReg64 .x22 ∧
      s_bl.readReg64 .x23 = s.readReg64 .x23 ∧
      s_bl.readReg64 .x24 = s.readReg64 .x24 ∧
      s_bl.readReg64 .x26 = s.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s.readReg64 .x29 ∧
      s_bl.mem = s.mem) := by
    fin3_step
    exact RunsTo.refl ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, rfl⟩
  refine (step_inner_compress256 hHooks hpre hfrz hsym hbl hcom hist hblk
    (innerPadBlock2_length (1 + pfx.length / 64) tail) host hobl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hcom_sf, hx19_sf, hx20_sf, hx21_sf, hx22_sf, _, _, hist_sf, host_sf, hobl_sf⟩
  exact ⟨hpc_sf, hcom_sf, hx19_sf.trans hx19, hx20_sf.trans hx20,
    hx21_sf.trans hx21, hx22_sf.trans hx22, hist_sf, host_sf, hobl_sf⟩

end FinalizeFixed3ExtProof

end CryptoVerification.SpqrV1.Kdf
