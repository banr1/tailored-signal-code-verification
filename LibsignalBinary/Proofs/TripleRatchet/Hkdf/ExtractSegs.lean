/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import ProofLib.SepLogic.HeapIntro

/-!
# Segment Proofs for `extract`

Proves symbolic-execution segments `seg0_runsTo` through `seg3_runsTo` and their
`[LibsignalPlacement]` counterparts for `GenericHkdf<Hmac<Sha256>>::extract`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Extract

/-- Bridge lemma turning `NewFromSliceOkExt img C ext` into a `RunsToE` transition on
`tripleRatchetProgAtExt img.base ext` for a `≤ 32`-byte key slice at `keyRegA` (whose separation
logic assertion agrees with `(keyA ↦ₛ key)`). -/
theorem nfs_runsTo_ext {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hNfs : NewFromSliceOkExt img C ext)
    {s : State} {ret keyRegA keyA : BitVec 64} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyRegA)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 key.length)
    (hkey_len : key.length ≤ 32)
    (hkey_pts : (keyRegA ↦ₛ key) = (keyA ↦ₛ key))
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") := by
    unfold tripleRatchetProgAtExt newFromSliceName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")]
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyRegA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 ret 0x98 (fun _ => True) := IsBlock.memRegion ret 0x98
  have hb2 : IsBlock P2 keyA key.length
      (fun m => key.length ≤ 2 ^ 64 ∧ m.readBytes keyA key.length = key) :=
    IsBlock.pointsToBytes keyA key
  have hb3 : IsBlock P3 (s.sp - 544#64) 544 (fun _ => True) := IsBlock.memRegion (s.sp - 544#64) 544
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : RW s.mem keyA key.length :=
    fun a ha => hrw_key a (by simp only [InRegion] at ha ⊢; omega)
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length :=
    ⟨hd_ret_key.1, Nat.le_trans hkey_len hd_ret_key.2⟩
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 544#64) 544 :=
    ⟨Nat.le_trans hkey_len hd_key_stk.1, hd_key_stk.2⟩
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, hkey_mem⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre_sat : s.mem ⊨ ((newFromSliceSpec C.F).inImage img).pre xg s ∗ R := by
    rw [Spec.inImage, newFromSliceSpec]
    dsimp only [xg]
    rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2_nat, hkey_le64⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full hNfs xg R (hpc.trans hfn.symm) hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, newFromSliceSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, newFromSliceSpec] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, newFromSliceSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, ⟨⟩⟩⟩
  rw [Spec.inImage, newFromSliceSpec] at hpost_sat
  dsimp only [xg] at hpost_sat
  rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1_tag : IsBlock (ret ↦₆₄ 0#64) ret 8 (fun m => m.read64 ret = 0#64) :=
    IsBlock.pointsTo64 ret 0#64
  have hb1_hm : IsBlock (hmacCoreAt C.F (ret + 8#64) key []) (ret + 8#64) 0x90
      (fun m => HmacSt m (ret + 8#64) C.F key []) :=
    isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide)
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    hb1_tag.sepConj hb1_hm rfl (by decide)
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by
    dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by
    ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hmc_map := hmc.2.2
  replace hmc := hmc.1
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans hkey_mem.symm) hmc hmc_map
  exact ⟨s', hsteps, ⟨htr, CallingConventionPreserved.vregs hcc⟩, ⟨hpc', hstat', hcc, hok, hhm, hframe⟩,
    hsteps.codeLoaded hL⟩

/-- Bridge lemma turning `NewFromSliceOkExt img C ext` into a `RunsToE` transition on
`tripleRatchetProgAtExt img.base ext` for a 32-byte key slice at `keyA`. -/
theorem nfs32_runsTo_ext {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hNfs : NewFromSliceOkExt img C ext)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) :=
  nfs_runsTo_ext hNfs hfrz hsym hpc hstat hx0 hx1 (by rw [hx2, hkey_len])
    (by omega) rfl (by rwa [hkey_len]) hrw_ret hrw_key hrw_stk hd_ret_key hd_ret_stk hd_key_stk hsp_al

section Segments

variable {img : Obj.Image} {C : Crypto} {ext : String → Option (State → State)}

set_option maxHeartbeats 3200000 in
/-- Segment 0 (`img.base + 0x1ad38` → `img.base + 0x2b3b0`, 20 steps): prologue, zero
`[sp0 + 144 .. sp0 + 176)`, select `(sp0 + 144, 32)` or `(x.saltA, saltLen)`, and `bl new_from_slice`. -/
theorem seg0_runsTo {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s0 (ENfs1 img.base x s0 sp0) := by
  generalize hPost : ENfs1 img.base x s0 sp0 = Post
  iterate 20 s2_step
  subst hPost
  refine RunsTo.refl ?_
  have hsaved : ExtSaved s0 sp0
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) :=
    { h29 := by simp (config := { decide := true }) only [arm64_norm]
      hlr := by simp (config := { decide := true }) only [arm64_norm]
      h28 := by simp (config := { decide := true }) only [arm64_norm]
      h26 := by simp (config := { decide := true }) only [arm64_norm]
      h25 := by simp (config := { decide := true }) only [arm64_norm]
      h24 := by simp (config := { decide := true }) only [arm64_norm]
      h23 := by simp (config := { decide := true }) only [arm64_norm]
      h22 := by simp (config := { decide := true }) only [arm64_norm]
      h21 := by simp (config := { decide := true }) only [arm64_norm]
      h20 := by simp (config := { decide := true }) only [arm64_norm]
      h19 := by simp (config := { decide := true }) only [arm64_norm] }
  have hag : AgreesOutside s0.mem
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) sp0 432 := by
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide))
  have hframe : ExtFrame s0 sp0 _ :=
    ExtFrame.of_agreesOutside_sp0 (n := 432) (S2Frame.refl _ _) (by decide) hag
  unfold ENfs1
  refine ⟨⟨hstat, rfl, rfl, rfl, rfl, hsaved, hframe⟩,
    rfl, rfl, rfl, ?_, ?_, rfl, rfl, fun sv hsv => (hsalt_some sv hsv).1, ?_⟩
  · by_cases h0 : x.saltA = 0#64 <;> simp [saltRegOf, hx1, h0]
  · cases hsalt : x.salt with
    | none =>
      by_cases h0 : x.saltA = 0#64
      · simp [saltSliceOf, hsalt, hx1, h0]
      · have hx2_0 : s0.readReg64 .x2 = 0#64 := (hsalt_none hsalt).resolve_left h0
        simp [saltSliceOf, hsalt, hx1, h0, hx2_0]
    | some sv =>
      obtain ⟨hne, -, -⟩ := hsalt_some sv hsalt
      have hx2' : s0.readReg64 .x2 = 32#64 := hx2 (by simp [hsalt])
      simp [saltSliceOf, hsalt, hx1, hx2', hne, sv.2]
  · cases hsalt : x.salt with
    | none =>
      by_cases h0 : x.saltA = 0#64
      · simp only [hsalt, saltPtrOf, saltSliceOf, h0, ↓reduceIte, List.length_replicate,
          State.setMem]
        refine readBytes_32_zero_of_read64_zero ?_ ?_ ?_ ?_ <;>
          simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
      · simp only [hsalt, saltPtrOf, saltSliceOf, h0, ↓reduceIte]; rfl
    | some sv =>
      obtain ⟨hne, hmem_sv, hd_sv_stk⟩ := hsalt_some sv hsalt
      simp only [hsalt, saltPtrOf, saltSliceOf, List.Vector.toList_length, State.setMem]
      have hd_sv_sp0 : DisjointRegions sp0 432 x.saltA 32 := by
        have hsub : 0 < 432 ∧ (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
          have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
          rw [heq]; decide
        exact (disj_stk_sub_right hd_sv_stk sp0 432 hsub).symm
      rw [(frame_of_agreesOutside hag).readBytes_eq ?_ (by decide)]
      · exact hmem_sv
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact hd_sv_sp0

/-- Segment 1 (`img.base + 0x2b3b0` → `img.base + 0x1ad88`): first `new_from_slice` call (`salt`). -/
theorem nfs1_runsTo (hNfs : NewFromSliceOkExt img C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1 img.base x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet1 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs_runsTo_ext hNfs
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1 hx2
    (saltSliceOf_length_le x)
    (pointsToBytes_saltRegOf_eq sp0 x hsalt_some_ne)
    hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544.2))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

/-- Segment 1a (`img.base + 0x1ad88` → `img.base + 0x51b0c`, 28 steps): check `Ok`, copy `Hmac` to `sp0`, prepare `memcpy`. -/
theorem seg1a_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EMemcpy img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hpos : s.mem.read8 (sp0 + 247#64) = 0#8 := by
    have heq : sp0 + 247#64 = (sp0 + 184#64) + 0x3f#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.1
  iterate 28 s2_step
  refine RunsTo.refl ?_
  unfold EMemcpy
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, hx21, rfl, rfl, ?_⟩
  · dsimp only [State.setMem]
    refine ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide)
      | with_reducible refine agreesOutside_sp0_write64_zero ?_ (by decide))
  · refine HmacSt.of_copy_empty hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

/-- Segment 1b (`img.base + 0x51b0c` → `img.base + 0x1ae80`, 4 steps): `memcpy(sp0, ikm, 32)` and `pos := 32`. -/
theorem seg1b_runsTo [HkdfHooks C.F ext] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpy img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EC88 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 :=
    hrw_sp0_s.sub (by bv_omega)
  refine s2_memcpy_step_ext img.base C ext
    hstat hpc hx0 hx1 (by rw [hx2]; rfl) hlr hikm_s hrw_sp0_32 ?_
  have hag_mc : AgreesOutside s.mem (s.mem.writeBytes sp0 x.ikm) sp0 328 :=
    (ProofLib.AgreesOutside.writeBytes_self s.mem sp0 x.ikm).mono (by omega)
  have hrw_sp0 : (s.mem.writeBytes sp0 x.ikm).RW sp0 432 :=
    rw_of_perm_eq hag_mc.2 hrw_sp0_s
  iterate 3 s2_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s.mem ((s.mem.writeBytes sp0 x.ikm).write8 (sp0 + 63#64) 32#8) sp0 328 :=
    agreesOutside_sp0_write8 hag_mc (by decide)
  unfold EC88 ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag⟩,
    rfl, hx22, HmacSt.of_writeBytes_32_write8_pos hhm hikm_len⟩

/-- Segment 1c (`img.base + 0x1ae80` → `img.base + 0x30680`, 13 steps): copy `Hmac` to `sp0 + 176` and call `finalize_fixed`. -/
theorem seg1c_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EFin img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  unfold EFin
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, hx22, ?_⟩
  · dsimp only [State.setMem]
    refine ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide))
  · refine HmacSt.of_copy_19 hhm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

/-- Segment 2 (`img.base + 0x30680` → `img.base + 0x1aeb4`): `finalize_fixed` produces `PRK` at `sp0 + 144`. -/
theorem fin_runsTo (hFin : Fin.FinalizeFixedRunsToExt img.base C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFin img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (ERetFin img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hpre : FinalizeFixedProof.FinPre img.base C.F (effectiveSalt x.salt) x.ikm s :=
    { pc_eq := hpc
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      msg_lt := by omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  refine (hFin hpre).mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_frame hfr' ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_triple hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CalleeSaved.x22 hcs).trans hx22, hout⟩

/-- Segment 3 (`img.base + 0x1aeb4` → `img.base + 0x2b3b0`, 4 steps): setup for second `new_from_slice` (`PRK`). -/
theorem seg2_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERetFin img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (ENfs2 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hprk⟩
  iterate 4 s2_step
  refine RunsTo.refl ?_
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    rfl, rfl, rfl, rfl, rfl, hx22, hprk⟩

/-- Segment 4 (`img.base + 0x2b3b0` → `img.base + 0x1aec4`): second `new_from_slice` call (`PRK`). -/
theorem nfs2_runsTo (hNfs : NewFromSliceOkExt img C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2 img.base C.F x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet2 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_runsTo_ext hNfs
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1 hx2
    hprk_len
    hprk
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0.2))
    hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

/-- Segment 5 (`img.base + 0x1aec4` → `s0.readReg64 .lr`, 27 steps): check `Ok`, store `(PRK, Hkdf)` to `out`, epilogue. -/
theorem seg3_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet2 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EPost C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hok, hprk, hhm⟩
  rcases hsaved with ⟨hs29, hslr, hs28, hs26, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 0xb0 :=
    hframe.rw_of_rw (s0.readReg64 .x0) 0xb0 hRW_out
  have h_ro_1 := fun (m : Memory) (rOff wOff v : BitVec 64) =>
    read64_sp0_write64_out m hd_out_stk (rOff := rOff) (wOff := wOff) (v := v)
  have h_ro_0 := fun (m : Memory) (rOff v : BitVec 64) =>
    read64_sp0_write64_out_zero m hd_out_stk (rOff := rOff) (v := v)
  iterate 27 s2_step
  refine RunsTo.refl ?_
  unfold EPost
  refine ⟨rfl, hstat, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsp0.symm, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hx27
    · rfl
    · rfl
    · rfl
  · rw [← hprk]
    refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · refine HmacSt.of_copy_empty hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · dsimp only [State.setMem]
    refine hframe.of_agreesOutside_out ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_out_write64 ?_ (by decide)
      | with_reducible refine agreesOutside_out_write64_zero ?_)

end Segments

/-! ## Relocatable `[LibsignalPlacement]` Segment Proofs -/

/-- Relocatable (`[LibsignalPlacement]`) bridge lemma turning a `subroutine_ok` for
`newFromSliceSpec C.F` (augmented with `⌜Inv s0.mem⌝`) into a `RunsToE` transition on
`((blkPC_54).rebase (blkPl_54).base H)` for a `≤ 32`-byte key slice at `keyRegA`. -/
theorem nfs_runsTo_placed [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {s : State} {ret keyRegA keyA : BitVec 64} {key : List (BitVec 8)}
    (hInv : Inv s.mem)
    (hpc : s.pc = lsmpl.base 114)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyRegA)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 key.length)
    (hkey_len : key.length ≤ 32)
    (hkey_pts : (keyRegA ↦ₛ key) = (keyA ↦ₛ key))
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyRegA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 ret 0x98 (fun _ => True) := IsBlock.memRegion ret 0x98
  have hb2 : IsBlock P2 keyA key.length
      (fun m => key.length ≤ 2 ^ 64 ∧ m.readBytes keyA key.length = key) :=
    IsBlock.pointsToBytes keyA key
  have hb3 : IsBlock P3 (s.sp - 544#64) 544 (fun _ => True) := IsBlock.memRegion (s.sp - 544#64) 544
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : RW s.mem keyA key.length :=
    fun a ha => hrw_key a (by simp only [InRegion] at ha ⊢; omega)
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length :=
    ⟨hd_ret_key.1, Nat.le_trans hkey_len hd_ret_key.2⟩
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 544#64) 544 :=
    ⟨Nat.le_trans hkey_len hd_key_stk.1, hd_key_stk.2⟩
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, hkey_mem⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre_sat : s.mem ⊨
      ({ newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }).pre xg s ∗ R := by
    dsimp only []
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hInv, ?_⟩
    rw [newFromSliceSpec]
    dsimp only [xg]
    rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hkey_le64⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full hNfs xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [newFromSliceSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [newFromSliceSpec] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [newFromSliceSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, ⟨⟩⟩⟩
  dsimp only [newFromSliceSpec, xg] at hpost_sat
  rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1_tag : IsBlock (ret ↦₆₄ 0#64) ret 8 (fun m => m.read64 ret = 0#64) :=
    IsBlock.pointsTo64 ret 0#64
  have hb1_hm : IsBlock (hmacCoreAt C.F (ret + 8#64) key []) (ret + 8#64) 0x90
      (fun m => HmacSt m (ret + 8#64) C.F key []) :=
    isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide)
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    hb1_tag.sepConj hb1_hm rfl (by decide)
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by
    dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by
    ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hmc_map := hmc.2.2
  replace hmc := hmc.1
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans hkey_mem.symm) hmc hmc_map
  exact ⟨s', hsteps, ⟨htr, CallingConventionPreserved.vregs hcc⟩, ⟨hpc', hstat', hcc, hok, hhm, hframe⟩,
    hsteps.codeLoaded hL⟩

/-- Relocatable (`[LibsignalPlacement]`) bridge lemma turning a `subroutine_ok` for
`newFromSliceSpec C.F` (augmented with `⌜Inv s0.mem⌝`) into a `RunsToE` transition on
`((blkPC_54).rebase (blkPl_54).base H)` for a 32-byte key slice at `keyA`. -/
theorem nfs32_runsTo_placed [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hInv : Inv s.mem)
    (hpc : s.pc = lsmpl.base 114)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) :=
  nfs_runsTo_placed hNfs hInv hpc hstat hx0 hx1 (by rw [hx2, hkey_len])
    (by omega) rfl (by rwa [hkey_len]) hrw_ret hrw_key hrw_stk hd_ret_key hd_ret_stk hd_key_stk hsp_al

section SegmentsPlaced

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

set_option maxHeartbeats 3200000 in
theorem seg0_placed_runsTo {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = (blkPl_54).base)
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s0 (ENfs1Placed x s0 sp0) := by
  generalize hPost : ENfs1Placed x s0 sp0 = Post
  iterate 20 s2_step
  subst hPost
  refine RunsTo.refl ?_
  have hsaved : ExtSaved s0 sp0
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) :=
    { h29 := by simp (config := { decide := true }) only [arm64_norm]
      hlr := by simp (config := { decide := true }) only [arm64_norm]
      h28 := by simp (config := { decide := true }) only [arm64_norm]
      h26 := by simp (config := { decide := true }) only [arm64_norm]
      h25 := by simp (config := { decide := true }) only [arm64_norm]
      h24 := by simp (config := { decide := true }) only [arm64_norm]
      h23 := by simp (config := { decide := true }) only [arm64_norm]
      h22 := by simp (config := { decide := true }) only [arm64_norm]
      h21 := by simp (config := { decide := true }) only [arm64_norm]
      h20 := by simp (config := { decide := true }) only [arm64_norm]
      h19 := by simp (config := { decide := true }) only [arm64_norm] }
  have hag : AgreesOutside s0.mem
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) sp0 432 := by
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide))
  have hframe : ExtFrame s0 sp0 _ :=
    ExtFrame.of_agreesOutside_sp0 (n := 432) (S2Frame.refl _ _) (by decide) hag
  unfold ENfs1Placed
  refine ⟨⟨hstat, rfl, rfl, rfl, rfl, hsaved, hframe⟩,
    rfl, rfl, rfl, ?_, ?_, rfl, rfl, fun sv hsv => (hsalt_some sv hsv).1, ?_⟩
  · by_cases h0 : x.saltA = 0#64 <;> simp [saltRegOf, hx1, h0]
  · cases hsalt : x.salt with
    | none =>
      by_cases h0 : x.saltA = 0#64
      · simp [saltSliceOf, hsalt, hx1, h0]
      · have hx2_0 : s0.readReg64 .x2 = 0#64 := (hsalt_none hsalt).resolve_left h0
        simp [saltSliceOf, hsalt, hx1, h0, hx2_0]
    | some sv =>
      obtain ⟨hne, -, -⟩ := hsalt_some sv hsalt
      have hx2' : s0.readReg64 .x2 = 32#64 := hx2 (by simp [hsalt])
      simp [saltSliceOf, hsalt, hx1, hx2', hne, sv.2]
  · cases hsalt : x.salt with
    | none =>
      by_cases h0 : x.saltA = 0#64
      · simp only [hsalt, saltPtrOf, saltSliceOf, h0, ↓reduceIte, List.length_replicate,
          State.setMem]
        refine readBytes_32_zero_of_read64_zero ?_ ?_ ?_ ?_ <;>
          simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
      · simp only [hsalt, saltPtrOf, saltSliceOf, h0, ↓reduceIte]; rfl
    | some sv =>
      obtain ⟨hne, hmem_sv, hd_sv_stk⟩ := hsalt_some sv hsalt
      simp only [hsalt, saltPtrOf, saltSliceOf, List.Vector.toList_length, State.setMem]
      have hd_sv_sp0 : DisjointRegions sp0 432 x.saltA 32 := by
        have hsub : 0 < 432 ∧ (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
          have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
          rw [heq]; decide
        exact (disj_stk_sub_right hd_sv_stk sp0 432 hsub).symm
      rw [(frame_of_agreesOutside hag).readBytes_eq ?_ (by decide)]
      · exact hmem_sv
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact hd_sv_sp0

theorem nfs1_placed_runsTo {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hInv : Inv s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1Placed x s0 sp0 s) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (ERet1 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs_runsTo_placed hNfs hInv
    hpc hstat hx0 hx1 hx2
    (saltSliceOf_length_le x)
    (pointsToBytes_saltRegOf_eq sp0 x hsalt_some_ne)
    hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544.2))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  have hlr' : s.readReg64 .lr = extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) := by
    rw [hlr, extPlacedFakeB_off_80]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

theorem seg1a_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1 extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyPlaced C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hpos : s.mem.read8 (sp0 + 247#64) = 0#8 := by
    have heq : sp0 + 247#64 = (sp0 + 184#64) + 0x3f#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.1
  iterate 28 s2_step
  refine RunsTo.refl ?_
  unfold EMemcpyPlaced
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, hx21, rfl, rfl, ?_⟩
  · dsimp only [State.setMem]
    refine ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide)
      | with_reducible refine agreesOutside_sp0_write64_zero ?_ (by decide))
  · refine HmacSt.of_copy_empty hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

theorem seg1b_placed_runsTo [HkdfPlacedHooks C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 :=
    hrw_sp0_s.sub (by bv_omega)
  refine s2_memcpy_step_placed C H
    hstat hpc hx0 hx1 (by rw [hx2]; rfl) hlr hikm_s hrw_sp0_32 ?_
  have hag_mc : AgreesOutside s.mem (s.mem.writeBytes sp0 x.ikm) sp0 328 :=
    (ProofLib.AgreesOutside.writeBytes_self s.mem sp0 x.ikm).mono (by omega)
  have hrw_sp0 : (s.mem.writeBytes sp0 x.ikm).RW sp0 432 :=
    rw_of_perm_eq hag_mc.2 hrw_sp0_s
  iterate 3 s2_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s.mem ((s.mem.writeBytes sp0 x.ikm).write8 (sp0 + 63#64) 32#8) sp0 328 :=
    agreesOutside_sp0_write8 hag_mc (by decide)
  unfold EC88 ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag⟩,
    rfl, hx22, HmacSt.of_writeBytes_32_write8_pos hhm hikm_len⟩

theorem seg1c_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88 extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EFinPlaced C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  unfold EFinPlaced
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, hx22, ?_⟩
  · dsimp only [State.setMem]
    refine ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide))
  · refine HmacSt.of_copy_19 hhm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

theorem fin_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hFin :
      FinalizeFixedProof.FinPre finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
        (FinalizeFixedProof.FinPost C.F (effectiveSalt x.salt) x.ikm s))
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ERetFin extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hpre : FinalizeFixedProof.FinPre finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s :=
    { pc_eq := hpc.trans finPlacedFakeB_off_0.symm
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      msg_lt := by omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  refine (hFin hpre).mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_frame hfr' ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_triple hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  have hlr' : s.readReg64 .lr = extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

theorem seg2_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERetFin extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ENfs2Placed C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hprk⟩
  iterate 4 s2_step
  refine RunsTo.refl ?_
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    rfl, rfl, rfl, rfl, rfl, hx22, hprk⟩

theorem nfs2_placed_runsTo {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hInv : Inv s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2Placed C.F x s0 sp0 s) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (ERet2 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_runsTo_placed hNfs hInv
    hpc hstat hx0 hx1 hx2
    hprk_len
    hprk
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0.2))
    hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  have hlr' : s.readReg64 .lr = extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) := by
    rw [hlr, extPlacedFakeB_off_396]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

theorem seg3_placed_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet2 extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EPost C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hok, hprk, hhm⟩
  rcases hsaved with ⟨hs29, hslr, hs28, hs26, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 0xb0 :=
    hframe.rw_of_rw (s0.readReg64 .x0) 0xb0 hRW_out
  have h_ro_1 := fun (m : Memory) (rOff wOff v : BitVec 64) =>
    read64_sp0_write64_out m hd_out_stk (rOff := rOff) (wOff := wOff) (v := v)
  have h_ro_0 := fun (m : Memory) (rOff v : BitVec 64) =>
    read64_sp0_write64_out_zero m hd_out_stk (rOff := rOff) (v := v)
  iterate 27 s2_step
  refine RunsTo.refl ?_
  unfold EPost
  refine ⟨rfl, hstat, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsp0.symm, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hx27
    · rfl
    · rfl
    · rfl
  · rw [← hprk]
    refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · refine HmacSt.of_copy_empty hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · dsimp only [State.setMem]
    refine hframe.of_agreesOutside_out ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_out_write64 ?_ (by decide)
      | with_reducible refine agreesOutside_out_write64_zero ?_)

end SegmentsPlaced

end Extract

namespace HkdfExt

open Extract

section SegmentsCX

variable {img : Obj.Image} {C : Crypto} {ext : String → Option (State → State)}

theorem seg0_runsTo_cx {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s0 (ENfs1 img.base x s0 sp0) :=
  Extract.seg0_runsTo hpc hstat hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none hsalt_some

theorem seg1a_runsTo_cx {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EMemcpy img.base C.F x s0 sp0) :=
  Extract.seg1a_runsTo hRW_stk hsp_al hs

theorem seg1c_runsTo_cx {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EFin img.base C.F x s0 sp0) :=
  Extract.seg1c_runsTo hRW_stk hsp_al hs

theorem seg2_runsTo_cx {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERetFin img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (ENfs2 img.base C.F x s0 sp0) :=
  Extract.seg2_runsTo hsp_al hs

theorem seg3_runsTo_cx {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet2 img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EPost C.F x s0 sp0) :=
  Extract.seg3_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs

end SegmentsCX

end HkdfExt

end CryptoVerification.LibsignalTripleRatchet
