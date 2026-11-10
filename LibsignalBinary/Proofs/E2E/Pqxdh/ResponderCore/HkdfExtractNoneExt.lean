/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfStubsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfExtractExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt

/-!
# `.inImage`-Free `pqxdhHkdfExtractNone_ok` and `PqxdhHkdfExtractOk_ext`

Proves `.inImage`-free `pqxdhHkdfExtractNone_ok_of_stubsExt` (`salt = none`,
`ikm.length ∈ {160, 192, 224}`) and combines it with `pqxdhHkdfExtractSome_ok_of_stubsExt` to
obtain `pqxdhHkdfExtract_ok_of_stubsExt` on `tripleRatchetProgAtExt img.base ext` under
`FrozenRo img s.mem`. Uses `memcpy_opt_stub_runsTo` for the trailing-bytes copy so `192 % 64 = 0`
and `160 % 64 = 224 % 64 = 32` are handled uniformly.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExtractX
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

local macro "fin_reg_ext" : tactic => `(tactic| (
  try rw [State.readReg64_setMem]
  try rw [State.pc_setMem]
  try rw [State.sp_setMem]
  try rw [State.status_setMem]
  simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## Cut-Point Predicates for Long-IKM `extract` -/

def ENfs1LongX (b : BitVec 64) (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) :
    Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = saltPtrOf sp0 x ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.readBytes (saltPtrOf sp0 x) 32 = effectiveSalt x.salt

def ERet1LongX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

def ECompLongX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 308) ∧
  s.readReg64 .x0 = sp0 + 0x40#64 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length / 64) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EMemcpyLongX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "memcpy") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 328) ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 (x.ikm.length % 64) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 =
    shaStateBytes ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl F
      (hmacInnerInit F (effectiveSalt x.salt))) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EC88LongX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 328) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem sp0 F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

def EFinLongX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem (sp0 + 176#64) F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

/-! ## Segment Proofs for Long-IKM `extract` -/

set_option maxHeartbeats 3200000 in
private theorem seg0_long_x_runsTo {img : Obj.Image} {ext : String → Option (State → State)}
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s0 (ENfs1LongX img.base x s0 sp0) := by
  iterate 20 s2_step
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
  have hframe : ExtFrameX s0 sp0 _ :=
    ExtFrameX.of_agreesOutside_sp0 (n := 432) (S2Frame.refl _ _) (by decide) hag
  unfold ENfs1LongX
  refine ⟨⟨hstat, rfl, rfl, rfl, rfl, hsaved, hframe⟩,
    rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp [saltPtrOf, hsalt, hx1, hsaltA]
  · simp [hx1, hsaltA]
  · rw [saltPtrOf, effectiveSalt, hsalt]
    dsimp only [Option.map, Option.getD, State.setMem]
    refine readBytes_32_zero_of_read64_zero ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]

private theorem nfs1_long_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsalt : x.salt = none)
    (hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1LongX img.base x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s
      (ERet1LongX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrw_salt : RW s.mem (saltPtrOf sp0 x) 32 := by
    rw [saltPtrOf, hsalt]
    exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144)
  have hrun := nfs32_ro_runsTo_ext himg hS
    (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 hx1 hx2 (effectiveSalt_length x.salt) hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_x0.2))
    hrw_salt
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_16928.2))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_16928)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16928#64 16928 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_pair hframe hfr' hsub_x0.2 hsub_16928.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩


private theorem ExtSaved_and_FrameX_of_agreesOutside_328
    {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    (hs : ExtSaved s0 sp0 m) (hf : ExtFrameX s0 sp0 m) (hag : AgreesOutside m m' sp0 328) :
    ExtSaved s0 sp0 m' ∧ ExtFrameX s0 sp0 m' :=
  ⟨hs.of_agreesOutside_328 hag, ExtFrameX.of_agreesOutside_sp0 hf (by decide) hag⟩

private theorem seg1a_long_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1LongX img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (ECompLongX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    clear * -; bv_omega
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hpos : s.mem.read8 (sp0 + 247#64) = 0#8 := by
    have heq : sp0 + 247#64 = (sp0 + 184#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hhm.2.2.1
  have hcnt1 : s.mem.read64 (sp0 + 280#64) = 1#64 := by
    have heq : sp0 + 280#64 = (sp0 + 184#64) + 0x60#64 := by bv_lin
    rw [heq]; exact hhm.2.2.2.2.1
  have hcnt2 : s.mem.read64 (sp0 + 320#64) = 1#64 := by
    have heq : sp0 + 320#64 = (sp0 + 184#64) + 0x88#64 := by bv_lin
    rw [heq]; exact hhm.2.2.2.2.2.2
  rcases hikm_len with hlen | hlen | hlen <;> {
    rw [hlen] at hx21
    iterate 35 s2_step
    refine RunsTo.refl ?_
    unfold ECompLongX
    rw [hlen]
    refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
      by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext,
      by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, by fin_reg_ext, ?_, ?_, ?_, ?_⟩
    · dsimp only [State.setMem]
      refine ExtSaved_and_FrameX_of_agreesOutside_328 hsaved hframe ?_
      repeat' (first
        | with_reducible exact AgreesOutside.rfl' _ _ _
        | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide)
        | with_reducible refine agreesOutside_sp0_write64_zero ?_ (by decide))
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt1]
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt2]
  }

private theorem seg1b1_long_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 16928#64) 17360)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLongX img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (EMemcpyLongX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hx22, hx24, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  let blocks := x.ikm.take (64 * (x.ikm.length / 64))
  have hblk_len : blocks.length = 64 * (x.ikm.length / 64) := by
    dsimp [blocks]; simp; omega
  have hblk_pos : 0 < blocks.length := by
    rw [hblk_len]; rcases hikm_len with h | h | h <;> omega
  have hblk_le : blocks.length ≤ 2 ^ 64 := by
    rw [hblk_len]; rcases hikm_len with h | h | h <;> omega
  have hblk_s : s.mem.readBytes x.ikmA blocks.length = blocks := by
    rw [hblk_len]
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
    simpa [blocks] using h
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_40 : 0 < 32 ∧ ((sp0 + 0x40#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 0x40#64) - (sp0 - 16928#64) = 16992#64 := by bv_lin
    rw [heq]; decide
  have hsub_ext : 0 < 16384 ∧ ((sp0 - 16384#64) - (sp0 - 16928#64)).toNat + 16384 ≤ 17360 := by
    have heq : (sp0 - 16384#64) - (sp0 - 16928#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hrw_st_s : s.mem.RW (sp0 + 0x40#64) 32 :=
    rw_sp0_sub hrw_sp0_s (sp0 + 0x40#64) 32 (by clear * -; bv_omega)
  have hrw_blk_s : s.mem.RW x.ikmA blocks.length := by
    have hrw_ikm_s : s.mem.RW x.ikmA x.ikm.length := hframe.rw_of_rw _ _ hRW_ikm
    exact hrw_ikm_s.sub (by clear * - hblk_len hikm_len; bv_omega)
  have hrw_ext_s : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact hframe.rw_of_rw (sp0 - 16384#64) 16384 (rw_stkX_sub hRW_stk _ _ hsub_ext.2)
  have hd_ikm_blk : DisjointRegions x.ikmA blocks.length (sp0 - 16928#64) 17360 :=
    hd_ikm_stk.sub_left _ ⟨hblk_pos, by clear * - hblk_len hikm_len; bv_omega⟩
  have hd_st_blk : DisjointRegions (sp0 + 0x40#64) 32 x.ikmA blocks.length :=
    (disj_stkX_sub_right hd_ikm_blk (sp0 + 0x40#64) 32 hsub_40).symm
  have hd_st_ext : DisjointRegions (sp0 + 0x40#64) 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact (disj_sp0_sub_off sp0 16384#64 16384 0x40#64 32 (by decide)).symm
  have hd_blk_ext : DisjointRegions x.ikmA blocks.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact disj_stkX_sub_right hd_ikm_blk (sp0 - 16384#64) 16384 hsub_ext
  have hx2_mul : 64 * (s.readReg64 .x2).toNat = blocks.length := by
    rw [hblk_len]
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  have hc := compress256_stub_runsTo hS.compress256 (by decide)
    hpc hstat hx0 hx1 hx2_mul hblk_le hist hblk_s
    hrw_st_s hrw_blk_s hrw_ext_s hd_st_blk hd_st_ext hd_blk_ext
    (by rw [hsp]; exact hsp_al)
  refine hc.trans fun s1 hs1 => ?_
  rcases hs1 with ⟨hpc1, hstat1, hcc1, hist1, _, hfr_c⟩
  rw [hsp] at hfr_c
  have hpc1' : s1.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 308) :=
    hpc1.trans hlr
  have hsp1 : s1.sp = sp0 := (Extract.CallingConventionPreserved.sp_eq hcc1).trans hsp
  have hx19_1 : s1.readReg64 .x19 = s0.readReg64 .x0 := (CallingConventionPreserved.x19 hcc1).trans hx19
  have hx20_1 : s1.readReg64 .x20 = x.ikmA := (CallingConventionPreserved.x20 hcc1).trans hx20
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 (x.ikm.length % 64) :=
    (CallingConventionPreserved.x21 hcc1).trans hx21
  have hx22_1 : s1.readReg64 .x22 = sp0 + 176#64 := (CallingConventionPreserved.x22 hcc1).trans hx22
  have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) :=
    hcc1.2.2.2.2.2.2.1.trans hx24
  have hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27 := (CallingConventionPreserved.x27 hcc1).trans hx27
  have hx29_1 : s1.readReg64 .x29 = sp0 + 336#64 := (CallingConventionPreserved.x29 hcc1).trans hx29
  have hsaved1 : ExtSaved s0 sp0 s1.mem := by
    refine hsaved.of_s2frame hfr_c (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 0x40#64 32 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16384#64 16384 336#64 96 (by decide)
  have hframe1 : ExtFrameX s0 sp0 s1.mem :=
    ExtFrameX.trans_pair hframe hfr_c hsub_40.2 hsub_ext.2
  have hrw_sp0_1 : s1.mem.RW sp0 432 :=
    hframe1.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hd_c (off : BitVec 64) (sz : ℕ)
      (h1 : 32 ≤ (off - 0x40#64).toNat ∧ sz ≤ (0x40#64 - off).toNat)
      (h2 : 16384 ≤ (off + 16384#64).toNat ∧ sz ≤ (0#64 - (off + 16384#64)).toNat) :
      ∀ r ∈ [(sp0 + 0x40#64, (32 : ℕ)), (sp0 - 16384#64, 16384)],
        DisjointRegions r.1 r.2 (sp0 + off) sz := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 0x40#64 32 off sz h1
    · exact disj_sp0_sub_off sp0 16384#64 16384 off sz h2
  have hcnt1_1 : s1.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) := by
    rw [hfr_c.read64_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x60#64) 8 (by clear * -; bv_omega))
      (hd_c 0x60#64 8 (by decide) (by decide)), hcnt1]
  have hout_1 : s1.mem.readBytes (sp0 + 0x68#64) 32 =
      shaStateBytes (hmacOuterInit C.F (effectiveSalt x.salt)) := by
    rw [hfr_c.readBytes_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x68#64) 32 (by clear * -; bv_omega))
      (hd_c 0x68#64 32 (by decide) (by decide)) (by decide), hout]
  have hcnt2_1 : s1.mem.read64 (sp0 + 0x88#64) = 1#64 := by
    rw [hfr_c.read64_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x88#64) 8 (by clear * -; bv_omega))
      (hd_c 0x88#64 8 (by decide) (by decide)), hcnt2]
  have htail : RunsTo (tripleRatchetProgAtExt img.base ext) s1 (EMemcpyLongX img.base C.F x s0 sp0) := by
    iterate 5 s2_step
    refine RunsTo.refl ?_
    let m2 := s1.mem.write8 (sp0 + 63#64) (BitVec.ofNat 8 (x.ikm.length % 64))
    have hag_328 : AgreesOutside s1.mem m2 sp0 328 :=
      agreesOutside_sp0_write8 (AgreesOutside.rfl' s1.mem sp0 328) (by decide)
    have hag_63 : AgreesOutside s1.mem m2 (sp0 + 63#64) 1 :=
      (AgreesOutside.rfl' s1.mem (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
    have hf63 : Frame s1.mem m2 [(sp0 + 63#64, 1)] := frame_of_agreesOutside hag_63
    unfold EMemcpyLongX ExtCommonX
    simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
      State.readReg64_advancePC, State.readReg64_writeReg64,
      Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_true, ite_false]
    dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
    refine ⟨⟨hstat1, hsp1, hx19_1, hx27_1, hx29_1,
      hsaved1.of_agreesOutside_328 hag_328,
      ExtFrameX.of_agreesOutside_sp0 hframe1 (by decide) hag_328⟩,
      rfl, trivial, trivial, trivial, trivial, hx22_1,
      Memory.read8_write8_same s1.mem (sp0 + 63#64) _, ?_, ?_, ?_, ?_⟩
    · rw [hf63.readBytes_eq ?_ (by decide)]; · exact hist1
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact disj_sp0_off sp0 63#64 1 0x40#64 32 (by decide)
    · rw [hf63.read64_eq ?_, hcnt1_1]
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact disj_sp0_off sp0 63#64 1 0x60#64 8 (by decide)
    · rw [hf63.readBytes_eq ?_ (by decide), hout_1]
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact disj_sp0_off sp0 63#64 1 0x68#64 32 (by decide)
    · rw [hf63.read64_eq ?_, hcnt2_1]
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact disj_sp0_off sp0 63#64 1 0x88#64 8 (by decide)
  exact Extract.RunsTo.toE htail

private theorem seg1b2_long_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 16928#64) 17360)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyLongX img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (EC88LongX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  let blocks := x.ikm.take (64 * (x.ikm.length / 64))
  let rem := x.ikm.drop (64 * (x.ikm.length / 64))
  let src := x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))
  have hblk_len : blocks.length = 64 * (x.ikm.length / 64) := by dsimp [blocks]; simp; omega
  have hrem_len : rem.length = x.ikm.length % 64 := by dsimp [rem]; simp; omega
  have hrem_le32 : rem.length ≤ 32 := by
    rw [hrem_len]; rcases hikm_len with h | h | h <;> omega
  have hrem_s : s.mem.readBytes src rem.length = rem := by
    dsimp [src, rem]
    rw [hrem_len]
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    exact h.trans (List.take_of_length_le (by simp; omega))
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_32 : 0 < 32 ∧ (sp0 - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_ext : 0 < 16384 ∧ ((sp0 - 16384#64) - (sp0 - 16928#64)).toNat + 16384 ≤ 17360 := by
    have heq : (sp0 - 16384#64) - (sp0 - 16928#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hrw_dst_s : s.mem.RW sp0 rem.length :=
    rw_sp0_sub hrw_sp0_s sp0 rem.length (by clear * - hrem_le32; bv_omega)
  have hsrc_sub : (src - x.ikmA).toNat + rem.length ≤ x.ikm.length := by
    have heq : src - x.ikmA = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) := by
      dsimp [src]; bv_lin
    rw [heq, hrem_len]
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hrw_src_s : s.mem.RW src rem.length :=
    (hframe.rw_of_rw _ _ hRW_ikm).sub hsrc_sub
  have hrw_ext_s : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact hframe.rw_of_rw (sp0 - 16384#64) 16384 (rw_stkX_sub hRW_stk _ _ hsub_ext.2)
  have hd_src_stk_opt : rem.length = 0 ∨ DisjointRegions src rem.length (sp0 - 16928#64) 17360 := by
    by_cases hz : rem.length = 0
    · exact Or.inl hz
    · exact Or.inr (hd_ikm_stk.sub_left _ ⟨Nat.pos_of_ne_zero hz, hsrc_sub⟩)
  have hd_dst_src : rem.length = 0 ∨ DisjointRegions sp0 rem.length src rem.length := by
    rcases hd_src_stk_opt with hz | hd
    · exact Or.inl hz
    · by_cases hz : rem.length = 0
      · exact Or.inl hz
      · refine Or.inr (disj_stkX_sub_right hd sp0 rem.length ⟨Nat.pos_of_ne_zero hz, ?_⟩).symm
        clear * - hrem_le32; bv_omega
  have hd_dst_ext : rem.length = 0 ∨
      DisjointRegions sp0 rem.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    by_cases hz : rem.length = 0
    · exact Or.inl hz
    · rw [hsp]
      have hd32 : DisjointRegions sp0 32 (sp0 - 16384#64) 16384 := by
        simpa [BitVec.add_zero] using (disj_sp0_sub_off sp0 16384#64 16384 0#64 32 (by decide)).symm
      exact Or.inr (hd32.sub_left _ ⟨Nat.pos_of_ne_zero hz, by clear * - hrem_le32; bv_omega⟩)
  have hd_src_ext : rem.length = 0 ∨
      DisjointRegions src rem.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rcases hd_src_stk_opt with hz | hd
    · exact Or.inl hz
    · rw [hsp]
      exact Or.inr (disj_stkX_sub_right hd (sp0 - 16384#64) 16384 hsub_ext)
  have hx2_nat : (s.readReg64 .x2).toNat = rem.length := by
    rw [hrem_len]; rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  have hmc := memcpy_opt_stub_runsTo hS.memcpy (bs := rem)
    hpc hstat hx0 hx1 hx2_nat hrem_s
    hrw_dst_s hrw_src_s hrw_ext_s hd_dst_src hd_dst_ext hd_src_ext
    (by rw [hsp]; exact hsp_al)
  refine hmc.mono fun s1 hs1 => ?_
  rcases hs1 with ⟨hpc1, hstat1, hcc1, _, hdst1, _, hfr_mc⟩
  rw [hsp] at hfr_mc
  have hfr32 : S2Frame s.mem s1.mem [(sp0, 32), (sp0 - 16384#64, 16384)] := by
    refine hfr_mc.mono fun a ha r hr => ?_
    have h32 := ha (sp0, 32) (by simp)
    have hext := ha (sp0 - 16384#64, 16384) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [OutsideRegion] at h32 ⊢; bv_omega
    · exact hext
  have hsaved1 : ExtSaved s0 sp0 s1.mem := by
    refine hsaved.of_s2frame hfr32 (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 32 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16384#64 16384 336#64 96 (by decide)
  have hframe1 : ExtFrameX s0 sp0 s1.mem :=
    ExtFrameX.trans_pair hframe hfr32 hsub_32.2 hsub_ext.2
  have hd32 (off : BitVec 64) (sz : ℕ)
      (h1 : 32 ≤ off.toNat ∧ sz ≤ (0#64 - off).toNat)
      (h2 : 16384 ≤ (off + 16384#64).toNat ∧ sz ≤ (0#64 - (off + 16384#64)).toNat) :
      ∀ r ∈ [(sp0, (32 : ℕ)), (sp0 - 16384#64, 16384)],
        DisjointRegions r.1 r.2 (sp0 + off) sz := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 32 off sz h1
    · exact disj_sp0_sub_off sp0 16384#64 16384 off sz h2
  have hpos1 : s1.mem.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 rem.length := by
    have hrw1 : s.mem.RW (sp0 + 0x3f#64) 1 := rw_sp0_sub hrw_sp0_s (sp0 + 0x3f#64) 1 (by clear * -; bv_omega)
    have hrd := hrw1.readable (sp0 + 0x3f#64) (by simp only [InRegion, BitVec.sub_self]; decide)
    have heq8 := hfr32.1 (sp0 + 0x3f#64) hrd.1 hrd.2 fun r hr =>
      (hd32 0x3f#64 1 (by decide) (by decide) r hr).outside
        (by simp only [InRegion, BitVec.sub_self]; decide) (by decide)
    rw [heq8, hrem_len, hpos]
  have hist1 : s1.mem.readBytes (sp0 + 0x40#64) 32 =
      shaStateBytes ((chunks64 blocks).foldl C.F (hmacInnerInit C.F (effectiveSalt x.salt))) := by
    rw [hfr32.readBytes_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x40#64) 32 (by clear * -; bv_omega))
      (hd32 0x40#64 32 (by decide) (by decide)) (by decide), hist]
  have hcnt1_1 : s1.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64) := by
    rw [hfr32.read64_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x60#64) 8 (by clear * -; bv_omega))
      (hd32 0x60#64 8 (by decide) (by decide)), hblk_len, Nat.mul_div_cancel_left _ (by decide), hcnt1]
  have hout_1 : s1.mem.readBytes (sp0 + 0x68#64) 32 =
      shaStateBytes (hmacOuterInit C.F (effectiveSalt x.salt)) := by
    rw [hfr32.readBytes_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x68#64) 32 (by clear * -; bv_omega))
      (hd32 0x68#64 32 (by decide) (by decide)) (by decide), hout]
  have hcnt2_1 : s1.mem.read64 (sp0 + 0x88#64) = 1#64 := by
    rw [hfr32.read64_eq (rw_sp0_sub hrw_sp0_s (sp0 + 0x88#64) 8 (by clear * -; bv_omega))
      (hd32 0x88#64 8 (by decide) (by decide)), hcnt2]
  have hhm1 : HmacStGen s1.mem sp0 C.F (effectiveSalt x.salt) blocks rem :=
    ⟨by rw [hblk_len]; omega,
     by rw [hblk_len]; rcases hikm_len with h | h | h <;> omega,
     by omega,
     hdst1, hpos1, hist1, hcnt1_1, hout_1, hcnt2_1⟩
  exact ⟨⟨hstat1, (Extract.CallingConventionPreserved.sp_eq hcc1).trans hsp,
    (CallingConventionPreserved.x19 hcc1).trans hx19,
    (CallingConventionPreserved.x27 hcc1).trans hx27,
    (CallingConventionPreserved.x29 hcc1).trans hx29, hsaved1, hframe1⟩,
    hpc1.trans hlr, (CallingConventionPreserved.x22 hcc1).trans hx22, hhm1⟩

private theorem seg1c_long_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88LongX img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EFinLongX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    clear * -; bv_omega
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  unfold EFinLongX
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, hx22, ?_⟩
  · dsimp only [State.setMem]
    refine ExtSaved_and_FrameX_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine agreesOutside_sp0_write64 ?_ (by decide))
  · refine HmacStGen.of_copy_19 hhm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

private theorem fin_long_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLongX img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (ERetFinX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x90 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_m16528 : 0 < 16528 ∧ ((sp0 - 16528#64) - (sp0 - 16928#64)).toNat + 16528 ≤ 17360 := by
    have heq : (sp0 - 16528#64) - (sp0 - 16928#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hfin := finalize_fixed_gen_runsToE_base hS.memsetStep hS.compressOneStep
    hpc hstat hx0 hx1
    (by rw [effectiveSalt_length]; decide)
    (by simp; omega)
    hhm
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144.2))
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_176.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_m16528.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 176#64 0x90 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hfin.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcc, hout, hfr'⟩
  rw [hsp] at hfr'
  rw [List.take_append_drop] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16528#64 16528 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_triple hframe hfr' hsub_144.2 hsub_176.2 hsub_m16528.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcc).trans hsp,
    (CallingConventionPreserved.x19 hcc).trans hx19,
    (CallingConventionPreserved.x27 hcc).trans hx27,
    (CallingConventionPreserved.x29 hcc).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcc).trans hx22, hout⟩

/-! ## `extract_none_long_ro_runsToE_ext` and `PqxdhHkdfExtractOk_ext` -/

/-- Pure `RunsToE` contract for `extract` when `x.salt = none` and
`x.ikm.length ∈ {160, 192, 224}` at `17360` B stack under `img.RoDataLoaded s0.mem`. -/
theorem extract_none_long_ro_runsToE_ext {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 16928#64) 17360) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s0 (EPostX C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stkX_sub hRW_stk sp0 432 hsub_432
  have hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928 := by
    rw [saltPtrOf, hsalt]
    exact (disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)).symm
  have h0 := Extract.RunsTo.toE (seg0_long_x_runsTo (img := img) (ext := ext)
    hpc hrun hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)
  have h1 := Extract.RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_long_ro_x_runsTo himg hS hro0 hkf hRW_stk hsalt hd_salt_16928 hsp_al hs
  have h2 := h1.trans fun s hs =>
    Extract.RunsTo.toE (seg1a_long_x_runsTo (img := img) (C := C) (ext := ext) hRW_stk hikm_len hsp_al hs)
  have h3a := h2.trans fun s hs =>
    seg1b1_long_x_runsTo hS hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs
  have h3 := h3a.trans fun s hs =>
    seg1b2_long_x_runsTo hS hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs
  have h4 := h3.trans fun s hs =>
    Extract.RunsTo.toE (seg1c_long_x_runsTo (img := img) (C := C) (ext := ext) hRW_stk hsp_al hs)
  have h5 := h4.trans fun s hs =>
    fin_long_ro_x_runsTo hS hRW_stk hikm_len hsp_al hs
  have h6 := h5.trans fun s hs =>
    Extract.RunsTo.toE (seg2_x_runsTo (img := img) (C := C) (ext := ext) hsp_al hs)
  have h7 := Extract.RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_ro_x_runsTo himg hS hro0 hkf hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    Extract.RunsTo.toE (seg3_x_runsTo (img := img) (C := C) (ext := ext)
      hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

private theorem sep_none_ext_1 (A C G I R : SepProp) :
    (A ∗ C ∗ G ∗ I) ∗ R = A ∗ (G ∗ (C ∗ I ∗ R)) := by ac_rfl

private theorem sep_none_ext_2 (A C G I R : SepProp) :
    (A ∗ C ∗ G ∗ I) ∗ R = G ∗ (A ∗ (C ∗ I ∗ R)) := by ac_rfl

private theorem sep_none_ext_3 (A C G I R : SepProp) :
    (A ∗ C ∗ G ∗ I) ∗ R = C ∗ (A ∗ (G ∗ I ∗ R)) := by ac_rfl

private theorem sep_none_ext_4 (A C G I R : SepProp) :
    (A ∗ C ∗ G ∗ I) ∗ R = C ∗ (G ∗ (A ∗ I ∗ R)) := by ac_rfl

private theorem sep_none_ext_post (P1 P2 C G I R : SepProp) :
    (P1 ∗ P2) ∗ (G ∗ (C ∗ I ∗ R)) = (P1 ∗ P2 ∗ C ∗ G ∗ I) ∗ R := by ac_rfl

/-- `subroutine_ok` for `pqxdhHkdfExtractNoneSpecAt extractStackExt P img` (`17360` B stack). -/
theorem pqxdhHkdfExtractNone_ok_at_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractNoneSpecAt extractStackExt P img) := by
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym =
      img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") := by
    unfold tripleRatchetProgAtExt hkdfExtractSym
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")]
  rw [hfn]
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNoneSpecAt, stackAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx3, hx4, hsp_eq, hikm_len⟩, hsep⟩
  subst hsp_eq
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hstk_eq : memRegion (s0.sp - BitVec.ofNat 64 extractStackExt) extractStackExt =
      memRegion (sp0 - 16928#64) 17360 :=
    congrArg₂ memRegion
      (by dsimp [sp0, extractStackExt, extractStack, newFromSliceStack, extHookStack]; bv_lin) rfl
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let x : ExtractGhost := ⟨ret, 0#64, none, ikmA, bytesToBv8 ikm⟩
  have hikm_bv_len : x.ikm.length = ikm.length := by dsimp [x]; exact bytesToBv8_length ikm
  have hikm_cases : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224 := by
    rwa [hikm_bv_len]
  have hikm_pos : 0 < x.ikm.length := by omega
  have hx4' : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length := by
    rw [hikm_bv_len]; exact hx4
  rw [hstk_eq] at hsep
  have hb_ret := IsBlock.memRegion ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) (rfl : x.ikm.length = x.ikm.length)
  have hb_stk := IsBlock.memRegion (sp0 - 16928#64) 17360
  have hsep_ret_stk := sep_none_ext_1 _ _ _ _ R ▸ hsep
  have hsep_stk := sep_none_ext_2 _ _ _ _ R ▸ hsep
  have hsep_ikm_ret := sep_none_ext_3 _ _ _ _ R ▸ hsep
  have hsep_ikm_stk := sep_none_ext_4 _ _ _ _ R ▸ hsep
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 16928#64) 17360 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA x.ikm.length :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm :=
    (hb_ikm.read hsep_ikm_ret).2
  have hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret hikm_pos (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 16928#64) 17360 :=
    hb_ikm.disjoint hb_stk hikm_pos (by decide) hsep_ikm_stk
  have hruns := extract_none_long_ro_runsToE_ext himg hS (x := x)
    hpc hrun hF0.roData hsp0 hx1 hx3 hx4' rfl rfl hikm_cases hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcallee htr⟩
  dsimp only [pqxdhHkdfExtractNoneSpecAt, stackAt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrameX at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 := by
    have h := congrArg List.length hprk_eq.symm
    rw [bytesToBv8_length] at h
    exact h.trans (length_hmacWith C.F _ _)
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [])
      ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep := S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
    ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost_sep
  rw [hstk_eq, ← sep_none_ext_post]
  exact hpost_sep

theorem pqxdhHkdfExtractNone_ok_of_stubsExt {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractNoneSpecExt P img) :=
  pqxdhHkdfExtractNone_mono_stack (by decide) (by decide)
    (pqxdhHkdfExtractNone_ok_at_ext hP himg hS)

/-- Full `.inImage`-free `PqxdhHkdfExtractOk_ext P img ext` from `HkdfStubsExt img.base C.F ext`. -/
theorem pqxdhHkdfExtract_ok_of_stubsExt {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext) :
    PqxdhHkdfExtractOk_ext P img ext :=
  ⟨pqxdhHkdfExtractNone_ok_of_stubsExt hP himg hS,
   pqxdhHkdfExtractSome_ok_of_stubsExt hP himg hS⟩

end CryptoVerification.E2E.Pqxdh.ResponderCore
