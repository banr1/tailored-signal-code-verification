/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeIdentityRootKeys
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on tag 15 (`pq_ratchet_state`)

Proves `mergeFieldX15_ok` (`0x581c`, jump-table byte `0x24` at `.rodata + 0x7902a` dispatching
to `+0xd0`), which invokes `prost::encoding::bytes::merge` (`0x2788`) on the `Vec<u8>` field at
`ss + 0x78` and exits via `+0x758`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX15

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed
    CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral CryptoVerification.E2E.Record.L1GX

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys
  calleeSavedVRegs_setPC_pre_identityRootKeys
  calleeSavedVRegs_setMem_setPC_pre_identityRootKeys

/-! ## Instruction decodes (`0x58ec..0x58fc`) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree mf15 [0x58ec → 0x58fc]

/-! ## Jump-table byte at `.rodata + 0x7902a` -/

def mfRoBytes_mf15 : SepProp :=
  ((mfEntry_identityRootKeys + 40#64 &&& 18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14 - 0x5000)) ↦₈ᵣ 0x24#8

theorem rodata_byte14_eq_mf15 :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14) - num% (ls_xref% 0x2440 0x2444))).take 1 = [0x24#8] := by
  rfl_kernel

theorem holdsBytes_rodata_byte14_mf15 {s : State} (hF : sessionImg0.FrozenLoaded s) :
    Arm64.Obj.HoldsBytes s.mem (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14)) [0x24#8] (fun _ => .ro) :=
  loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14)) (n := 1) (bs := [0x24#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl
      rodata_byte14_eq_mf15

theorem rodata_intro_mf15 {s : State} {P : SepProp} (hF : sessionImg0.FrozenLoaded s)
    (hP : s.mem ⊨ P) : s.mem ⊨ mfRoBytes_mf15 ∗ P := by
  have h1 : (mfEntry_identityRootKeys + 40#64 &&& 18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14 - 0x5000) =
      sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14) := by
    rw [EntryAux.sessionImg0_base]; unfold mfEntry_identityRootKeys; rfl
  unfold mfRoBytes_mf15
  rw [h1, ← pointsToBytesRO_singleton]
  exact Satisfies.of_holdsBytes_ro (holdsBytes_rodata_byte14_mf15 hF) (by decide) hP

/-! ## `prostSSGXAt` split at `ss + 0x78` -/

/-- Portion of `prostSSGXAt` outside the `pq_ratchet_state` `Vec<u8>` at `ss + 0x78`. -/
def prostSSGXRest_mf15 (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A0 ss v.base.lik ∗ vecU8 A0 (ss + 0x18#64) v.base.rik ∗
      vecU8 A0 (ss + 0x30#64) v.base.root ∗
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A0 (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A0 ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_split_mf15 (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A0 ss v = vecU8 A0 (ss + 0x78#64) v.ext.pq ∗ prostSSGXRest_mf15 ss v := by
  unfold prostSSGXAt prostSSGXRest_mf15
  rw [sepConj_left_comm (vecU8 A0 (ss + 0x60#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecOf A0 104 8 _ _ _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x30#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x18#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 ss _) (vecU8 A0 (ss + 0x78#64) _)]
  rfl

theorem genFieldX_tag15 {fl : GenFieldX} (h : fl.tag = 15) : ∃ b, fl = .pq b := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | pendingId i k => simp [GenFieldX.tag] at h
  | pendingSpk i k spk => simp [GenFieldX.tag] at h
  | remReg u => simp [GenFieldX.tag] at h
  | locReg u => simp [GenFieldX.tag] at h
  | abk b => simp [GenFieldX.tag] at h
  | kyber i ct => simp [GenFieldX.tag] at h
  | pq b => exact ⟨b, rfl⟩

/-! ## Post-call epilogue -/

theorem step_cbz_epilogue_mf15 (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mfEntry_identityRootKeys + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) s P Q Qp := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
    (b := sessionImg0.base) (H := H)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x581c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 4)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5820
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 8)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5824
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 12)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5828
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 16)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x582c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 20)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5830
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 24)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5834
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 28)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5838
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 32)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x583c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 36)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5840
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 40)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5844
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 44)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5848
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 48)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x584c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 52)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5850
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 56)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5854
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 60)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5858
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 208)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58ec
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 212)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 216)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 220)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 224)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58fc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1880)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1884)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1888)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1892)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1896)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1900)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1904)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f8c
  change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) (s0.readReg64 .lr) s P Q Qp
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := mfEntry_identityRootKeys + 1880#64)
  wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact step_epilogue_758_identityRootKeys C ctl w56
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    hP hnext

theorem finish_post_mf15 (P : GenFieldX → Prop) (x : MergeFieldXGhost)
    (valPtr w56 : BitVec 64) (b : List (BitVec 8))
    {s0 sf : State} {F_ss R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hpay : x.fld.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGXAt A0 x.ss (x.v.apply x.fld))
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          vecU8 A0 valPtr b ∗
          Prost.sliceCursorAfter x.slot x.ptr
            (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail) x.tail ∗
          (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_mf15))) ∗ R) :
    sf.mem ⊨ (mergeFieldXSpec P).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_mf15 ∗
      ((mfUnusedStack_identityRootKeys s0.sp ∗ stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        ((vecU8 A0 valPtr b ∗ F_ss) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr
            (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail) x.tail ∗
          R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys s0.sp
      s0 w56)) h2
  rw [hss, ← hpay] at h3
  dsimp only [mergeFieldXSpec]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

theorem step_call_and_ret_mf15 (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (P : GenFieldX → Prop)
    (hbytes : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (x : MergeFieldXGhost) (valPtr w56 : BitVec 64)
    (valBs b : List (BitVec 8))
    {s0 sm : State} {F_ss R : SepProp}
    (hpcm : sm.pc = mfEntry_identityRootKeys + 18446744073709539180#64)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hFm : sessionImg0.FrozenLoaded sm)
    (hsymm : sm.symtab = sessionImg0.symtab)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = mfEntry_identityRootKeys + 224#64)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = valPtr)
    (hx2m : sm.readReg64 .x2 = x.bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (htail_lt : (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail).length < 2 ^ 32)
    (hpay : x.fld.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGXAt A0 x.ss (x.v.apply x.fld)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) sm
      (vecU8 A0 valPtr valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr
          (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_mf15))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldXSpec P).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      (mfEntry_identityRootKeys +
        18446744073709539180#64) (Prost.bytesMergeSpec A0 sessionImg0) := by
    rw [bytesMerge_fnAddr_eq_identityRootKeys C ctl]
    exact hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim (fun cap0 => SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, valBs, x.bufRef, x.slot, x.ptr,
     encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail⟩
  refine SepWPp.call (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ (F_ss ∗
      mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_mf15))
    hcall hpcm hrunm hspm_align hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, A0, g]
    have hp1 : sessionImg0.FrozenLoaded sm ∧ sm.symtab = sessionImg0.symtab := ⟨hFm, hsymm⟩
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = valPtr ∧ sm.readReg64 .x2 = x.bufRef ∧
        (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail).length < 2 ^ 63 ∧
        Prost.BytesMergeCapOk cap0
          (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail).length :=
      ⟨hx0m, hx1m, hx2m, Nat.lt_of_lt_of_le htail_lt (by decide),
        Prost.bytesMergeCapOk_of_len_lt32 htail_lt⟩
    rw [hspm, pure_true_emp_identityRootKeys hp1, pure_true_emp_identityRootKeys hp2,
      emp_sepConj, emp_sepConj]
    convert hm using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec,
      Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 hcs2
    have hb64 : b.length < 2 ^ 64 := by
      have hlen_app := htail_lt
      simp only [List.length_append] at hlen_app
      omega
    have hm_eq : mergeBytes .lengthDelimited
        (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail) = some (b, x.tail) := by
      rw [List.append_assoc, mergeBytes_encode b x.tail hb64]
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, g]
    rw [hm_eq]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜Prost.BytesMergeCapOk cap' x.tail.length⌝ ∗ vecU8At A0 valPtr cap' ptr' b) ⊢
        vecU8 A0 valPtr b :=
      Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
        Entails.pure_left fun _ =>
          Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))) ?_
    refine step_cbz_epilogue_mf15 C ctl w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        vecU8 A0 valPtr b ∗
        Prost.sliceCursorAfter x.slot x.ptr
          (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ x.tail) x.tail ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_mf15))
      hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_mf15 P x valPtr w56 b htrf hx0f hpay hss, hspf, hcsf⟩

/-- `SessionStructure::merge_field` contract for tag 15 (`pq_ratchet_state` at `ss + 0x78`). -/
theorem mergeFieldX15_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldXOk C ctl (fun fl => fl.tag = 15) abs := by
  let P15 : GenFieldX → Prop := fun fl => fl.tag = 15
  unfold MergeFieldXOk Serialization.OkAt
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [mergeFieldXSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hP, _, _, hlen, hF, hsym⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_mf15 ∗ prostSSGXAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt s0.sp mergeFieldStack) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_intro_mf15 hF (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_mf15 ∗ prostSSGXAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s0.sp mergeFieldStack,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys s0.sp, prostSSGXAt_eq_split_mf15 x.ss x.v]
  unfold mfRoBytes_mf15
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim (fun w80 => SepWPp.exists_elim (fun w72 =>
    SepWPp.exists_elim (fun w64 => SepWPp.exists_elim (fun w56 =>
      SepWPp.exists_elim (fun w48 => SepWPp.exists_elim (fun w40 =>
        SepWPp.exists_elim (fun w32 => SepWPp.exists_elim (fun w24 =>
          SepWPp.exists_elim (fun w16 => SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
    (b := sessionImg0.base) (H := H)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x581c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 4)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5820
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 8)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5824
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 12)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5828
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 16)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x582c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 20)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5830
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 24)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5834
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 28)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5838
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 32)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x583c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 36)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5840
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 40)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5844
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 44)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5848
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 48)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x584c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 52)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5850
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 56)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5854
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 60)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5858
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 208)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58ec
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 212)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 216)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 220)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58f8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 224)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    mf15_decode_0x58fc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1880)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1884)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1888)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1892)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1896)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1900)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1904)
    CryptoVerification.libsignalSessionCode_fnOff_0x581c (by decide)
    IdentityRootKeysStateSimp.mf234_decode_0x5f8c
  dsimp only [tripleRatchetProgAt] at hpc
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  obtain ⟨b, hfl_eq⟩ := genFieldX_tag15 hP
  have hpay : x.fld.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b := by
    rw [hfl_eq]; rfl
  have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
  rw [hP] at hx1
  rw [hwt] at hx2
  rw [hpay] at hlen ⊢
  simp only [arm64_norm] at hx0 hx1 hx2 hx3
  change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
  refine of_sepWP_inImage_identityRootKeys hF hsym (mid :=
      mfEntry_identityRootKeys + 18446744073709539180#64) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  intro hFm hsymm
  refine SepWPp.congr_pre ?_
    (step_call_and_ret_mf15 C ctl P15 hC.2.2.1 x (x.ss + 0x78#64) w56 x.v.ext.pq b
      (F_ss := prostSSGXRest_mf15 x.ss x.v)
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hlen hpay
      (by rw [hfl_eq, prostSSGXAt_eq_split_mf15]; rfl))
  unfold mfSavedRegs_identityRootKeys mfRoBytes_mf15
  simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX15
