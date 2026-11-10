/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.AsmConstants

@[expose] public section

set_option autoImplicit false

/-!
# Base Layout, Stack, Panic, and Callee Helpers for `signal_session::address`
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

/-! ## Return Offsets and `.fs` Normalization Lemmas -/

def memrchrRetOff : BitVec 64 := 68#64
def parseSidRetOff : BitVec 64 := 116#64
def joinPlusOff : BitVec 64 := 180#64
def loopEntryOff : BitVec 64 := 288#64
def loopHeadOff : BitVec 64 := 292#64
def sxtbCheckOff : BitVec 64 := 256#64
def noneExitOff : BitVec 64 := 352#64
def allocEntryOff : BitVec 64 := 384#64
def shimRetOff : BitVec 64 := 392#64
def allocRetOff : BitVec 64 := 408#64
def memcpyRetOff : BitVec 64 := 428#64

@[simp, arm64_norm]
theorem addr_fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm]
theorem addr_fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem addr_fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem addr_fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := rfl

@[simp, arm64_norm]
theorem addr_fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := rfl

@[simp, arm64_norm]
theorem addr_fs_setPState (s : State) (p : PState) :
    (s.setPState p).fs = s.fs := rfl

@[simp, arm64_norm]
theorem addr_fs_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).fs = s.fs := by
  cases s; rfl

@[simp, arm64_norm]
theorem addr_sub_add (a k m : BitVec 64) : a - k + m = a - (k - m) := by bv_omega

@[simp, arm64_norm]
theorem sp_restore_96 (sp0 : BitVec 64) : sp0 - 96#64 + 96#64 = sp0 := by bv_bits

@[simp, arm64_norm]
theorem zext32_trunc32 (u : BitVec 32) : (u.zeroExtend 64).truncate 32 = u := by bv_bits

@[simp, arm64_norm]
theorem trunc32_zext64_8 (c : BitVec 8) :
    BitVec.truncate 32 (c.zeroExtend 64) = c.zeroExtend 32 := by bv_bits

@[simp, arm64_norm]
theorem trunc8_zext64_32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 8 = u.truncate 8 := by bv_bits

@[simp, arm64_norm]
theorem sbfm_sxtb32_norm (x : BitVec 64) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.truncate 32 x) >>> 0 &&& 255#64 |||
        (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x)).getLsbD 7 = true then
            BitVec.ofNat 64 (num% (2 ^ 64 - 1))
          else 0#64) &&&
          BitVec.ofNat 64 (num% (2 ^ 64 - 256))) =
      BitVec.signExtend 32 (BitVec.truncate 8 x) := by
  bv_bits

/-! ## Call-Site Callee Wrappers -/

theorem addr_fnOff :
    libsignalSessionCode.fnOff addressName = num% (ls_off% "libsignal_cli::address") :=
  ls_lemma% fnOff "libsignal_cli::address"

theorem addr_fnAddr_rel {b : BitVec 64} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff addressName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (tripleRatchetProgAtExt b ext).fnAddr addressName + off =
      (tripleRatchetProgAtExt b ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem addr_memrchr_ok {img : Obj.Image} {ext : String → Option (State → State)}
    (hmemrchr : subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% (ls_off% "core::slice::memchr::memrchr" - ls_off% "libsignal_cli::address"))
      ((memrchrSpec extHookStack).inImage img) := by
  rw [addr_fnAddr_rel (target := "core::slice::memchr::memrchr")
    (by rw [addr_fnOff, ls_stub% "core::slice::memchr::memrchr"]; decide)]
  exact hmemrchr

theorem addr_parseSid_ok {img : Obj.Image} {ext : String → Option (State → State)}
    (hpsid : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr parseSidName)
      ((parseSidCodeStackSpec extHookStack).keepsFs.inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% ((2 ^ 64 + ls_off% parseSidName - ls_off% "libsignal_cli::address") % 2 ^ 64))
      ((parseSidCodeStackSpec extHookStack).keepsFs.inImage img) := by
  rw [addr_fnAddr_rel (target := parseSidName)
    (by rw [addr_fnOff, ls_lemma% fnOff parseSidName]; decide)]
  exact hpsid

theorem addr_shim_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFs : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_cli::address"))
      (session2ShimSpecX.keepsFs.inImage img) := by
  rw [addr_fnAddr_rel (target := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [addr_fnOff, ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"]; decide)]
  have h := hFs.shim extHookStack (Nat.le_refl _) (by unfold extHookStack; decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage, Spec.keepsFs, session2ShimSpecX] at hpre
  have hpre' :
      s0.mem ⊨ ((withStack sessionShimSpec extHookStack).keepsFs.inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec]
    rw [emp_sepConj]
    exact hpre
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hal fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hrest
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hrest)

theorem addr_alloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFs : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::address"))
      ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img) := by
  rw [addr_fnAddr_rel (target := "__rustc::__rust_alloc")
    (by rw [addr_fnOff, ls_stub% "__rustc::__rust_alloc"]; decide)]
  exact hFs.alloc

theorem addr_memcpy_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFs : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::address"))
      (session2MemcpySpecX.keepsFs.inImage img) := by
  rw [addr_fnAddr_rel (target := "memcpy")
    (by rw [addr_fnOff, ls_stub% "memcpy"]; decide)]
  have h := hFs.session_memcpy_region extHookStack (Nat.le_refl _) (by unfold extHookStack; decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' :
      s0.mem ⊨
        ((withStack sessionMemcpyRegionSpec extHookStack).keepsFs.inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, session2MemcpySpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hal fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, session2MemcpySpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hrest)

theorem addr_panic_handle_error (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::address")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := ext) (name := addressName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::address"))
    (by rw [addr_fnOff, ls_stub% "alloc::raw_vec::handle_error"])

/-! ## Stack Frame, `sret` Scratch, and `protocolAddressAt` Folding -/

abbrev subStackSize : Nat := 0x50 + extHookStack

def addrSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem addrSavedRegs_entails_cells8 (sp0 : BitVec 64) (s0 : State) :
    addrSavedRegs sp0 s0 ⊢ cells (sp0 - 64#64) 8 := by
  unfold addrSavedRegs
  apply cells_sub_succ_entails 64 8
  apply cells_sub_succ_entails 56 7
  apply cells_sub_succ_entails 48 6
  apply cells_sub_succ_entails 40 5
  apply cells_sub_succ_entails 32 4
  apply cells_sub_succ_entails 24 3
  apply cells_sub_succ_entails 16 2
  rw [cells_sub_succ sp0 8 1 (by decide) (by decide), Nat.sub_self, cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right _ (Entails.refl _)

theorem cells64_open (sp0 : BitVec 64) :
    cells (sp0 - 64#64) 8 =
      (∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
       ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)) := by
  cells_unfold

theorem stackAt_addr_split (sp0 : BitVec 64) (stk : Nat)
    (hstk : 0xB0 + extHookStack ≤ stk) (hlt : stk ≤ 2 ^ 64) :
    stackAt sp0 stk =
      memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (subStackSize + 96)) ∗
      stackAt (sp0 - 96#64) subStackSize ∗
      memRegion (sp0 - 96#64) 32 ∗
      cells (sp0 - 64#64) 8 := by
  have heq : stk = (subStackSize + 96) + (stk - (subStackSize + 96)) := by
    unfold subStackSize; omega
  conv => lhs; rw [heq]
  rw [stackAt_split_bottom sp0 (subStackSize + 96) (stk - (subStackSize + 96)) (by omega)]
  rw [show subStackSize + 96 = subStackSize + 8 * 12 by omega,
    ProofLib.stackAt_split_cells sp0 subStackSize 12 (by omega)]
  have h12 : cells (sp0 - 96#64) 12 = cells (sp0 - 96#64) 4 ∗ cells (sp0 - 64#64) 8 :=
    cells_split_sub sp0 96 64 4 8 (by decide)
  have hsub_n : subStackSize + 8 * 12 + (stk - (subStackSize + 8 * 12)) = stk := by
    unfold subStackSize; omega
  rw [hsub_n, h12, ← ProofLib.memRegion_cells (sp0 - 96#64) 4 (by decide)]

theorem stackAt_addr_pack (sp0 : BitVec 64) (stk : Nat) (s0 : State)
    (hstk : 0xB0 + extHookStack ≤ stk) (hlt : stk ≤ 2 ^ 64) :
    (memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (subStackSize + 96)) ∗
      stackAt (sp0 - 96#64) subStackSize ∗
      memRegion (sp0 - 96#64) 32 ∗
      addrSavedRegs sp0 s0) ⊢ stackAt sp0 stk := by
  rw [stackAt_addr_split sp0 stk hstk hlt]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (addrSavedRegs_entails_cells8 sp0 s0)))

theorem stackAt_sub_hook (sp1 : BitVec 64) :
    stackAt sp1 subStackSize =
      memRegion (sp1 - BitVec.ofNat 64 subStackSize) 80 ∗
      stackAt sp1 extHookStack := by
  have heq : subStackSize = extHookStack + 80 := by unfold subStackSize; omega
  rw [heq, stackAt_split_bottom sp1 extHookStack 80 (by unfold extHookStack; decide)]

theorem stackAt_sub_parseSid (sp1 : BitVec 64) :
    stackAt sp1 subStackSize =
      stackAt (sp1 - 80#64) extHookStack ∗ stackAt sp1 parseSidFrameStack := by
  have heq : subStackSize = 80 + extHookStack := rfl
  rw [heq, stackAt_split_bottom sp1 80 extHookStack (by unfold extHookStack; decide)]
  have hbot : sp1 - BitVec.ofNat 64 (80 + extHookStack) =
      sp1 - 80#64 - BitVec.ofNat 64 extHookStack := by
    unfold extHookStack
    bv_omega
  dsimp only [stackAt, parseSidFrameStack]
  rw [hbot]

theorem scratch32_split_17 (sp1 : BitVec 64) :
    memRegion sp1 32 =
      memRegion sp1 12 ∗ memRegion (sp1 + 12#64) 17 ∗ memRegion (sp1 + 29#64) 3 := by
  rw [memRegion_split sp1 12 20 (by decide),
    memRegion_split (sp1 + 12#64) 17 3 (by decide)]
  have h29 : sp1 + 12#64 + 17#64 = sp1 + 29#64 := by bv_omega
  rw [h29]

theorem scratch17_pack_byte (out : BitVec 64) (b : BitVec 8) :
    (out ↦₈ b) ∗ memRegion (out + 1#64) 16 ⊢ memRegion out 17 := by
  rw [memRegion_split out 1 16 (by decide)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion out b)

theorem parseSidResultAt_some_pack_tail (out : BitVec 64) (pni : Bool)
    (u : List.Vector (BitVec 8) 16) :
    parseSidResultAt out (some (pni, u)) ⊢
      (out ↦₈ kindByte pni) ∗ memRegion (out + 1#64) 16 := by
  dsimp only [parseSidResultAt]
  generalize hlist : u.toList = bs
  have hlen : bs.length = 16 := hlist ▸ u.2
  rw [← hlen]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (out + 1#64) bs)

theorem out32_open_none (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗ memRegion (out + 8#64) 24 := by
  rw [memRegion_uncons (n := 32) out (by decide) (by decide), sepExists_sepConj_left]

theorem out32_open_some (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ b24 : BitVec 8, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
        ((out + 24#64) ↦₈ b24) ∗ memRegion (out + 25#64) 7) := by
  rw [memRegion_split out 8 24 (by decide),
    memRegion_split (out + 8#64) 8 16 (by decide),
    memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (out + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem vecU8At_pos_init (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8At A v (BitVec.ofNat 64 bs.length) p' bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8At vecHeader
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

theorem protocolAddressAt_pos_init (A : RustAlloc) (out ptr : BitVec 64)
    (name : List (BitVec 8)) (dev : BitVec 8)
    (hpos : 0 < name.length) (hlt : name.length < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    let g : AddrGhost := ⟨⟨BitVec.ofNat 64 name.length, ptr, name⟩, dev⟩
    (out ↦₆₄ BitVec.ofNat 64 name.length) ∗
      ((out + 8#64) ↦₆₄ ptr) ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
      A.live ptr name.length 1 ∗
      (ptr ↦ₛ name) ∗
      ((out + 24#64) ↦₈ dev) ∗
      memRegion (out + 25#64) 7 ⊢
      protocolAddressAt A g out := by
  dsimp only [protocolAddressAt, vecGhostAt]
  have h1 := vecU8At_pos_init A out ptr name hpos hlt hptr
  have hoff24 : asm64% addrDeviceOff = 24#64 := rfl
  have hoff25 : asm64% (addrDeviceOff + 1) = 25#64 := rfl
  have hsz7 : asm% (protocolAddressSize - (addrDeviceOff + 1)) = 7 := rfl
  rw [hoff24, hoff25, hsz7]
  refine Entails.trans ?_ (sepConj_mono_left h1)
  exact Entails.of_eq (by ac_rfl)

/-! ## Callee-Saved Invariant, `spAligned`, `AddrPanicAllow`, and `addr_call_inImage` -/

theorem addrSavedRegs_at_frame {sp0 sp : BitVec 64} (hsp : sp = sp0 - 96#64) (s0 : State) :
    addrSavedRegs sp0 s0 =
      ((sp + 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 40#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((sp + 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 56#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp + 64#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 72#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp + 80#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 88#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold addrSavedRegs; rw [hsp]
  have h1 : sp0 - 96#64 + 32#64 = sp0 - 64#64 ∧ sp0 - 96#64 + 40#64 = sp0 - 56#64 ∧
      sp0 - 96#64 + 48#64 = sp0 - 48#64 ∧ sp0 - 96#64 + 56#64 = sp0 - 40#64 ∧
      sp0 - 96#64 + 64#64 = sp0 - 32#64 ∧ sp0 - 96#64 + 72#64 = sp0 - 24#64 ∧
      sp0 - 96#64 + 80#64 = sp0 - 16#64 ∧ sp0 - 96#64 + 88#64 = sp0 - 8#64 :=
    ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega,
     by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩
  rcases h1 with ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

def AddrUpperSaved (s0 s : State) : Prop :=
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s.fs = s0.fs

theorem AddrUpperSaved.trans_calleeSaved_fs {s0 s sf : State}
    (h1 : AddrUpperSaved s0 s) (h2 : CalleeSavedPreserved s sf) (hfs : sf.fs = s.fs) :
    AddrUpperSaved s0 sf :=
  ⟨h2.2.2.2.2.2.2.1.trans h1.1, h2.2.2.2.2.2.2.2.1.trans h1.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.1, h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.1, hfs.trans h1.2.2.2.2.2⟩

theorem sp_sub_96_spAligned {s0 s : State} (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - 96#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp] at hal0 ⊢
  revert hal0; generalize s0.sp = p; bv_bits

def AddrPanicAllow (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    sf.mem ⊨ (⌜allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R

theorem addrPanicAllow_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf) : AddrPanicAllow s0 sf P_f :=
  fun _ hm =>
    Satisfies.mono (sepConj_mono_left (Entails.pure_right h (entails_anyHeap P_f))) hm

theorem addr_call_inImage {prog : Program} {img : Obj.Image}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (spec.inImage img))
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      allocFailedIn s sf := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (AddrPanicAllow s0)) :
    SepWPp prog ret s P Q (AddrPanicAllow s0) := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp hlr
    (fun R hm => by
      have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hP) hm
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩)
    (fun sf code R' hex hpost => hexit sf code R' hex hpost)
    (fun sf hpan ⟨R', hpost⟩ => by
      have halloc := hpanic sf R' hpan hpost
      have halloc0 : allocFailedIn s0 sf := by simpa [allocFailedIn, htr] using halloc
      exact addrPanicAllow_of_eq halloc0)
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf ⟨hfz, hsym⟩ hpcm hrunm hspm hcsm)
    (fun sf R' hoom_s hpost => (hoom sf (F ∗ R') hoom_s hpost).elim)

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
