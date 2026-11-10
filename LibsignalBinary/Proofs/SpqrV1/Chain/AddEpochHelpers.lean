/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.New
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import ProofLib.SepLogic.WPp

/-!
# Helper Lemmas and Specifications for `<spqr::chain::Chain>::add_epoch` (`0x61004`, 148 insns)

Pure separation-logic helpers and specifications for `<spqr::chain::Chain>::add_epoch`
(`src/chain.rs:356–375`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false


theorem sub_ok_at_rebase {α : Type} {b : BitVec 64}
    {H : String → Option (State → State)} {spec : Spec α}
    {name callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  rwa [← Program.fnAddr_rel rfl rfl hk]

namespace AgreeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end AgreeStateSimp

/-! ## Symbol Name, Stack Budget, Representation, and Specification -/

abbrev chainAddEpochName : String :=
  "<spqr::chain::Chain>::add_epoch"

/-- `<spqr::chain::Chain>::add_epoch` frame (`0xc0 = 192` B) + `extHookStack`. -/
abbrev chainAddEpochStackX : Nat := 192 + extHookStack

/-- `EpochSecret` at `a` (32 bytes = `0x20`, align 8) with pinned `secret: Vec<u8>`:
- `+0x00..+0x18` (24B): `secret: Vec<u8>` (`vecU8At A a pin.cap pin.ptr es.secret`)
- `+0x18..+0x20` (8B): `epoch: u64` (`(a + 0x18#64) ↦₆₄ es.epoch`) -/
def epochSecretAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (es : EpochSecret) : SepProp :=
  vecU8At A a pin.cap pin.ptr es.secret ∗
    ((a + 0x18#64) ↦₆₄ es.epoch)

/-- `EpochSecret` at `a` (32 bytes) with existentially quantified `VecPin`. -/
def epochSecretRepr (A : RustAlloc) (a : BitVec 64) (es : EpochSecret) : SepProp :=
  ∃∗ pin : VecPin, epochSecretAt A a pin es

/-- Pure `Chain` value constructed by `Chain.addEpoch hkdf self epochSecret` on success. -/
def chainAddEpochVal (hkdf : HkdfFn) (self : Chain) (epochSecret : EpochSecret) : Chain :=
  let genr8r := hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96
  let newLink : ChainEpoch :=
    { send := Chain.cedForDirection genr8r self.dir
      recv := Chain.cedForDirection genr8r self.dir.switch }
  { self with
    currentEpoch := epochSecret.epoch
    nextRoot := genr8r.take 32
    links := self.links ++ [newLink] }

theorem chain_addEpoch_eq_ok (hkdf : HkdfFn) {self : Chain} {epochSecret : EpochSecret}
    (hovf : self.currentEpoch ≠ 0xffffffffffffffff#64)
    (hep : epochSecret.epoch = self.currentEpoch + 1#64) :
    Chain.addEpoch hkdf self epochSecret = .ok (chainAddEpochVal hkdf self epochSecret) := by
  unfold Chain.addEpoch chainAddEpochVal
  have h1 : (self.currentEpoch == 0xffffffffffffffff#64) = false := by simp [hovf]
  have h2 : (epochSecret.epoch != self.currentEpoch + 1#64) = false := by simp [hep]
  simp [h1, h2]

/-- Ghost arguments of `<spqr::chain::Chain>::add_epoch` (`0x61004`). -/
structure ChainAddEpochGhost where
  /-- `self: &mut Chain` pointer (`x0`, 88 bytes). -/
  selfPtr : BitVec 64
  /-- `epoch_secret: EpochSecret` pointer (`x1`, 32 bytes moved in). -/
  esPtr : BitVec 64
  G : ChainGhost
  esPin : VecPin
  self : Chain
  epochSecret : EpochSecret

/-- Spec of `<spqr::chain::Chain>::add_epoch` (`src/chain.rs:356–375`, image offset `0x61004`,
148 instructions):
* `x0 = selfPtr` (`&mut Chain`), `x1 = esPtr` (`epoch_secret: EpochSecret` moved in by pointer).
* If `Chain.addEpoch hkdf x.self x.epochSecret = .error _`, panics in Rust with `sf.trace = s0.trace`.
* If `Chain.addEpoch hkdf x.self x.epochSecret = .ok c'`, updates `selfPtr` to `chainRepr A x.selfPtr c'`
  and consumes `epochSecretAt` (leaving `memRegion x.esPtr 32`), or panics on OOM. -/
def chainAddEpochSpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainAddEpochGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.esPtr ∧
      (x.self.links.length < x.G.linksCap.toNat ∨
        max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63)⌝ ∗
      chainAt A x.selfPtr x.G x.self ∗
      epochSecretAt A x.esPtr x.esPin x.epochSecret ∗
      A.pool ∗ stackAt s.sp chainAddEpochStackX
  post := fun x s0 sf =>
    match Chain.addEpoch hkdf x.self x.epochSecret with
    | .error _ => ⌜False⌝
    | .ok c' =>
      ⌜sf.trace = s0.trace⌝ ∗
        chainRepr A x.selfPtr c' ∗
        memRegion x.esPtr 32 ∗
        A.pool ∗ stackAt s0.sp chainAddEpochStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.addEpoch hkdf x.self x.epochSecret).isOk = false ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainAddEpochOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainAddEpochName)
    ((chainAddEpochSpecX hkdf A).inImage img)

namespace ChainAddEpochFacts

theorem vecDequePhysIdx_lt {head cap i : Nat} (hhead : head < cap) (hi : i < cap) :
    vecDequePhysIdx head cap i < cap := by
  unfold vecDequePhysIdx
  split_ifs <;> omega

theorem vecDequeLogIdx_physIdx {head cap i : Nat} (hhead : head < cap) (hi : i < cap) :
    vecDequeLogIdx head cap (vecDequePhysIdx head cap i) = i := by
  unfold vecDequePhysIdx vecDequeLogIdx
  split_ifs <;> omega

theorem vecDequeLogIdx_ne_of_ne_physIdx {head cap i k : Nat}
    (hhead : head < cap) (_hi : i < cap) (hk : k < cap)
    (hne : k ≠ vecDequePhysIdx head cap i) :
    vecDequeLogIdx head cap k ≠ i := by
  unfold vecDequePhysIdx at hne
  unfold vecDequeLogIdx
  split_ifs at hne ⊢ <;> omega

theorem vecDequeSlotsAt_append_singleton_of_ne {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (x : α) (s n : Nat)
    (hhead : head < cap) (hlen : xs.length < cap)
    (hne : ∀ k < n, s + k < cap ∧ s + k ≠ vecDequePhysIdx head cap xs.length) :
    vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) s n =
      vecDequeSlotsAt elem stride cap head ptr xs s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hs_lt, hs_ne⟩ := hne 0 (Nat.zero_lt_succ n)
    have hlog_ne : vecDequeLogIdx head cap s ≠ xs.length :=
      vecDequeLogIdx_ne_of_ne_physIdx hhead hlen (by omega) (by simpa using hs_ne)
    have ih' := ih (s + 1) fun k hk => by
      have h := hne (k + 1) (by omega)
      have hsk : s + 1 + k = s + (k + 1) := by omega
      rwa [hsk]
    simp only [vecDequeSlotsAt, List.length_append, List.length_singleton, ih']
    by_cases hlt : vecDequeLogIdx head cap s < xs.length
    · have hlt' : vecDequeLogIdx head cap s < xs.length + 1 := by omega
      simp only [hlt, hlt', ↓reduceDIte, List.getElem_append_left hlt]
    · have hlt' : ¬ vecDequeLogIdx head cap s < xs.length + 1 := by omega
      simp only [hlt, hlt', ↓reduceDIte]

/-- All slots of a `VecDeque` buffer except physical slot `s`. -/
def vecDequeSlotsExcept {α : Type} (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (s : Nat) : SepProp :=
  vecDequeSlotsAt elem stride cap head ptr xs 0 s ∗
    vecDequeSlotsAt elem stride cap head ptr xs (s + 1) (cap - 1 - s)

theorem vecDequeSlotsAt_split_physIdx {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α)
    (hhead : head < cap) (hlen : xs.length < cap) :
    let s := vecDequePhysIdx head cap xs.length
    vecDequeSlotsAt elem stride cap head ptr xs 0 cap =
      memRegion (ptr + BitVec.ofNat 64 (s * stride)) stride ∗
        vecDequeSlotsExcept elem stride cap head ptr xs s := by
  intro s
  have hs_lt : s < cap := vecDequePhysIdx_lt hhead hlen
  have hlog : vecDequeLogIdx head cap s = xs.length := vecDequeLogIdx_physIdx hhead hlen
  have hslots :
      vecDequeSlotsAt elem stride cap head ptr xs 0 cap =
        vecDequeSlotsAt elem stride cap head ptr xs 0 (s + (1 + (cap - 1 - s))) := by
    congr 1; omega
  rw [hslots, vecDequeSlotsAt_add, Nat.zero_add, vecDequeSlotsAt_add]
  have hslot :
      vecDequeSlotsAt elem stride cap head ptr xs s 1 =
        memRegion (ptr + BitVec.ofNat 64 (s * stride)) stride := by
    simp [vecDequeSlotsAt, hlog]
  rw [hslot]
  unfold vecDequeSlotsExcept
  ac_rfl

theorem vecDequeSlotsAt_append_singleton_physIdx {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (x : α)
    (hhead : head < cap) (hlen : xs.length < cap) :
    let s := vecDequePhysIdx head cap xs.length
    elem x (ptr + BitVec.ofNat 64 (s * stride)) ∗
      vecDequeSlotsExcept elem stride cap head ptr xs s =
      vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) 0 cap := by
  intro s
  have hs_lt : s < cap := vecDequePhysIdx_lt hhead hlen
  have hlog : vecDequeLogIdx head cap s = xs.length := vecDequeLogIdx_physIdx hhead hlen
  have hslots :
      vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) 0 cap =
        vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) 0 (s + (1 + (cap - 1 - s))) := by
    congr 1; omega
  rw [hslots, vecDequeSlotsAt_add, Nat.zero_add, vecDequeSlotsAt_add]
  have hpre :
      vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) 0 s =
        vecDequeSlotsAt elem stride cap head ptr xs 0 s :=
    vecDequeSlotsAt_append_singleton_of_ne elem stride cap head ptr xs x 0 s hhead hlen
      (fun k hk => ⟨by omega, by omega⟩)
  have hpost :
      vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) (s + 1) (cap - 1 - s) =
        vecDequeSlotsAt elem stride cap head ptr xs (s + 1) (cap - 1 - s) :=
    vecDequeSlotsAt_append_singleton_of_ne elem stride cap head ptr xs x (s + 1) (cap - 1 - s)
      hhead hlen (fun k hk => ⟨by omega, by omega⟩)
  have hslot :
      vecDequeSlotsAt elem stride cap head ptr (xs ++ [x]) s 1 =
        elem x (ptr + BitVec.ofNat 64 (s * stride)) := by
    simp [vecDequeSlotsAt, hlog]
  rw [hpre, hpost, hslot]
  unfold vecDequeSlotsExcept
  ac_rfl

theorem rodata_chainAddEpochInfo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x5bc5c 0x5bc60)) ↦ᵣ chainAddEpochInfo) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x5bc5c 0x5bc60)) (n := 36) (bs := chainAddEpochInfo)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

@[simp] theorem chainAddEpochInfo_length : chainAddEpochInfo.length = 36 := by decide

theorem subroutine_ok_inImage_rodata1_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr1 : BitVec 64} {roBytes1 : List (BitVec 8)}
    {spec : Spec α}
    (hro1 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          (roAddr1 ↦ᵣ roBytes1) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr1 ↦ᵣ roBytes1) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (roAddr1 ↦ᵣ roBytes1) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, hro1 hL.1 hpre⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq; rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Split `stackAt sp chainAddEpochStackX` (`192 + 16384 = 16576` bytes) into
`stackAt (sp - 192#64) extHookStack` and 24 8-byte stack slots in `[sp - 192#64, sp)`. -/
theorem stackAt_chainAddEpochX_split (sp : BitVec 64) :
    stackAt sp chainAddEpochStackX =
      stackAt (sp - 192#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
        ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
        ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11)) ∗
      (∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
        ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
        ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23)) := by
  change memRegion (sp - BitVec.ofNat 64 16576) 16576 =
    memRegion (sp - 192#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16576) (n := 16384) (k := 192)
      (b' := sp - 192#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 192#64) (n := 96) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16576) 16384 ∗
    (memRegion (sp - 192#64) (8 * 12) ∗ memRegion (sp - 96#64) (8 * 12)) = _
  rw [ProofLib.memRegion_cells (sp - 192#64) 12 (by decide),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 192#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16576 := by bv_kernel
  have hc12a : cells (sp - 192#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
        ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
        ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11)) := by
    cells_unfold
  have hc12b : cells (sp - 96#64) 12 =
      (∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
        ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
        ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23)) := by
    cells_unfold
  rw [hsub, hc12a, hc12b]

/-- Rejoin the 24 8-byte stack slots in `[sp - 192#64, sp)` into `stackAt sp chainAddEpochStackX`. -/
theorem rejoin_stack_chainAddEpochX (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
     v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64) :
    stackAt (sp - 192#64) extHookStack ∗
      ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
      ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
      ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11) ∗
      ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
      ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
      ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23) ⊢
      stackAt sp chainAddEpochStackX := by
  rw [stackAt_chainAddEpochX_split sp]
  have h12a :
      ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
      ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
      ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11) ⊢
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
        ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
        ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11)) :=
    Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
          (Entails.sepExists_right v9 (Entails.sepExists_right v10
            (Entails.sepExists_right v11 (Entails.refl _))))))))))))
  have h12b :
      ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
      ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
      ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23) ⊢
      (∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
        ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
        ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23)) :=
    Entails.sepExists_right v12 (Entails.sepExists_right v13 (Entails.sepExists_right v14
      (Entails.sepExists_right v15 (Entails.sepExists_right v16 (Entails.sepExists_right v17
        (Entails.sepExists_right v18 (Entails.sepExists_right v19 (Entails.sepExists_right v20
          (Entails.sepExists_right v21 (Entails.sepExists_right v22
            (Entails.sepExists_right v23 (Entails.refl _))))))))))))
  rw [show stackAt (sp - 192#64) extHookStack ∗
      ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
      ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
      ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11) ∗
      ((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
      ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
      ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23) =
    stackAt (sp - 192#64) extHookStack ∗
      (((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp - 168#64) ↦₆₄ v3) ∗
       ((sp - 160#64) ↦₆₄ v4) ∗ ((sp - 152#64) ↦₆₄ v5) ∗ ((sp - 144#64) ↦₆₄ v6) ∗ ((sp - 136#64) ↦₆₄ v7) ∗
       ((sp - 128#64) ↦₆₄ v8) ∗ ((sp - 120#64) ↦₆₄ v9) ∗ ((sp - 112#64) ↦₆₄ v10) ∗ ((sp - 104#64) ↦₆₄ v11)) ∗
      (((sp - 96#64) ↦₆₄ v12) ∗ ((sp - 88#64) ↦₆₄ v13) ∗ ((sp - 80#64) ↦₆₄ v14) ∗ ((sp - 72#64) ↦₆₄ v15) ∗
       ((sp - 64#64) ↦₆₄ v16) ∗ ((sp - 56#64) ↦₆₄ v17) ∗ ((sp - 48#64) ↦₆₄ v18) ∗ ((sp - 40#64) ↦₆₄ v19) ∗
       ((sp - 32#64) ↦₆₄ v20) ∗ ((sp - 24#64) ↦₆₄ v21) ∗ ((sp - 16#64) ↦₆₄ v22) ∗ ((sp - 8#64) ↦₆₄ v23)) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono h12a h12b)

/-- Fold 12 8-byte cells at `[sp - 192#64, sp - 96#64)` into `memRegion (sp - 192#64) 96`. -/
theorem cells12_192_entails_memRegion_96 (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    ((sp - 192#64) ↦₆₄ w0) ∗ ((sp - 184#64) ↦₆₄ w1) ∗ ((sp - 176#64) ↦₆₄ w2) ∗ ((sp - 168#64) ↦₆₄ w3) ∗
    ((sp - 160#64) ↦₆₄ w4) ∗ ((sp - 152#64) ↦₆₄ w5) ∗ ((sp - 144#64) ↦₆₄ w6) ∗ ((sp - 136#64) ↦₆₄ w7) ∗
    ((sp - 128#64) ↦₆₄ w8) ∗ ((sp - 120#64) ↦₆₄ w9) ∗ ((sp - 112#64) ↦₆₄ w10) ∗ ((sp - 104#64) ↦₆₄ w11) ⊢
      memRegion (sp - 192#64) 96 := by
  rw [show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (sp - 192#64) 12 (by decide)]
  cells_unfold
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.sepExists_right w8
        (Entails.sepExists_right w9 (Entails.sepExists_right w10
          (Entails.sepExists_right w11 (Entails.refl _))))))))))))

/-- Stack address selected by `csel` in `add_epoch` for `cedForDirection genr8r dir`. -/
def cedSrcAddEpoch (sp : BitVec 64) (dir : Direction) : BitVec 64 :=
  match dir with
  | .a2b => sp - 160#64
  | .b2a => sp - 128#64

theorem cedCells_reframe_addEpoch (sp : BitVec 64) (w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64)
    (dir : Direction) :
    ((sp - 160#64) ↦₆₄ w4) ∗ ((sp - 152#64) ↦₆₄ w5) ∗
    ((sp - 144#64) ↦₆₄ w6) ∗ ((sp - 136#64) ↦₆₄ w7) ∗
    ((sp - 128#64) ↦₆₄ w8) ∗ ((sp - 120#64) ↦₆₄ w9) ∗
    ((sp - 112#64) ↦₆₄ w10) ∗ ((sp - 104#64) ↦₆₄ w11) =
    (cedSrcAddEpoch sp dir ↦₆₄ ChainNewFacts.cedWord w4 w8 dir) ∗
    ((cedSrcAddEpoch sp dir + 8#64) ↦₆₄ ChainNewFacts.cedWord w5 w9 dir) ∗
    ((cedSrcAddEpoch sp dir + 16#64) ↦₆₄ ChainNewFacts.cedWord w6 w10 dir) ∗
    ((cedSrcAddEpoch sp dir + 24#64) ↦₆₄ ChainNewFacts.cedWord w7 w11 dir) ∗
    (cedSrcAddEpoch sp dir.switch ↦₆₄ ChainNewFacts.cedWord w4 w8 dir.switch) ∗
    ((cedSrcAddEpoch sp dir.switch + 8#64) ↦₆₄ ChainNewFacts.cedWord w5 w9 dir.switch) ∗
    ((cedSrcAddEpoch sp dir.switch + 16#64) ↦₆₄ ChainNewFacts.cedWord w6 w10 dir.switch) ∗
    ((cedSrcAddEpoch sp dir.switch + 24#64) ↦₆₄ ChainNewFacts.cedWord w7 w11 dir.switch) := by
  cases dir
  · simp (config := { decide := true }) only [cedSrcAddEpoch, ChainNewFacts.cedWord,
      Direction.switch, bv_sub_add_lit, Nat.reduceSub]
  · simp (config := { decide := true }) only [cedSrcAddEpoch, ChainNewFacts.cedWord,
      Direction.switch, bv_sub_add_lit, Nat.reduceSub]
    ac_rfl

theorem hokm_sp_reframe_addEpoch (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    (hall : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))
    (dir : Direction) :
    ((sp - 192#64) ↦ₛ bs) =
      ((sp - 192#64) ↦₆₄ w0) ∗ ((sp - 184#64) ↦₆₄ w1) ∗
      ((sp - 176#64) ↦₆₄ w2) ∗ ((sp - 168#64) ↦₆₄ w3) ∗
      (cedSrcAddEpoch sp dir ↦₆₄ ChainNewFacts.cedWord w4 w8 dir) ∗
      ((cedSrcAddEpoch sp dir + 8#64) ↦₆₄ ChainNewFacts.cedWord w5 w9 dir) ∗
      ((cedSrcAddEpoch sp dir + 16#64) ↦₆₄ ChainNewFacts.cedWord w6 w10 dir) ∗
      ((cedSrcAddEpoch sp dir + 24#64) ↦₆₄ ChainNewFacts.cedWord w7 w11 dir) ∗
      (cedSrcAddEpoch sp dir.switch ↦₆₄ ChainNewFacts.cedWord w4 w8 dir.switch) ∗
      ((cedSrcAddEpoch sp dir.switch + 8#64) ↦₆₄ ChainNewFacts.cedWord w5 w9 dir.switch) ∗
      ((cedSrcAddEpoch sp dir.switch + 16#64) ↦₆₄ ChainNewFacts.cedWord w6 w10 dir.switch) ∗
      ((cedSrcAddEpoch sp dir.switch + 24#64) ↦₆₄ ChainNewFacts.cedWord w7 w11 dir.switch) := by
  have h1 := hall (sp - 192#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc] at h1
  rw [h1, cedCells_reframe_addEpoch sp w4 w5 w6 w7 w8 w9 w10 w11 dir]

theorem chainAddEpoch_fnOff : libsignalSessionCode.fnOff chainAddEpochName = 0x5bc0c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5bc0c

abbrev panicAddOverflowName : String :=
  "core::panicking::panic_const::panic_const_add_overflow"

theorem panicAddOverflow_fnOff :
    libsignalSessionCode.fnOff panicAddOverflowName =
      num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")

abbrev corePanicName : String :=
  "core::panicking::panic"

theorem corePanic_fnOff :
    libsignalSessionCode.fnOff corePanicName =
      num% (ls_off% "core::panicking::panic") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "core::panicking::panic")

@[simp, arm64_norm, wp_norm]
theorem cmp_dir_toI32 (dir : Direction) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 dir.toI32) == 0#32) = (dir.toI32 == 0#32) := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem cmp_dir_toI32_bne (dir : Direction) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 dir.toI32) != 0#32) = (dir.toI32 != 0#32) := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrcAddEpoch_dir (sp : BitVec 64) (dir : Direction) :
    (if ¬(dir.toI32 == 0#32) = true then sp - 128#64 else sp - 160#64) = cedSrcAddEpoch sp dir := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrcAddEpoch_dir_bne (sp : BitVec 64) (dir : Direction) :
    (if (dir.toI32 != 0#32) = true then sp - 128#64 else sp - 160#64) = cedSrcAddEpoch sp dir := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrcAddEpoch_switch (sp : BitVec 64) (dir : Direction) :
    (if ¬(dir.toI32 == 0#32) = true then sp - 160#64 else sp - 128#64) = cedSrcAddEpoch sp dir.switch := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrcAddEpoch_switch_bne (sp : BitVec 64) (dir : Direction) :
    (if (dir.toI32 != 0#32) = true then sp - 160#64 else sp - 128#64) = cedSrcAddEpoch sp dir.switch := by
  cases dir <;> rfl

/-- Remainder of a `Vec<u8>` heap allocation after extracting `ptr ↦ₛ bs`. -/
def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len)

theorem vecU8At_unpack (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length := by
  unfold vecU8At vecHeader vecU8Rest
  rw [show ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
    exact Entails.refl _

theorem vecU8Rest_zero (A : RustAlloc) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hle : bs.length ≤ (0#64).toNat) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A 0#64 ptr bs.length = emp := by
  have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
  subst hbs
  simp [vecU8Rest, pointsToBytes_nil]

theorem vecU8Rest_nonzero_entails (A : RustAlloc) {cap : BitVec 64} (ptr : BitVec 64)
    {bs : List (BitVec 8)} (hcap : cap ≠ 0#64)
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hpos : 0 < cap.toNat := by
    by_contra h0; apply hcap; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  have hlayout : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  unfold vecU8Rest
  simp only [show (cap = 0) = False by exact eq_false hcap, ↓reduceIte]
  have hm := NextKeyInternalFacts.pointsToBytes_memRegion_entails ptr hle hlayout
  rw [show (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
  exact Entails.pure_right hlayout (sepConj_mono_right hm)

theorem cells4_entails_memRegion_32 (a u0 u1 u2 u3 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ⊢
      memRegion a 32 := by
  rw [ChainNewFacts.memRegion_32_cells4 a]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3 (Entails.refl _))))

/-- Split `stackAt sp chainAddEpochStackX` at `sp - 16384#64` for tail-calling `__rust_dealloc`. -/
theorem stackAt_chainAddEpochX_top_split (sp : BitVec 64) :
    stackAt sp chainAddEpochStackX =
      memRegion (sp - BitVec.ofNat 64 chainAddEpochStackX) 192 ∗ stackAt sp extHookStack := by
  change memRegion (sp - BitVec.ofNat 64 16576) 16576 =
    memRegion (sp - BitVec.ofNat 64 16576) 192 ∗ memRegion (sp - BitVec.ofNat 64 16384) 16384
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16576) (n := 192) (k := 16384)
    (b' := sp - BitVec.ofNat 64 16384) rfl (by bv_omega) (by decide)

/-- Untouched fields of `Chain` during `add_epoch` (`send_epoch`, `params`, and 4B tail padding). -/
def chainUntouchedAt (a : BitVec 64) (c : Chain) : SepProp :=
  ((a + 0x40#64) ↦₆₄ c.sendEpoch) ∗
    chainParamsAt (a + 0x48#64) c.params ∗
    memRegion (a + 0x54#64) 4

theorem chainAt_unpack_addEpoch (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) :
    chainAt A a G c ⊢
      ⌜G.epochs.length = c.links.length ∧ c.links.length ≤ G.linksCap.toNat ∧
        c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧ G.nextRoot.cap.toNat < 2 ^ 63 ∧
        G.nextRoot.ptr ≠ 0⌝ ∗
      (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
      ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      (G.nextRoot.ptr ↦ₛ c.nextRoot) ∗ vecU8Rest A G.nextRoot.cap G.nextRoot.ptr c.nextRoot.length ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗
      ((a + 80#64) ↦₃₂ c.dir.toI32) ∗
      chainUntouchedAt a c := by
  have hring_len :
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ⊢
      ⌜(G.epochs.zip c.links).length ≤ G.linksCap.toNat⌝ ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
          G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) := by
    unfold vecDequeRingBuf
    refine Entails.pure_left fun ⟨hle, hcap, hptr, hhead⟩ =>
      Entails.pure_right hle (Entails.pure_right ⟨hle, hcap, hptr, hhead⟩ (Entails.refl _))
  unfold chainAt vecDequeAt vecDequeHeader directionAt chainUntouchedAt
  have hnr := vecU8At_unpack A (a + 0x20#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnr
  rw [show ⌜G.epochs.length = c.links.length⌝ ∗
      (((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
        ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length)) ∗
       vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links)) ∗
      vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      chainParamsAt (a + 72#64) c.params ∗ ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ memRegion (a + 84#64) 4 =
    ⌜G.epochs.length = c.links.length⌝ ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
      ((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
       ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗ ((a + 56#64) ↦₆₄ c.currentEpoch) ∗
       ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ (((a + 64#64) ↦₆₄ c.sendEpoch) ∗ chainParamsAt (a + 72#64) c.params ∗ memRegion (a + 84#64) 4)) by ac_rfl]
  refine Entails.pure_left fun hlen_eq => ?_
  refine Entails.trans (sepConj_mono_left hring_len) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hlen_le => ?_
  have hzip_len : (G.epochs.zip c.links).length = c.links.length := by simp [hlen_eq]
  rw [hzip_len] at hlen_le ⊢
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hnr)) ?_
  rw [show vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      (⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧ G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
       ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
       (G.nextRoot.ptr ↦ₛ c.nextRoot) ∗ vecU8Rest A G.nextRoot.cap G.nextRoot.ptr c.nextRoot.length) ∗
      ((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
       ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗ ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 80#64) ↦₃₂ c.dir.toI32) ∗
       (((a + 64#64) ↦₆₄ c.sendEpoch) ∗ chainParamsAt (a + 72#64) c.params ∗ memRegion (a + 84#64) 4)) =
    ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧ G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
      ((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
       vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
       ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
       (G.nextRoot.ptr ↦ₛ c.nextRoot) ∗ vecU8Rest A G.nextRoot.cap G.nextRoot.ptr c.nextRoot.length ∗
       ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 80#64) ↦₃₂ c.dir.toI32) ∗
       (((a + 64#64) ↦₆₄ c.sendEpoch) ∗ chainParamsAt (a + 72#64) c.params ∗ memRegion (a + 84#64) 4)) by ac_rfl]
  refine Entails.pure_left fun ⟨hnr_le, hnr_lt, hnr_ptr⟩ =>
    Entails.pure_right ⟨hlen_eq, hlen_le, hnr_le, hnr_lt, hnr_ptr⟩ (Entails.refl _)

theorem epochSecretAt_unpack (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (es : EpochSecret) :
    epochSecretAt A a pin es ⊢
      ⌜es.secret.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
      ((a + 24#64) ↦₆₄ es.epoch) ∗ (pin.ptr ↦ₛ es.secret) ∗ vecU8Rest A pin.cap pin.ptr es.secret.length := by
  unfold epochSecretAt
  refine Entails.trans (sepConj_mono_left (vecU8At_unpack A a pin.cap pin.ptr es.secret)) ?_
  rw [show (⌜es.secret.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
      (pin.ptr ↦ₛ es.secret) ∗ vecU8Rest A pin.cap pin.ptr es.secret.length) ∗ ((a + 24#64) ↦₆₄ es.epoch) =
    ⌜es.secret.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
      ((a + 24#64) ↦₆₄ es.epoch) ∗ (pin.ptr ↦ₛ es.secret) ∗ vecU8Rest A pin.cap pin.ptr es.secret.length by ac_rfl]
  exact Entails.refl _

/-- Split `vecDequeRingBuf` when `xs.length < cap.toNat` into the 14 cells of the empty slot at
`s = vecDequePhysIdx head.toNat cap.toNat xs.length` and `vecDequeSlotsExcept`. -/
theorem vecDequeRingBuf_split_physIdx (A : RustAlloc) (cap ptr head : BitVec 64)
    (xs : List (ChainEpochGhost × ChainEpoch)) (hlen : xs.length < cap.toNat) :
    let s := vecDequePhysIdx head.toNat cap.toNat xs.length
    let slotPtr := ptr + BitVec.ofNat 64 (s * 112)
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head xs ⊢
      ∃∗ d1 : BitVec 32, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ d0 : BitVec 32,
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ⌜head.toNat < cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (slotPtr ↦₆₄ u0) ∗ ((slotPtr + 8#64) ↦₆₄ u1) ∗ ((slotPtr + 16#64) ↦₆₄ u2) ∗
        ((slotPtr + 24#64) ↦₆₄ u3) ∗ ((slotPtr + 32#64) ↦₆₄ u4) ∗ ((slotPtr + 40#64) ↦₆₄ u5) ∗
        ((slotPtr + 48#64) ↦₃₂ d0) ∗ memRegion (slotPtr + 52#64) 4 ∗
        ((slotPtr + 56#64) ↦₆₄ w0) ∗ ((slotPtr + 64#64) ↦₆₄ w1) ∗ ((slotPtr + 72#64) ↦₆₄ w2) ∗
        ((slotPtr + 80#64) ↦₆₄ w3) ∗ ((slotPtr + 88#64) ↦₆₄ w4) ∗ ((slotPtr + 96#64) ↦₆₄ w5) ∗
        ((slotPtr + 104#64) ↦₃₂ d1) ∗ memRegion (slotPtr + 108#64) 4 ∗
        vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s := by
  intro s slotPtr
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hlen
  unfold vecDequeRingBuf chainEpochSize chainEpochAlign
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_left fun ⟨_, hcap_lt, hptr, hhead⟩ => ?_
  rw [vecDequeSlotsAt_split_physIdx (chainEpochAt A) 112 cap.toNat head.toNat ptr xs hhead hlen]
  change A.live ptr (cap.toNat * 112) 8 ∗
      (memRegion slotPtr 112 ∗ vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s) ⊢ _
  rw [ProofLib.memRegion_split' (b := slotPtr) (n := 56) (k := 56) (b' := slotPtr + 56#64) rfl (by bv_omega) (by decide),
    ChainNewFacts.memRegion_56_ced_split slotPtr, ChainNewFacts.memRegion_56_ced_split (slotPtr + 56#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun d1 => Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
    Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun d0 => Entails.sepExists_elim fun u0 =>
    Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
  refine Entails.sepExists_right d1 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right d0 (Entails.sepExists_right u0
        (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.sepExists_right u3
          (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))))))))))
  exact Entails.pure_right ⟨hhead, hcap_lt, hptr⟩ (Entails.refl _)

/-- Fold the updated `Chain` fields, the newly initialized `ChainEpoch` slot at `slotPtr`,
and `vecDequeSlotsExcept` into `chainRepr A selfPtr (chainAddEpochVal hkdf self epochSecret)`. -/
theorem chainRepr_addEpoch_intro (A : RustAlloc) (hkdf : HkdfFn)
    (selfPtr cap ptr head p_root' p_send_next p_send_prev p_recv_next p_recv_prev : BitVec 64)
    (G : ChainGhost) (self : Chain) (epochSecret : EpochSecret)
    (hlen_eq : G.epochs.length = self.links.length) (hlen_lt : self.links.length < cap.toNat)
    (hhead : head.toNat < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hroot : p_root' ≠ 0#64)
    (hgen : (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).length = 96) :
    let s := vecDequePhysIdx head.toNat cap.toNat self.links.length
    let slotPtr := ptr + BitVec.ofNat 64 (s * 112)
    let genr8r := hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96
    (selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head) ∗
    ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1)) ∗ A.live ptr (cap.toNat * 112) 8 ∗
    chainEpochDirectionAt A slotPtr
      { next := { cap := 32#64, ptr := p_send_next }, prev := { cap := 72#64, ptr := p_send_prev } }
      (Chain.cedForDirection genr8r self.dir) ∗
    chainEpochDirectionAt A (slotPtr + 56#64)
      { next := { cap := 32#64, ptr := p_recv_next }, prev := { cap := 72#64, ptr := p_recv_prev } }
      (Chain.cedForDirection genr8r self.dir.switch) ∗
    vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (G.epochs.zip self.links) s ∗
    ((selfPtr + 32#64) ↦₆₄ 32#64) ∗ ((selfPtr + 40#64) ↦₆₄ p_root') ∗ ((selfPtr + 48#64) ↦₆₄ 32#64) ∗
    A.live p_root' 32 1 ∗ (p_root' ↦ₛ genr8r.take 32) ∗ ((selfPtr + 56#64) ↦₆₄ epochSecret.epoch) ∗
    ((selfPtr + 80#64) ↦₃₂ self.dir.toI32) ∗ chainUntouchedAt selfPtr self ⊢
      chainRepr A selfPtr (chainAddEpochVal hkdf self epochSecret) := by
  intro s slotPtr genr8r
  let gce_new : ChainEpochGhost :=
    { send := { next := { cap := 32#64, ptr := p_send_next }, prev := { cap := 72#64, ptr := p_send_prev } }
      recv := { next := { cap := 32#64, ptr := p_recv_next }, prev := { cap := 72#64, ptr := p_recv_prev } } }
  let newLink : ChainEpoch :=
    { send := Chain.cedForDirection genr8r self.dir
      recv := Chain.cedForDirection genr8r self.dir.switch }
  refine Entails.sepExists_right
    { linksCap := cap, linksPtr := ptr, linksHead := head,
      epochs := G.epochs ++ [gce_new], nextRoot := { cap := 32#64, ptr := p_root' } } ?_
  have hzip_len : (G.epochs.zip self.links).length = self.links.length := by simp [hlen_eq]
  have hzip_lt : (G.epochs.zip self.links).length < cap.toNat := by omega
  have hzip_app : (G.epochs ++ [gce_new]).zip (self.links ++ [newLink]) =
      G.epochs.zip self.links ++ [(gce_new, newLink)] := List.zip_append hlen_eq
  have hslots := vecDequeSlotsAt_append_singleton_physIdx
    (chainEpochAt A) 112 cap.toNat head.toNat ptr (G.epochs.zip self.links) (gce_new, newLink) hhead hzip_lt
  dsimp only at hslots; rw [hzip_len] at hslots
  have hce : chainEpochDirectionAt A slotPtr gce_new.send newLink.send ∗
      chainEpochDirectionAt A (slotPtr + 56#64) gce_new.recv newLink.recv =
      chainEpochAt A (gce_new, newLink) slotPtr := rfl
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hlen_lt
  have hlen_root : (genr8r.take 32).length = 32 :=
    List.length_take_of_le (by change 32 ≤ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).length; omega)
  have hroot_vec := ChainNewFacts.vecU8At_32_intro A (selfPtr + 32#64) p_root' hlen_root hroot
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hroot_vec
  unfold chainAt chainAddEpochVal vecDequeAt vecDequeHeader vecDequeRingBuf
    directionAt chainUntouchedAt chainEpochSize chainEpochAlign
  dsimp only; rw [hzip_app]
  have hlen_app1 : (G.epochs ++ [gce_new]).length = (self.links ++ [newLink]).length := by simp [hlen_eq]
  have hlen_app2 : (G.epochs.zip self.links ++ [(gce_new, newLink)]).length = self.links.length + 1 := by simp [hzip_len]
  have hlen_app_le : self.links.length + 1 ≤ cap.toNat := by omega
  rw [hlen_app2]; simp only [hcap_ne, ↓reduceIte]
  rw [show (selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head) ∗
      ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1)) ∗ A.live ptr (cap.toNat * 112) 8 ∗
      chainEpochDirectionAt A slotPtr gce_new.send newLink.send ∗
      chainEpochDirectionAt A (slotPtr + 56#64) gce_new.recv newLink.recv ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (G.epochs.zip self.links) s ∗
      ((selfPtr + 32#64) ↦₆₄ 32#64) ∗ ((selfPtr + 40#64) ↦₆₄ p_root') ∗ ((selfPtr + 48#64) ↦₆₄ 32#64) ∗
      A.live p_root' 32 1 ∗ (p_root' ↦ₛ genr8r.take 32) ∗ ((selfPtr + 56#64) ↦₆₄ epochSecret.epoch) ∗
      ((selfPtr + 80#64) ↦₃₂ self.dir.toI32) ∗ (((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
       chainParamsAt (selfPtr + 72#64) self.params ∗ memRegion (selfPtr + 84#64) 4) =
    (((selfPtr + 32#64) ↦₆₄ 32#64) ∗ ((selfPtr + 40#64) ↦₆₄ p_root') ∗ ((selfPtr + 48#64) ↦₆₄ 32#64) ∗
      A.live p_root' 32 1 ∗ (p_root' ↦ₛ genr8r.take 32)) ∗
    (((selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head) ∗
      ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1))) ∗
     (A.live ptr (cap.toNat * 112) 8 ∗ ((chainEpochDirectionAt A slotPtr gce_new.send newLink.send ∗
        chainEpochDirectionAt A (slotPtr + 56#64) gce_new.recv newLink.recv) ∗
       vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (G.epochs.zip self.links) s)) ∗
     ((selfPtr + 56#64) ↦₆₄ epochSecret.epoch) ∗ ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
     chainParamsAt (selfPtr + 72#64) self.params ∗ ((selfPtr + 80#64) ↦₃₂ self.dir.toI32) ∗
     memRegion (selfPtr + 84#64) 4) by ac_rfl]
  rw [hce, hslots]
  refine Entails.trans (sepConj_mono_left hroot_vec) ?_
  rw [show ⌜(G.epochs ++ [gce_new]).length = (self.links ++ [newLink]).length⌝ ∗
      (((selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head) ∗
        ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1))) ∗
       (⌜self.links.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0 ∧ head.toNat < cap.toNat⌝ ∗
        (A.live ptr (cap.toNat * 112) 8 ∗ vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr
           (G.epochs.zip self.links ++ [(gce_new, newLink)]) 0 cap.toNat))) ∗
      vecU8At A (selfPtr + 32#64) 32#64 p_root' (genr8r.take 32) ∗
      ((selfPtr + 56#64) ↦₆₄ epochSecret.epoch) ∗ ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
      chainParamsAt (selfPtr + 72#64) self.params ∗ ((selfPtr + 80#64) ↦₃₂ self.dir.toI32) ∗
      memRegion (selfPtr + 84#64) 4 =
    ⌜(G.epochs ++ [gce_new]).length = (self.links ++ [newLink]).length⌝ ∗
    ⌜self.links.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0 ∧ head.toNat < cap.toNat⌝ ∗
    (vecU8At A (selfPtr + 32#64) 32#64 p_root' (genr8r.take 32) ∗
      (((selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head) ∗
        ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1))) ∗
       (A.live ptr (cap.toNat * 112) 8 ∗ vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr
          (G.epochs.zip self.links ++ [(gce_new, newLink)]) 0 cap.toNat) ∗
       ((selfPtr + 56#64) ↦₆₄ epochSecret.epoch) ∗ ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
       chainParamsAt (selfPtr + 72#64) self.params ∗ ((selfPtr + 80#64) ↦₃₂ self.dir.toI32) ∗
       memRegion (selfPtr + 84#64) 4)) by ac_rfl]
  exact Entails.pure_right hlen_app1
    (Entails.pure_right ⟨hlen_app_le, hcap_lt, hptr, hhead⟩ (Entails.refl _))

theorem onPanic_addEpoch_of_trace_eq {P : State → Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜P sf ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  refine Entails.trans (NextKeyInternalFacts.onPanic_entails_of_trace_eq htr) ?_
  exact Entails.pure_left fun h => Entails.pure_right (Or.inr h) (Entails.refl _)

open Lean Elab Tactic in
elab "wp_norm_hyp " h:ident : tactic => do
  wpNormAndSplitHyp h

open Lean Elab Tactic in
elab "wp_split_join " hsp:ident hcs:ident : tactic => do
  wpNormAndSplitHyp hsp
  wpNormAndSplitHyp hcs
  wpElimSpatialContext hsp

open Lean Elab Tactic in
elab "wpp_call_inImage_addEpoch " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_addEpoch: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_addEpoch_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end ChainAddEpochFacts

open ChainAddEpochFacts

theorem vecU8Rest_eq_zero (A : RustAlloc) {cap : BitVec 64} (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hcap : cap = 0#64) (hle : bs.length ≤ cap.toNat) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length = emp := by
  subst hcap; exact vecU8Rest_zero A ptr hle

theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

/-! ## Contract-Backed (`*Ext`) Parallel Specification (`chainAddEpochStackExt = 17808` B) -/

/-- `<spqr::chain::Chain>::add_epoch` frame (`192` B) + `hkdfToSliceStackExt` (`17616` B). -/
abbrev chainAddEpochStackExt : Nat := 192 + hkdfToSliceStackExt

/-- Contract-backed spec of `<spqr::chain::Chain>::add_epoch` at `chainAddEpochStackExt` (`17808` B). -/
def chainAddEpochSpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainAddEpochGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.esPtr ∧
      (x.self.links.length < x.G.linksCap.toNat ∨
        max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63)⌝ ∗
      chainAt A x.selfPtr x.G x.self ∗
      epochSecretAt A x.esPtr x.esPin x.epochSecret ∗
      A.pool ∗ stackAt s.sp chainAddEpochStackExt
  post := fun x s0 sf =>
    match Chain.addEpoch hkdf x.self x.epochSecret with
    | .error _ => ⌜False⌝
    | .ok c' =>
      ⌜sf.trace = s0.trace⌝ ∗
        chainRepr A x.selfPtr c' ∗
        memRegion x.esPtr 32 ∗
        A.pool ∗ stackAt s0.sp chainAddEpochStackExt
  onPanic := fun x s0 sf =>
    ⌜((Chain.addEpoch hkdf x.self x.epochSecret).isOk = false ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainAddEpochOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainAddEpochName)
    ((chainAddEpochSpecExt hkdf A).inImage img)

theorem stackAt_chainAddEpochExt_eq (sp : BitVec 64) :
    stackAt sp chainAddEpochStackExt =
      memRegion (sp - 17808#64) 1232 ∗ stackAt sp chainAddEpochStackX := by
  change memRegion (sp - BitVec.ofNat 64 17808) 17808 =
    memRegion (sp - 17808#64) 1232 ∗ memRegion (sp - BitVec.ofNat 64 16576) 16576
  exact ProofLib.memRegion_split' (b := sp - 17808#64) (n := 1232) (k := 16576)
    (b' := sp - 16576#64) rfl (by bv_omega) (by decide)

theorem stackAt_chainAddEpoch_hkdfExt_eq (sp sp' : BitVec 64) (hsp : sp' = sp - 192#64) :
    memRegion (sp - 17808#64) 1232 ∗ stackAt sp' extHookStack =
      stackAt sp' hkdfToSliceStackExt := by
  subst hsp
  change memRegion (sp - 17808#64) 1232 ∗ memRegion (sp - 192#64 - BitVec.ofNat 64 16384) 16384 =
    memRegion (sp - 192#64 - BitVec.ofNat 64 17616) 17616
  have h1 : sp - 192#64 - BitVec.ofNat 64 17616 = sp - 17808#64 := by bv_kernel
  have h2 : sp - 192#64 - BitVec.ofNat 64 16384 = sp - 16576#64 := by bv_kernel
  rw [h1, h2]
  exact (ProofLib.memRegion_split' (b := sp - 17808#64) (n := 1232) (k := 16384)
    (b' := sp - 16576#64) rfl (by bv_omega) (by decide)).symm

theorem sub_ok_conseq_entails {α : Type} {prog : Program} {pc : BitVec 64}
    {S₁ S₂ : Spec α} (h : subroutine_ok prog pc S₁)
    (hpre : ∀ x s0, S₂.pre x s0 ⊢ S₁.pre x s0)
    (hpost : ∀ x s0 sf, S₁.post x s0 sf ⊢ S₂.post x s0 sf)
    (hpan : ∀ x s0 sf, S₁.onPanic x s0 sf = S₂.onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, S₁.onExit x c s0 sf = S₂.onExit x c s0 sf)
    (hoom : ∀ x s0 sf, S₁.onOom x s0 sf = S₂.onOom x s0 sf) :
    subroutine_ok prog pc S₂ := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hm hsp _ => ?_
  refine h.mono_outcome x R s0 hpc hrun (Satisfies.mono (sepConj_mono_left (hpre x s0)) hm) hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hp⟩ | ⟨h1, hp⟩ | ⟨c, h1, hp⟩ | ⟨h1, hp⟩
  · exact Or.inl ⟨h1, h2, Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp⟩
  · rw [hpan] at hp; exact Or.inr (Or.inl ⟨h1, hp⟩)
  · rw [hexit] at hp; exact Or.inr (Or.inr (Or.inl ⟨c, h1, hp⟩))
  · rw [hoom] at hp; exact Or.inr (Or.inr (Or.inr ⟨h1, hp⟩))

section AddEpochFrameHelpers
open ChainAddEpochFacts ChainNewFacts

/-- The 12 callee-saved stack slots `[sp - 96#64 .. sp - 8#64]` saved in the prologue of `add_epoch`. -/
def calleeSavedStackAt (s0 : State) (v15 : BitVec 64) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗ ((s0.sp - 72#64) ↦₆₄ v15) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem calleeSavedStackAt_def (s0 : State) (v15 : BitVec 64) :
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗ ((s0.sp - 72#64) ↦₆₄ v15) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) =
    calleeSavedStackAt s0 v15 := rfl

/-- Frame of 30 spatial atoms untouched between `0x610c8` (`entry + 196#64`) and `0x611b0` (`entry + 428#64`). -/
def addEpochMidFrame (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (s0 : State) (v15 w0 w1 w2 w3 p_root' : BitVec 64)
    (esPin : VecPin) (self : Chain) (epochSecret : EpochSecret) : SepProp :=
  ((img.base + bv% (ls_xref% 0x5bc5c 0x5bc60)) ↦ᵣ chainAddEpochInfo) ∗
  ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
  ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
  calleeSavedStackAt s0 v15 ∗
  ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ 32#64) ∗
  ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ p_root') ∗
  ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ 32#64) ∗
  ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
  ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
  chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
  ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
  ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
  ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
  (esPin.ptr ↦ₛ epochSecret.secret) ∗
  vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
  A.live p_root' 32 1 ∗
  (p_root' ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32)

theorem addEpochMidFrame_def (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (s0 : State) (v15 w0 w1 w2 w3 p_root' : BitVec 64)
    (esPin : VecPin) (self : Chain) (epochSecret : EpochSecret) :
    ((img.base + bv% (ls_xref% 0x5bc5c 0x5bc60)) ↦ᵣ chainAddEpochInfo) ∗
    ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
    ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
    calleeSavedStackAt s0 v15 ∗
    ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ p_root') ∗
    ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
    ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
    chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
    ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
    ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
    ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
    (esPin.ptr ↦ₛ epochSecret.secret) ∗
    vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
    A.live p_root' 32 1 ∗
    (p_root' ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32) =
    addEpochMidFrame img hkdf A s0 v15 w0 w1 w2 w3 p_root' esPin self epochSecret := rfl

/-- The 8 stack cells for `cedSrcAddEpoch` (`a2b` and `b2a` next-key slices). -/
def cedStackBothAt (sp : BitVec 64) (w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) (dir : Direction) : SepProp :=
  (cedSrcAddEpoch sp dir ↦₆₄ cedWord w4 w8 dir) ∗ ((cedSrcAddEpoch sp dir + 8#64) ↦₆₄ cedWord w5 w9 dir) ∗
  ((cedSrcAddEpoch sp dir + 16#64) ↦₆₄ cedWord w6 w10 dir) ∗ ((cedSrcAddEpoch sp dir + 24#64) ↦₆₄ cedWord w7 w11 dir) ∗
  (cedSrcAddEpoch sp dir.switch ↦₆₄ cedWord w4 w8 dir.switch) ∗ ((cedSrcAddEpoch sp dir.switch + 8#64) ↦₆₄ cedWord w5 w9 dir.switch) ∗
  ((cedSrcAddEpoch sp dir.switch + 16#64) ↦₆₄ cedWord w6 w10 dir.switch) ∗ ((cedSrcAddEpoch sp dir.switch + 24#64) ↦₆₄ cedWord w7 w11 dir.switch)

theorem cedStackBothAt_def (sp : BitVec 64) (w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) (dir : Direction) :
    (cedSrcAddEpoch sp dir ↦₆₄ cedWord w4 w8 dir) ∗ ((cedSrcAddEpoch sp dir + 8#64) ↦₆₄ cedWord w5 w9 dir) ∗
    ((cedSrcAddEpoch sp dir + 16#64) ↦₆₄ cedWord w6 w10 dir) ∗ ((cedSrcAddEpoch sp dir + 24#64) ↦₆₄ cedWord w7 w11 dir) ∗
    (cedSrcAddEpoch sp dir.switch ↦₆₄ cedWord w4 w8 dir.switch) ∗ ((cedSrcAddEpoch sp dir.switch + 8#64) ↦₆₄ cedWord w5 w9 dir.switch) ∗
    ((cedSrcAddEpoch sp dir.switch + 16#64) ↦₆₄ cedWord w6 w10 dir.switch) ∗ ((cedSrcAddEpoch sp dir.switch + 24#64) ↦₆₄ cedWord w7 w11 dir.switch) =
    cedStackBothAt sp w4 w5 w6 w7 w8 w9 w10 w11 dir := rfl

theorem vecDequeAt_fold_addEpoch (A : RustAlloc) (a cap ptr head : BitVec 64)
    (G : ChainGhost) (self : Chain) (hlen_eq : G.epochs.length = self.links.length) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ head) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head (G.epochs.zip self.links) ⊢
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) a cap ptr head (G.epochs.zip self.links) := by
  have hzip : (G.epochs.zip self.links).length = self.links.length := by simp [hlen_eq]
  unfold vecDequeAt vecDequeHeader; rw [hzip, sepConj_assoc, sepConj_assoc, sepConj_assoc]; exact Entails.refl _

theorem vecDequeAt_unfold_addEpoch (A : RustAlloc) (a cap ptr head : BitVec 64)
    (G : ChainGhost) (self : Chain) (hlen_eq : G.epochs.length = self.links.length) :
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) a cap ptr head (G.epochs.zip self.links) ⊢
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ head) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head (G.epochs.zip self.links) := by
  have hzip : (G.epochs.zip self.links).length = self.links.length := by simp [hlen_eq]
  unfold vecDequeAt vecDequeHeader; rw [hzip, sepConj_assoc, sepConj_assoc, sepConj_assoc]; exact Entails.refl _

theorem SepWP.unfold_vecDeque_bind {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop}
    (A : RustAlloc) (a cap : BitVec 64) {ptr head : BitVec 64}
    (G : ChainGhost) (self : Chain) (hlen_eq : G.epochs.length = self.links.length)
    (hf : P = vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) a cap ptr head (G.epochs.zip self.links) ∗ F)
    (h : ∀ ptr1 head1 : BitVec 64,
      SepWP prog pc s
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ head1) ∗
          ((a + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
          vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr1 head1 (G.epochs.zip self.links)) ∗ F)
        post) :
    SepWP prog pc s P post :=
  SepWP.fold (vecDequeAt_unfold_addEpoch A a cap ptr head G self hlen_eq) hf (h ptr head)

theorem len_lt_newCapChainEpoch {len : Nat} {cap : BitVec 64}
    (heq : len = cap.toNat) (hgrow_ok : max (2 * cap.toNat) 4 * chainEpochSize < 2 ^ 63) :
    len < (newCapChainEpoch cap).toNat := by
  unfold newCapChainEpoch chainEpochSize at *
  have hlt : max (2 * cap.toNat) 4 < 2 ^ 64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega

theorem ofNat_len_ne_cap {len : Nat} {cap : BitVec 64} (hlt : len < cap.toNat) :
    BitVec.ofNat 64 len ≠ cap := by
  intro heq
  have hlt64 : len < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  have htoNat := congrArg BitVec.toNat heq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at htoNat; omega

theorem cmn_one_false_of_ne {x : BitVec 64} (h : x ≠ 0xffffffffffffffff#64) :
    (x + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; apply h; revert heq; bv_kernel

theorem sub_eq_zero_false_of_ne {a b : BitVec 64} (h : a ≠ b) :
    (a - b == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; apply h; revert heq; bv_kernel

theorem add_neg_eq_zero_false_of_ne {a b : BitVec 64} (h : a ≠ b) :
    (a + (~~~b + 1#64) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; apply h; revert heq; bv_kernel

theorem isOk_addEpoch_false_of_ovf (hkdf : HkdfFn) (self : Chain) (es : EpochSecret)
    (h : self.currentEpoch = 0xffffffffffffffff#64) :
    (Chain.addEpoch hkdf self es).isOk = false := by
  simp [Chain.addEpoch, h]; rfl

theorem isOk_addEpoch_false_of_epoch_ne (hkdf : HkdfFn) (self : Chain) (es : EpochSecret)
    (hovf : self.currentEpoch ≠ 0xffffffffffffffff#64)
    (hep : es.epoch ≠ self.currentEpoch + 1#64) :
    (Chain.addEpoch hkdf self es).isOk = false := by
  unfold Chain.addEpoch
  have h1 : (self.currentEpoch == 0xffffffffffffffff#64) = false := by simp [hovf]
  have h2 : (es.epoch != self.currentEpoch + 1#64) = true := by simp [hep]
  simp [h1, h2]; rfl

theorem ofNat_len_add_one {len : Nat} {cap : BitVec 64}
    (hlen : len < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    BitVec.ofNat 64 len + 1#64 = BitVec.ofNat 64 (len + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : len + 1 < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]

end AddEpochFrameHelpers

/-! ## Relocatable `[LibsignalPlacement]` Helpers for `<spqr::chain::Chain>::add_epoch` (Block `368`) -/

attribute [wp_unfold] NextKeyInternalFacts.withLsCallInv NextKeyInternalFacts.LsCallInv

namespace ChainAddEpochFacts

open NextKeyInternalFacts

theorem rodata_chainAddEpochInfo_placed [LibsignalPlacement] {m : Memory}
    (hF : LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.175") ↦ᵣ chainAddEpochInfo) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_addEpoch " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_addEpoch: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_addEpoch_of_trace_eq; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end ChainAddEpochFacts

end CryptoVerification.SpqrV1.ChainProofs
