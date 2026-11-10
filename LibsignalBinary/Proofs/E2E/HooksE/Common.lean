/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Proofs.E2E.HooksNames
public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
public import LibsignalBinary.Proofs.E2E.StoreNew.Defs
import ProofLib.SepLogic.WP.Structural
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
import LibsignalBinary.Proofs.E2E.Record.Support.Phi -- shake: keep

/-!
# E2E Hook Models, Contracts, and Bump-Allocator Helpers

Defines the token-free allocator model `A0`, empty-state SPQR model `spqrModelE`, hook contracts
(`rustAllocNWSpec`, `bcmpVregsSpec`, `e2eBcmpSpec`, `stringCloneSpec`, `timeAddSpec`,
`durationSinceSpec`, `HashbrownBinAbsHooks`), and bump-allocator memory lemmas for `absE C env`.
-/

@[expose] public section

namespace CryptoVerification.E2E.HooksE

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ witnessDeallocHook witnessDeallocHook_ok satisfies_mapFresh_unmapped
   readReg64_setPC_writeReg64_x0)
open CryptoVerification.E2E
open CryptoVerification.E2E.Record (spqrOffB)

/-! ## Concrete Allocator and SPQR Models -/

abbrev A0 : RustAlloc := A₀

/-- Empty-state `SpqrModel` (`spqrOffModel`) for `absE C env`: `recv` delegates to the in-image
`LibsignalSpqr.spqrRecvEmpty` (rejecting malformed preambles, DEV-LS24). -/
def spqrModelE : SpqrModel where
  send _ _ := some ([], none, [])
  draws _ _ := 0
  recv _ msg := LibsignalSpqr.spqrRecvEmpty msg
  recvPanics _ _ := false
  sendPanics _ _ := false

theorem spqrModelE_emptyOk : SpqrModel.SendEmptyOk spqrModelE where
  send _ := rfl
  draws _ := rfl
  noPanic _ h := Bool.false_ne_true h

theorem spqrModelE_modelRecvEmptyOk : SpqrModel.RecvEmptyOk spqrModelE where
  recv _ := rfl
  noPanic _ h := Bool.false_ne_true h

theorem spqrModelE_spqr_eq :
    spqrModelE.spqr =
      ⟨fun _ _ => [], fun _ _ => some ([], none, []),
        fun _ msg => LibsignalSpqr.spqrRecvEmpty msg, fun _ _ => false, fun _ _ => false⟩ := rfl

/-! ## Hook Contracts -/

/-! ### `__rustc::__rust_alloc` with No-Wrap (`rustAllocNWSpec`) -/

/-- `__rustc::__rust_alloc(size = x0, align = x1)` strengthening `rustAllocSpec A` with
`(sf.readReg64 .x0).toNat + size < 2 ^ 64` on non-null return. -/
def rustAllocNWSpec (A : RustAlloc) : Spec (Nat × Nat) where
  pre := (rustAllocSpec A).pre
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧
         (sf.readReg64 .x0).toNat + size < 2 ^ 64 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)
  onPanic := (rustAllocSpec A).onPanic

theorem hookOk_rustAllocSpec_of_NW {A : RustAlloc} {f : State → State}
    (h : HookOk f (rustAllocNWSpec A)) :
    HookOk f (rustAllocSpec A) := by
  intro (size, align) R s0 hrun hpre hsp
  obtain ⟨hkf, hsp_eq, Out⟩ := h (size, align) R s0 hrun hpre hsp
  refine ⟨hkf, hsp_eq, ?_⟩
  rcases Out with ⟨hret, hregs, hpost⟩ | hpan
  · refine Or.inl ⟨hret, hregs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [rustAllocNWSpec, rustAllocSpec]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    split
    · exact Entails.refl _
    · exact Entails.pure_left fun ⟨hal, _, htr⟩ => Entails.pure_right ⟨hal, htr⟩ (Entails.refl _)
  · exact Or.inr hpan

theorem hookSat_rustAllocSpec_of_NW {A : RustAlloc} {ext : String → Option (State → State)}
    {name : String} (h : HookSat ext name (rustAllocNWSpec A)) :
    HookSat ext name (rustAllocSpec A) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustAllocSpec_of_NW hok⟩

/-! ### `bcmp` (`e2eBcmpSpec` and `bcmpVregsSpec`) -/

/-- Ghost arguments for `bcmp(a = x0, b = x1, n = x2)` on equal-length byte slices. -/
structure BcmpCall where
  a : BitVec 64
  b : BitVec 64
  bsA : List (BitVec 8)
  bsB : List (BitVec 8)

/-- `bcmp(a = x0, b = x1, n = x2) -> w0` preserving `vregs`. -/
def bcmpVregsSpec : Spec BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧
      sf.vregs = s0.vregs ∧ sf.trace = s0.trace⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s0.sp extHookStack

/-- `bcmp(a = x0, b = x1, n = x2) -> w0` without `vregs` preservation. -/
def e2eBcmpSpec : Spec BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s0.sp extHookStack

theorem hookOk_bcmpSpec_of_vregs {h : State → State}
    (hok : HookOk h bcmpVregsSpec) : HookOk h e2eBcmpSpec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hst, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hst, ?_⟩
  rcases hout with ⟨hret, habi, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, htrap, hont⟩ | ⟨hoom, hono⟩
  · refine Or.inl ⟨hret, habi, ?_⟩
    dsimp only [bcmpVregsSpec, e2eBcmpSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hpost.1.2.2⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hpan, honp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, htrap, hont⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hono⟩))

/-! ### `hashmap_random_keys` (`randomKeysSpec` and `randomKeysTpidrSpec`) -/

export CryptoVerification.E2E.StoreNew (randomKeysSpec randomKeysTpidrSpec)

theorem hookOk_randomKeysSpec_of_tpidr {h : State → State}
    (hok : HookOk h randomKeysTpidrSpec) : HookOk h randomKeysSpec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hst, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hst, ?_⟩
  rcases hout with ⟨hret, habi, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, htrap, hont⟩ | ⟨hoom, hono⟩
  · refine Or.inl ⟨hret, habi, ?_⟩
    dsimp only [randomKeysTpidrSpec, randomKeysSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hpan, honp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, htrap, hont⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hono⟩))

/-! ### `<String as Clone>::clone` (`stringCloneSpec`) -/

/-- `<String as Clone>::clone(&self) -> String` (`x0 = &self`, sret `x8`): allocates a fresh
24-byte `String` with identical bytes while preserving `self`, or panics on allocation failure. -/
def stringCloneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ### `std::time::SystemTime` Hooks (`timeAddSpec` and `durationSinceSpec`) -/

/-- `<SystemTime as Add<Duration>>::add` for whole seconds (`x3.setWidth 32 = 0#32`): returns
`SystemTime.checkedAddSecs t secs` in `(x0, w1)`, or panics on overflow. -/
def timeAddSpec : Spec (SystemTime × Nat) where
  pre := fun (t, secs) s =>
    ⌜s.readReg64 .x0 = t.tvSec ∧ (s.readReg64 .x1).setWidth 32 = t.tvNsec ∧
      t.tvNsec.toNat < 10 ^ 9 ∧
      (s.readReg64 .x2).toNat = secs ∧ (s.readReg64 .x3).setWidth 32 = 0#32⌝ ∗
      stackAt s.sp extHookStack
  post := fun (t, secs) s0 sf =>
    let t' : SystemTime := ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩
    ⌜t.checkedAddSecs secs = some t' ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp extHookStack
  onPanic := fun (t, secs) s0 sf =>
    ⌜t.checkedAddSecs secs = none ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `SystemTime::duration_since(x0: &self, x1: earlier_sec, w2: earlier_nsec, x8: sret)`: writes
a 24-byte `Result<Duration, SystemTimeError>` at `x8`. -/
def durationSinceSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s.sp extHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s0.sp extHookStack

/-! ## Hashbrown Hook Bundle -/

/-- Abstract hook bundle for compiled `hashbrown` and `String::clone` proofs. -/
structure HashbrownBinAbsHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  tripleRatchet : TripleRatchetHooks C A S abs
  allocNW : HookSat abs rustAllocName (rustAllocNWSpec A)
  bcmp : HookSat abs bcmpName bcmpVregsSpec
  randomKeys : HookSat abs randomKeysName randomKeysSpec
  stringClone : HookSat abs stringCloneName (stringCloneSpec A)
  fallibilityAllocErr : abs allocErrName = some Rust.panicked

/-! ## Bump-Allocator and Memory Helpers -/

namespace HooksOkAux

theorem keepsFrozen_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.KeepsFrozen (m.write64 a v) :=
  Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 a v₀).canWrite (by decide) h) v

theorem satisfies_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ R :=
  IsBlock.write64 (IsBlock.pointsTo64 a v₀) h v

theorem allocFailedIn_allocPanicHook (s0 : State) :
    allocFailedIn s0 (allocPanicHook s0) := by
  simp [allocFailedIn, allocPanicHook, State.appendTrace, State.setStatus]

theorem trace_prefix_allocPanicHook (s0 : State) :
    s0.trace <+: (allocPanicHook s0).trace :=
  List.prefix_append s0.trace [allocFailedEvent]

theorem allocPanicHook_ok_of {α : Type} {spec : Spec α} {φ : α → State → State → Prop}
    (honPanic : ∀ x s0 sf, spec.onPanic x s0 sf = (⌜φ x s0 sf⌝ ∗ anyHeap))
    (hφ : ∀ x s0, allocFailedIn s0 (allocPanicHook s0) →
      s0.trace <+: (allocPanicHook s0).trace → φ x s0 (allocPanicHook s0)) :
    HookOk allocPanicHook spec := by
  intro x R s0 _ hpre _
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
  change s0.mem ⊨ spec.onPanic x s0 (allocPanicHook s0) ∗ R
  rw [honPanic, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ x s0 (allocFailedIn_allocPanicHook s0) (trace_prefix_allocPanicHook s0),
    Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hpre⟩

theorem allocPanicHook_ok {α : Type} {spec : Spec α}
    (honPanic : ∀ x s0 sf, spec.onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)) :
    HookOk allocPanicHook spec :=
  allocPanicHook_ok_of honPanic fun _ _ ha ht => ⟨ha, ht⟩

theorem heapBase_toNat : heapBase.toNat = 2 ^ 60 := by decide

theorem heapBase_add_toNat {k : Nat} (hk : k ≤ heapSize) :
    (heapBase + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k := by
  have hk' : k ≤ 2 ^ 60 := hk
  change (BitVec.ofNat 64 (2 ^ 60) + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k
  bv_omega

open Classical in
/-- `bumpAddr?` returns a non-null, aligned, unmapped block inside `[2^60, 2^61)`. -/
theorem bumpAddr?_spec {m : Memory} {size align : Nat} {p : BitVec 64}
    (h : bumpAddr? m size align = some p) :
    p ≠ 0 ∧ p.toNat % align = 0 ∧ heapBase.toNat ≤ p.toNat ∧
      p.toNat + size ≤ heapBase.toNat + heapSize ∧ Unmapped m p size := by
  unfold bumpAddr? at h
  split at h
  · rename_i hex
    simp only [Option.some.injEq] at h
    subst h
    have hfit : HeapBlockFitsAt m size align (Nat.find hex) := Nat.find_spec hex
    rcases hfit with ⟨_hal, hmod, hle, hunmap⟩
    have hk_le : Nat.find hex ≤ heapSize := by omega
    have hp_nat : (heapBase + BitVec.ofNat 64 (Nat.find hex)).toNat = 2 ^ 60 + Nat.find hex :=
      heapBase_add_toNat hk_le
    have hbase : heapBase.toNat = 2 ^ 60 := heapBase_toNat
    have hsize : heapSize = 2 ^ 60 := rfl
    have hne : heapBase + BitVec.ofNat 64 (Nat.find hex) ≠ 0 := by
      intro h0
      have h0' : (heapBase + BitVec.ofNat 64 (Nat.find hex)).toNat = 0 := by
        rw [h0]; rfl
      omega
    exact ⟨hne, hmod, by omega, by omega, hunmap⟩
  · contradiction

theorem memRegion_24_split (v : BitVec 64) :
    memRegion v 24 =
      (∃∗ w0 : BitVec 64, v ↦₆₄ w0) ∗
      ((∃∗ w1 : BitVec 64, (v + 8#64) ↦₆₄ w1) ∗
       (∃∗ w2 : BitVec 64, (v + 16#64) ↦₆₄ w2)) := by
  rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide),
    memRegion_eight v,
    memRegion_split' (b := v + 8#64) (n := 8) (k := 8) (b' := v + 16#64)
      rfl (by bv_omega) (by decide),
    memRegion_eight (v + 8#64),
    memRegion_eight (v + 16#64)]

theorem keepsFrozen_writeVecHeader_of_vecHeader {m : Memory} {v cap₀ ptr₀ len₀ : BitVec 64}
    {R : SepProp} (cap ptr len : BitVec 64) (h : m ⊨ vecHeader v cap₀ ptr₀ len₀ ∗ R) :
    m.KeepsFrozen (writeVecHeader m v cap ptr len) := by
  unfold vecHeader at h
  have h0 : m ⊨ (v ↦₆₄ cap₀) ∗ (((v + 8#64) ↦₆₄ ptr₀) ∗ (((v + 16#64) ↦₆₄ len₀) ∗ R)) := by
    ac_nf at h ⊢
  have hkf1 := keepsFrozen_write64_of_pointsTo64 cap h0
  have hw1 := satisfies_write64_of_pointsTo64 cap h0
  have h1 : m.write64 v cap ⊨
      ((v + 8#64) ↦₆₄ ptr₀) ∗ (((v + 16#64) ↦₆₄ len₀) ∗ ((v ↦₆₄ cap) ∗ R)) := by
    ac_nf at hw1 ⊢
  have hkf2 := hkf1.trans (keepsFrozen_write64_of_pointsTo64 ptr h1)
  have hw2 := satisfies_write64_of_pointsTo64 ptr h1
  have h2 : (m.write64 v cap).write64 (v + 8#64) ptr ⊨
      ((v + 16#64) ↦₆₄ len₀) ∗ ((v ↦₆₄ cap) ∗ (((v + 8#64) ↦₆₄ ptr) ∗ R)) := by
    ac_nf at hw2 ⊢
  exact hkf2.trans (keepsFrozen_write64_of_pointsTo64 len h2)

theorem satisfies_writeVecHeader_of_vecHeader {m : Memory} {v cap₀ ptr₀ len₀ : BitVec 64}
    {R : SepProp} (cap ptr len : BitVec 64) (h : m ⊨ vecHeader v cap₀ ptr₀ len₀ ∗ R) :
    writeVecHeader m v cap ptr len ⊨ vecHeader v cap ptr len ∗ R := by
  unfold vecHeader at h ⊢
  unfold writeVecHeader
  have h0 : m ⊨ (v ↦₆₄ cap₀) ∗ (((v + 8#64) ↦₆₄ ptr₀) ∗ (((v + 16#64) ↦₆₄ len₀) ∗ R)) := by
    ac_nf at h ⊢
  have hw1 := satisfies_write64_of_pointsTo64 cap h0
  have h1 : m.write64 v cap ⊨
      ((v + 8#64) ↦₆₄ ptr₀) ∗ (((v + 16#64) ↦₆₄ len₀) ∗ ((v ↦₆₄ cap) ∗ R)) := by
    ac_nf at hw1 ⊢
  have hw2 := satisfies_write64_of_pointsTo64 ptr h1
  have h2 : (m.write64 v cap).write64 (v + 8#64) ptr ⊨
      ((v + 16#64) ↦₆₄ len₀) ∗ ((v ↦₆₄ cap) ∗ (((v + 8#64) ↦₆₄ ptr) ∗ R)) := by
    ac_nf at hw2 ⊢
  have hw3 := satisfies_write64_of_pointsTo64 len h2
  ac_nf at hw3 ⊢

theorem keepsFrozen_writeVecHeader_of_memRegion {m : Memory} {v : BitVec 64} {R : SepProp}
    (cap ptr len : BitVec 64) (h : m ⊨ memRegion v 24 ∗ R) :
    m.KeepsFrozen (writeVecHeader m v cap ptr len) := by
  rw [memRegion_24_split v] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at h
  rcases h with ⟨w2, w1, w0, h⟩
  have h' : m ⊨ vecHeader v w0 w1 w2 ∗ R := by
    unfold vecHeader; ac_nf at h ⊢
  exact keepsFrozen_writeVecHeader_of_vecHeader cap ptr len h'

theorem satisfies_writeVecHeader_of_memRegion {m : Memory} {v : BitVec 64} {R : SepProp}
    (cap ptr len : BitVec 64) (h : m ⊨ memRegion v 24 ∗ R) :
    writeVecHeader m v cap ptr len ⊨ vecHeader v cap ptr len ∗ R := by
  rw [memRegion_24_split v] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at h
  rcases h with ⟨w2, w1, w0, h⟩
  have h' : m ⊨ vecHeader v w0 w1 w2 ∗ R := by
    unfold vecHeader; ac_nf at h ⊢
  exact satisfies_writeVecHeader_of_vecHeader cap ptr len h'

theorem satisfies_vecU8_exact {m : Memory} {v p : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (hp : p ≠ 0) (hbs : bs.length < 2 ^ 63)
    (h : m ⊨ vecHeader v (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 bs.length) ∗
      ((p ↦ₛ bs) ∗ R)) :
    m ⊨ vecU8 A0 v bs ∗ R := by
  let n := BitVec.ofNat 64 bs.length
  have hn : n.toNat = bs.length := by
    dsimp [n]
    exact Nat.mod_eq_of_lt (by omega)
  have hbuf :
      (if n = 0 then emp
       else A0.live p n.toNat 1 ∗ (p ↦ₛ bs) ∗ memRegion (p + n) (n.toNat - bs.length)) =
      (p ↦ₛ bs) := by
    split
    · rename_i h0
      have hlen0 : bs.length = 0 := by
        rw [← hn, h0]; rfl
      rw [List.eq_nil_of_length_eq_zero hlen0]
      exact (pointsToBytes_nil p).symm
    · dsimp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀]
      rw [hn, Nat.sub_self, memRegion_zero, emp_sepConj, sepConj_emp]
  unfold vecU8
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨n, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨p, ?_⟩
  unfold vecU8At
  change m ⊨ (vecHeader v n p n ∗ ⌜bs.length ≤ n.toNat ∧ n.toNat < 2 ^ 63 ∧ p ≠ 0⌝ ∗
    (if n = 0 then emp else A0.live p n.toNat 1 ∗ (p ↦ₛ bs) ∗ memRegion (p + n) (n.toNat - bs.length))) ∗ R
  rw [hbuf]
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
  exact ⟨⟨by omega, by omega, hp⟩, h⟩

theorem satisfies_vecU8_empty {m : Memory} {v ptr : BitVec 64} {R : SepProp}
    (hptr : ptr ≠ 0) (h : m ⊨ vecHeader v 0#64 ptr 0#64 ∗ R) :
    m ⊨ vecU8 A0 v [] ∗ R := by
  have h' : m ⊨ vecHeader v (BitVec.ofNat 64 ([] : List (BitVec 8)).length) ptr
      (BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗ ((ptr ↦ₛ []) ∗ R) := by
    rw [pointsToBytes_nil, emp_sepConj]
    exact h
  exact satisfies_vecU8_exact hptr (by decide) h'

theorem vecOutThen_some {bs : List (BitVec 8)} {ret p : BitVec 64} {Frame : SepProp} {s0 : State}
    (hbs : bs.length < 2 ^ 63) (hp : bumpAddr? s0.mem bs.length 1 = some p)
    (hmem : s0.mem ⊨ memRegion ret 24 ∗ Frame) :
    let m1 := s0.mem.mapFresh p bs.length Perm.rw
    let n := BitVec.ofNat 64 bs.length
    let mf := writeVecHeader (m1.writeBytes p bs) ret n p n
    s0.mem.KeepsFrozen mf ∧ (mf ⊨ vecU8 A0 ret bs ∗ Frame) := by
  rcases bumpAddr?_spec hp with ⟨hp_ne, _, _, _, hp_unmap⟩
  let m1 := s0.mem.mapFresh p bs.length Perm.rw
  have hkf1 : s0.mem.KeepsFrozen m1 := Memory.keepsFrozen_mapFresh s0.mem p bs.length Perm.rw
  have hm1 : m1 ⊨ memRegion p bs.length ∗ (memRegion ret 24 ∗ Frame) :=
    satisfies_mapFresh_unmapped hmem hp_unmap
  have hkf2 : m1.KeepsFrozen (m1.writeBytes p bs) :=
    keepsFrozen_writeBytes_of_memRegion bs (by omega) hm1
  have hm2 : m1.writeBytes p bs ⊨ (p ↦ₛ bs) ∗ (memRegion ret 24 ∗ Frame) :=
    satisfies_writeBytes bs (by omega) hm1
  have hm2' : m1.writeBytes p bs ⊨ memRegion ret 24 ∗ ((p ↦ₛ bs) ∗ Frame) := by
    ac_nf at hm2 ⊢
  let n := BitVec.ofNat 64 bs.length
  have hkf3 := keepsFrozen_writeVecHeader_of_memRegion n p n hm2'
  have hm3 := satisfies_writeVecHeader_of_memRegion n p n hm2'
  exact ⟨hkf1.trans (hkf2.trans hkf3), satisfies_vecU8_exact hp_ne hbs hm3⟩

end HooksOkAux

end CryptoVerification.E2E.HooksE
