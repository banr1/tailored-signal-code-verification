/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandHelpersExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSegsExt
import ProofLib.SepLogic.HeapIntro

/-!
# `.inImage`-Free HKDF Hook Bundle and `RunsToE` Bridges

Packages `.inImage`-free `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the four
external hooks used by HKDF (`sha2::sha256::compress256`, `memcpy` RW/RO, and `memset` at
`extHookStack = 16384` B) and derives `RunsToE` bridges without `img.FrozenLoaded` or `symtab`.
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
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

/-! ## `HkdfStubsExt` Bundle and Constructors -/

/-- `.inImage`-free `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the four
external hooks called by HKDF (`compress256`, `memcpy` RW/RO, `memset`) at `extHookStack`. -/
structure HkdfStubsExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop where
  compress256 :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "sha2::sha256::compress256"))
      (HkdfExt.compress256ExternShaSpec F extHookStack)
  memcpy :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "memcpy"))
      (sessionMemcpySpec extHookStack)
  memcpyRO :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "memcpy"))
      (memcpyROExtSpec extHookStack)
  memset :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "memset"))
      (HkdfExt.session2MemsetExternSpec extHookStack)

namespace HkdfStubsExt

private theorem hookOk_map_pure {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0, (f s0).mem ⊨ s₁.post (g y) s0 (f s0) ∗ R →
      (f s0).mem ⊨ s₂.post y s0 (f s0) ∗ R)
    (hpan : ∀ x s0 sf, s₁.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, s₁.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, s₁.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp'⟩ | ⟨code, _, he'⟩ | ⟨_, ho'⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 hq⟩
  · rw [hpan (g y) s0 (f s0), satisfies_pure_sepConj] at hp'; exact False.elim hp'.1
  · rw [hex (g y) code s0 (f s0), satisfies_pure_sepConj] at he'; exact False.elim he'.1
  · rw [hoom (g y) s0 (f s0), satisfies_pure_sepConj] at ho'; exact False.elim ho'.1

private theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (SignalSession.CliExt.withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (SignalSession.CliExt.withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (SignalSession.CliExt.withStack base s1).pre x s0 ∗ R' := by
    dsimp only [SignalSession.CliExt.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SignalSession.CliExt.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [SignalSession.CliExt.withStack] at hp
    rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [SignalSession.CliExt.withStack] at he
    rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [SignalSession.CliExt.withStack] at ho
    rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem stub_of_hookSat {α : Type} (b : BitVec 64)
    {ext : String → Option (State → State)} {hname : String} {off : Nat} {spec : Spec α}
    (hlt : off < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? off = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + BitVec.ofNat 64 off) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact hook_ok_stub (code := libsignalSessionCode) hlt hhook
    ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

private theorem readReg32_truncate8_eq (s : State) (r : Reg) :
    (s.readReg32 r).truncate 8 = (s.readReg64 r).truncate 8 := by
  change ((s.readReg64 r).setWidth 32).setWidth 8 = (s.readReg64 r).setWidth 8
  exact BitVec.setWidth_setWidth_of_le (s.readReg64 r) (by decide : 8 ≤ 32)

private theorem isPanic_compress256 :
    Rust.isPanicSymbol "sha2::sha256::compress256" = false := by
  simp [Rust.isPanicSymbol]

private theorem isPanic_memcpy : Rust.isPanicSymbol "memcpy" = false := by
  simp [Rust.isPanicSymbol]

private theorem isPanic_memset : Rust.isPanicSymbol "memset" = false := by
  simp [Rust.isPanicSymbol]

theorem of_hookSat (b : BitVec 64) (C : Crypto) (ext : String → Option (State → State))
    (hComp : HookSat ext "sha2::sha256::compress256" (SignalSession.CliExt.compress256Spec C))
    (hMemcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec)
    (hMemcpyRO : HookSat ext "memcpy" SignalSession.CliExt.memcpyROSpec)
    (hMemset : HookSat ext "memset" SignalSession.CliExt.memsetSpec) :
    HkdfStubsExt b C.F ext where
  compress256 := by
    have hsat : HookSat ext "sha2::sha256::compress256"
        (HkdfExt.compress256ExternShaSpec C.F extHookStack) := by
      refine hookSat_map hComp fun f hf => ?_
      refine hookOk_map_pure (fun (stA, blkA, st, bs) => (stA, st, blkA, bs, (bs.length / 64))) hf
        (fun ⟨stA, blkA, st, bs⟩ R s0 hp => ?_)
        (fun ⟨stA, blkA, st, bs⟩ R s0 hq => ?_)
      · dsimp only [HkdfExt.compress256ExternShaSpec, SignalSession.CliExt.compress256Spec,
          SignalSession.CliExt.withStack] at hp ⊢
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
        rcases hp with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
        have hn : (s0.readReg64 .x2).toNat = bs.length / 64 := by omega
        have hlen : bs.length = 64 * (bs.length / 64) := by omega
        refine ⟨⟨hx0, hx1, hn, hlen⟩, ?_⟩
        ac_nf at hmem ⊢
      · dsimp only [HkdfExt.compress256ExternShaSpec, SignalSession.CliExt.compress256Spec,
          SignalSession.CliExt.withStack] at hq ⊢
        ac_nf at hq ⊢
    exact stub_of_hookSat b (by decide)
      (ls_hook% "sha2::sha256::compress256") isPanic_compress256 hsat
  memcpy := by
    let base : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
      { pre := fun (dst, src, bs) s0 =>
          ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
            memRegion dst bs.length ∗ (src ↦ₛ bs)
        post := fun (dst, src, bs) s0 sf =>
          ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) }
    have hsat : HookSat ext "memcpy" (sessionMemcpySpec extHookStack) := by
      refine hookSat_map hMemcpy fun f hf => ?_
      have h1 : HookOk f (SignalSession.CliExt.withStack base SignalSession.CliExt.memHookStack) :=
        hookOk_map_pure (fun x => x) hf
          (fun ⟨dst, src, bs⟩ R s0 hp => by
            dsimp only [SignalSession.CliExt.memcpySpec, libcMemcpySpec,
              SignalSession.CliExt.withStack, base] at hp ⊢
            ac_nf at hp ⊢)
          (fun ⟨dst, src, bs⟩ R s0 hq => by
            dsimp only [SignalSession.CliExt.memcpySpec,
              SignalSession.CliExt.withStack, base] at hq ⊢
            ac_nf at hq ⊢)
      have h2 := hookOk_stack_mono h1 (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack)
        (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨dst, src, bs⟩ R s0 hp => by
          dsimp only [sessionMemcpySpec, libcMemcpySpec,
            SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨dst, src, bs⟩ R s0 hq => by
          dsimp only [sessionMemcpySpec,
            SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_of_hookSat b (by decide)
      (ls_hook% "memcpy") isPanic_memcpy hsat
  memcpyRO := by
    let base : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
      { pre := fun (dst, src, bs) s0 =>
          ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
            bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
        post := fun (dst, src, bs) s0 sf =>
          ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    have hsat : HookSat ext "memcpy" (memcpyROExtSpec extHookStack) := by
      refine hookSat_map hMemcpyRO fun f hf => ?_
      have h2 := hookOk_stack_mono (base := base) hf
        (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack) (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨dst, src, bs⟩ R s0 hp => by
          dsimp only [memcpyROExtSpec, SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨dst, src, bs⟩ R s0 hq => by
          dsimp only [memcpyROExtSpec, SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_of_hookSat b (by decide)
      (ls_hook% "memcpy") isPanic_memcpy hsat
  memset := by
    let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
      { pre := fun (ptr, c, len) s0 =>
          ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg64 .x1).truncate 8 = c ∧
            (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
        post := fun (ptr, c, len) s0 sf =>
          ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
    have hsat : HookSat ext "memset" (HkdfExt.session2MemsetExternSpec extHookStack) := by
      refine hookSat_map hMemset fun f hf => ?_
      have h1 : HookOk f (SignalSession.CliExt.withStack base SignalSession.CliExt.memHookStack) :=
        hookOk_map_pure (fun x => x) hf
          (fun ⟨ptr, c, len⟩ R s0 hp => by
            dsimp only [SignalSession.CliExt.memsetSpec, libcMemsetSpec,
              SignalSession.CliExt.withStack, base] at hp ⊢
            simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
            rcases hp with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
            refine ⟨⟨hx0, (readReg32_truncate8_eq s0 .x1).trans hx1, hx2⟩, ?_⟩
            ac_nf at hmem ⊢)
          (fun ⟨ptr, c, len⟩ R s0 hq => by
            dsimp only [SignalSession.CliExt.memsetSpec,
              SignalSession.CliExt.withStack, base] at hq ⊢
            ac_nf at hq ⊢)
      have h2 := hookOk_stack_mono h1 (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack)
        (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨ptr, c, len⟩ R s0 hp => by
          dsimp only [HkdfExt.session2MemsetExternSpec, SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨ptr, c, len⟩ R s0 hq => by
          dsimp only [HkdfExt.session2MemsetExternSpec, SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_of_hookSat b (by decide)
      (ls_hook% "memset") isPanic_memset hsat

private theorem hookSat_cliExternsWith_of_not_panic {α : Type}
    {ext : String → Option (State → State)} {n : String} {spec : Spec α}
    (hn : E2E.isImagePanicSymbol n = false) (h : HookSat ext n spec) :
    HookSat (SignalSession.cliExternsWith ext) n spec := by
  obtain ⟨f, hf, hok⟩ := h
  have heq : SignalSession.cliExternsWith ext n = ext n := by
    simp [SignalSession.cliExternsWith, E2E.withImagePanics, hn]
  exact ⟨f, heq.trans hf, hok⟩

private theorem isPanicE_compress256 :
    E2E.isImagePanicSymbol "sha2::sha256::compress256" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_compress256, E2E.extraImagePanicNames]

private theorem isPanicE_memcpy :
    E2E.isImagePanicSymbol "memcpy" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memcpy, E2E.extraImagePanicNames]

private theorem isPanicE_memset :
    E2E.isImagePanicSymbol "memset" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memset, E2E.extraImagePanicNames]

theorem of_externsOk_raw (b : BitVec 64) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : SignalSession.CliExternsOk P A ext) :
    HkdfStubsExt b P.C.F ext :=
  of_hookSat b P.C ext hOk.compress256 hOk.memcpy hOk.memcpyRO hOk.memset

theorem of_externsOk (b : BitVec 64) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : SignalSession.CliExternsOk P A ext) :
    HkdfStubsExt b P.C.F (SignalSession.cliExternsWith ext) :=
  of_hookSat b P.C (SignalSession.cliExternsWith ext)
    (hookSat_cliExternsWith_of_not_panic isPanicE_compress256 hOk.compress256)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memcpy hOk.memcpy)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memcpy hOk.memcpyRO)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memset hOk.memset)

end HkdfStubsExt

/-! ## `subroutine_ok`-to-`RunsToE` Bridges -/

section StubBridges

theorem compress256_stub_runsTo {prog : Program} {b : BitVec 64}
    {F : ShaCompress} {hookStack : Nat}
    (hComp : subroutine_ok prog (b + bv% (ls_off% "sha2::sha256::compress256"))
      (HkdfExt.compress256ExternShaSpec F hookStack))
    (hstk_le : hookStack ≤ 2 ^ 64 := by decide)
    {s : State} {stPtr blkPtr : BitVec 64} {st : ShaState} {bs : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : 64 * (s.readReg64 .x2).toNat = bs.length)
    (hbs_le : bs.length ≤ 2 ^ 64)
    (hst_mem : s.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes st)
    (hbs_mem : s.mem.readBytes blkPtr bs.length = bs)
    (hrw_st : RW s.mem stPtr 32)
    (hrw_blk : RW s.mem blkPtr bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_st_blk : DisjointRegions stPtr 32 blkPtr bs.length)
    (hd_st_stk : DisjointRegions stPtr 32 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_blk_stk : DisjointRegions blkPtr bs.length (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes stPtr 32 =
        LibsignalHmac.shaStateBytes ((HMAC.chunks64 bs).foldl F st) ∧
      s'.mem.readBytes blkPtr bs.length = bs ∧
      Extract.S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 64 × ShaState × List (BitVec 8) := (stPtr, blkPtr, st, bs)
  let P1 : SepProp := stPtr ↦ₛ LibsignalHmac.shaStateBytes st
  let P2 : SepProp := blkPtr ↦ₛ bs
  let P3 : SepProp := stackAt s.sp hookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hst_len : (LibsignalHmac.shaStateBytes st).length = 32 := HkdfExt.shaStateBytes_length st
  have hb1 : IsBlock P1 stPtr 32
      (fun m => (LibsignalHmac.shaStateBytes st).length ≤ 2 ^ 64 ∧
        m.readBytes stPtr (LibsignalHmac.shaStateBytes st).length = LibsignalHmac.shaStateBytes st) :=
    IsBlock.pointsToBytes_len hst_len
  have hb2 : IsBlock P2 blkPtr bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes blkPtr bs.length = bs) :=
    IsBlock.pointsToBytes blkPtr bs
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 hookStack) hookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 hookStack) hookStack
  have hsatP : s.mem ⊨ P :=
    HkdfExt.satisfies_three_blocks hb1 hb2 hb3
      ⟨by rw [hst_len]; decide, by rwa [hst_len]⟩ ⟨hbs_le, hbs_mem⟩ trivial
      hrw_st hrw_blk hrw_stk hd_st_blk hd_st_stk hd_blk_stk hbs_le hstk_le
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ (HkdfExt.compress256ExternShaSpec F hookStack).pre xg s ∗ R := by
    rw [HkdfExt.compress256ExternShaSpec]
    dsimp only [xg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hComp xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [HkdfExt.compress256ExternShaSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [HkdfExt.compress256ExternShaSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [HkdfExt.compress256ExternShaSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  rw [HkdfExt.compress256ExternShaSpec] at hpost_sat
  dsimp only [xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let st' := (HMAC.chunks64 bs).foldl F st
  let P1' : SepProp := stPtr ↦ₛ LibsignalHmac.shaStateBytes st'
  have hst'_len : (LibsignalHmac.shaStateBytes st').length = 32 := HkdfExt.shaStateBytes_length st'
  have hb1' : IsBlock P1' stPtr 32
      (fun m => (LibsignalHmac.shaStateBytes st').length ≤ 2 ^ 64 ∧
        m.readBytes stPtr (LibsignalHmac.shaStateBytes st').length = LibsignalHmac.shaStateBytes st') :=
    IsBlock.pointsToBytes_len hst'_len
  change s'.mem ⊨ (P2 ∗ P1' ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hst_s' : s'.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes st' := by
    have h := (hb1'.read hpost_1).2; rwa [hst'_len] at h
  have hbs_s' : s'.mem.readBytes blkPtr bs.length = bs := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : Extract.S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)] :=
    Extract.isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 hbs_le (hbs_s'.trans hbs_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hst_s', hbs_s', hframe⟩,
    hsteps.codeLoaded hL⟩

theorem compress256_one_stub_runsTo {prog : Program} {b : BitVec 64}
    {F : ShaCompress} {hookStack : Nat}
    (hComp : subroutine_ok prog (b + bv% (ls_off% "sha2::sha256::compress256"))
      (HkdfExt.compress256ExternShaSpec F hookStack))
    (hstk_le : hookStack ≤ 2 ^ 64 := by decide)
    {s : State} {stPtr blkPtr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hst_mem : s.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes st)
    (hblk_mem : s.mem.readBytes blkPtr 64 = blk)
    (hrw_st : RW s.mem stPtr 32)
    (hrw_blk : RW s.mem blkPtr 64)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hd_st_stk : DisjointRegions stPtr 32 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_blk_stk : DisjointRegions blkPtr 64 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes (F st blk) ∧
      s'.mem.readBytes blkPtr 64 = blk ∧
      Extract.S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)]) := by
  have hblk_len : blk.length = 64 := by rw [← hblk_mem, Memory.readBytes_length]
  have hx2_len : 64 * (s.readReg64 .x2).toNat = blk.length := by rw [hx2, hblk_len]; rfl
  have hrun := compress256_stub_runsTo hComp hstk_le hpc hstat hx0 hx1 hx2_len
    (by rw [hblk_len]; decide) hst_mem (by rwa [hblk_len]) hrw_st (by rwa [hblk_len]) hrw_stk
    (by rwa [hblk_len]) hd_st_stk (by rwa [hblk_len]) hsp_al
  refine hrun.mono fun s' hs' => ?_
  rw [chunks64_single hblk_len, List.foldl_cons, List.foldl_nil, hblk_len] at hs'
  exact hs'

theorem memcpy_opt_stub_runsTo {prog : Program} {b : BitVec 64}
    (hMemcpy : subroutine_ok prog (b + bv% (ls_off% "memcpy"))
      (sessionMemcpySpec extHookStack))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hrw_src : RW s.mem src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_src : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length)
    (hd_dst_stk : bs.length = 0 ∨
      DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_src_stk : bs.length = 0 ∨
      DisjointRegions src bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      Extract.S2Frame s.mem s'.mem [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  have hbs_le : bs.length ≤ 2 ^ 64 := by
    rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  let xg : BitVec 64 × BitVec 64 × List (BitVec 8) := (dst, src, bs)
  let P1 : SepProp := memRegion dst bs.length
  let P2 : SepProp := src ↦ₛ bs
  let P3 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 dst bs.length (fun _ => True) := IsBlock.memRegion dst bs.length
  have hb2 : IsBlock P2 src bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes src bs.length = bs) :=
    IsBlock.pointsToBytes src bs
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    HkdfExt.satisfies_three_blocks_opt hb1 hb2 hb3 trivial ⟨hbs_le, hbs_mem⟩ trivial
      hrw_dst hrw_src hrw_stk
      (hd_dst_src.imp id Or.inr) (hd_dst_stk.imp id Or.inr) (hd_src_stk.imp id Or.inr)
      hbs_le (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ (sessionMemcpySpec extHookStack).pre xg s ∗ R := by
    dsimp only [sessionMemcpySpec, libcMemcpySpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hMemcpy xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [sessionMemcpySpec, libcMemcpySpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [sessionMemcpySpec, libcMemcpySpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [sessionMemcpySpec, libcMemcpySpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [sessionMemcpySpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_sep⟩
  let P1' : SepProp := dst ↦ₛ bs
  have hb1' : IsBlock P1' dst bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes dst bs.length = bs) :=
    IsBlock.pointsToBytes dst bs
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1', P2, P3]; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst bs.length = bs := (hb1'.read hpost_1).2
  have hsrc_s' : s'.mem.readBytes src bs.length = bs := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : Extract.S2Frame s.mem s'.mem
      [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    Extract.isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 hbs_le (hsrc_s'.trans hbs_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hsrc_s', hframe⟩,
    hsteps.codeLoaded hL⟩

theorem memcpy_stub_runsTo {prog : Program} {b : BitVec 64}
    (hMemcpy : subroutine_ok prog (b + bv% (ls_off% "memcpy"))
      (sessionMemcpySpec extHookStack))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hrw_src : RW s.mem src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_src : DisjointRegions dst bs.length src bs.length)
    (hd_dst_stk : DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_src_stk : DisjointRegions src bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      Extract.S2Frame s.mem s'.mem [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :=
  memcpy_opt_stub_runsTo hMemcpy hpc hstat hx0 hx1 hx2 hbs_mem
    hrw_dst hrw_src hrw_stk (Or.inr hd_dst_src) (Or.inr hd_dst_stk) (Or.inr hd_src_stk) hsp_al

theorem memcpy_zero_stub_runsTo {prog : Program} {b : BitVec 64}
    (hMemcpy : subroutine_ok prog (b + bv% (ls_off% "memcpy"))
      (sessionMemcpySpec extHookStack))
    {s : State} {dst src : BitVec 64}
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = 0)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      Extract.S2Frame s.mem s'.mem [(dst, 0), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  have hrun := memcpy_opt_stub_runsTo hMemcpy (bs := []) hpc hstat hx0 hx1 hx2
    rfl (by intro a ha; simp [InRegion] at ha) (by intro a ha; simp [InRegion] at ha) hrw_stk
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hsp_al
  exact hrun.mono fun s' ⟨hpc', hstat', hcc, hx0', _, _, hfr⟩ => ⟨hpc', hstat', hcc, hx0', hfr⟩

theorem memcpyRO_stub_runsTo {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hRO : subroutine_ok (tripleRatchetProgAtExt b ext) (b + bv% (ls_off% "memcpy"))
      (memcpyROExtSpec extHookStack))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen_le : bs.length ≤ 64)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hread_src : s.mem.Readable src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hout_src_dst : ∀ a, InRegion src bs.length a → OutsideRegion dst bs.length a)
    (hout_src_stk : ∀ a, InRegion src bs.length a →
      OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      S2FrameRO src bs.length s.mem s'.mem
        [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 64 × List (BitVec 8) := (dst, src, bs)
  let P1 : SepProp := memRegion dst bs.length
  let P2 : SepProp := (src ↦ᵣ bs)
  let P3 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 dst bs.length (fun _ => True) := IsBlock.memRegion dst bs.length
  have hb2 : IsBlockRO P2 src bs.length (fun m => m.readBytes src bs.length = bs) :=
    IsBlockRO.pointsToBytesRO src bs (by omega)
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    satisfies_two_rw_one_ro hb1 hb2 hb3 trivial hbs_mem trivial
      hrw_dst hread_src hrw_stk hd_dst_stk (by decide) hout_src_dst hout_src_stk
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ (memcpyROExtSpec extHookStack).pre xg s ∗ R := by
    dsimp only [memcpyROExtSpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by omega⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hRO xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [memcpyROExtSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [memcpyROExtSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [memcpyROExtSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [memcpyROExtSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_mem⟩
  let P1' : SepProp := (dst ↦ₛ bs)
  have hb1' : IsBlock P1' dst bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes dst bs.length = bs) :=
    IsBlock.pointsToBytes dst bs
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1', P2, P3]; ac_nf at hpost_mem ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst bs.length = bs := (hb1'.read hpost_1).2
  have hsrc_s' : s'.mem.readBytes src bs.length = bs := hb2.read hpost_2
  have hmc_full : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  have hframe : S2FrameRO src bs.length s.mem s'.mem
      [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    isBlock_two_rw_one_ro_s2frameRO hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 (by omega) (hsrc_s'.trans hbs_mem.symm) hmc_full
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hsrc_s', hframe⟩,
    hsteps.codeLoaded hL⟩

theorem memset_stub_runsTo {prog : Program} {b : BitVec 64}
    (hMemset : subroutine_ok prog (b + bv% (ls_off% "memset"))
      (HkdfExt.session2MemsetExternSpec extHookStack))
    {s : State} {dst : BitVec 64} {val : BitVec 8} {n : ℕ}
    (hpc : s.pc = b + bv% (ls_off% "memset"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hrw_dst : RW s.mem dst n)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : DisjointRegions dst n (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst n = List.replicate n val ∧
      Extract.S2Frame s.mem s'.mem [(dst, n), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 8 × Nat := (dst, val, n)
  let P1 : SepProp := memRegion dst n
  let P2 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2
  have hb1 : IsBlock P1 dst n (fun _ => True) := IsBlock.memRegion dst n
  have hb2 : IsBlock P2 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    HkdfExt.satisfies_two_blocks hb1 hb2 trivial trivial hrw_dst hrw_stk hd_dst_stk (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ (HkdfExt.session2MemsetExternSpec extHookStack).pre xg s ∗ R := by
    dsimp only [HkdfExt.session2MemsetExternSpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hMemset xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [HkdfExt.session2MemsetExternSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [HkdfExt.session2MemsetExternSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [HkdfExt.session2MemsetExternSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [HkdfExt.session2MemsetExternSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_sep⟩
  let P1' : SepProp := dst ↦ₛ List.replicate n val
  have hrep_len : (List.replicate n val).length = n := List.length_replicate
  have hb1' : IsBlock P1' dst n
      (fun m => (List.replicate n val).length ≤ 2 ^ 64 ∧
        m.readBytes dst (List.replicate n val).length = List.replicate n val) :=
    IsBlock.pointsToBytes_len hrep_len
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ R) := by dsimp only [P1', P2]; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ R) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ P2) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst n = List.replicate n val := by
    have h := (hb1'.read hpost_1).2; rwa [hrep_len] at h
  have hmc_full : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  have hmc := hmc_full
  unfold Heap.Matches at hmc
  have hframe : Extract.S2Frame s.mem s'.mem
      [(dst, n), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    HkdfExt.isBlock_two_s2frame hb1 hb1' hb2 hpP hmP hpost_1 hpost_2 hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hframe⟩,
    hsteps.codeLoaded hL⟩

end StubBridges

end CryptoVerification.E2E.Pqxdh.ResponderCore
