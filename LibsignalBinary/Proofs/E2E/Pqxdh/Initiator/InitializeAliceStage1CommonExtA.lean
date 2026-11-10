/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs -- shake: keep

/-!
# Contract-Backed Hook and Key-Agreement Bridges (`tripleRatchetProgAtExt`)

Bridges `CliExternsOk` / `HookSat` contracts at `pqxdhHookStackExt` (`16384` B) to the by-value
`kyber::encapsulate` ABI (`kyberEncapsByValSpec`), allocator/memcpy helpers, and the
`FrozenLoaded`-only `<PrivateKey>::calculate_agreement` contract
(`calculateAgreement_frozen_ok_ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFill_ok_at_tripleRatchet
  rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem fitBv8_kyberEncapsOutBytes_eq_extA_of_len {P : Primitives}
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (pk r : Bytes) (hpk : pk.length = 1568) :
    let o := encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
    fitBv8 1600 (kyberEncapsOutBytes P pk r) = o.1.toList ++ o.2.toList := by
  intro o; unfold kyberEncapsOutBytes; rw [hEncapsEq pk r hpk]; dsimp only; unfold fitBv8
  rw [bytesToBv8_append, e2e_bytesToBv8_vecU8, e2e_bytesToBv8_vecU8]
  have hlen : (o.1.toList ++ o.2.toList).length = 1600 := by
    rw [List.length_append, o.1.toList_length, o.2.toList_length]
  rw [hlen, List.take_of_length_le (by rw [hlen]), Nat.sub_self, List.replicate_zero,
    List.append_nil]

@[simp, arm64_norm] abbrev initAliceCalcSubStackExt : Nat := 64 + pqxdhHookStackExt
@[simp, arm64_norm] abbrev initAliceCalcStackExt : Nat := 160 + initAliceCalcSubStackExt

theorem initAlice_stackAt_split (sp : BitVec 64) (extra inner : Nat)
    (hbound : extra + inner ≤ 2 ^ 64) :
    stackAt sp (extra + inner) =
      memRegion (sp - BitVec.ofNat 64 (extra + inner)) extra ∗ stackAt sp inner := by
  have hb' : sp - BitVec.ofNat 64 inner =
      sp - BitVec.ofNat 64 (extra + inner) + BitVec.ofNat 64 extra := by
    rw [Nat.add_comm extra inner, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (extra + inner))
    (n := extra) (k := inner) (b' := sp - BitVec.ofNat 64 inner) rfl hb' hbound

theorem initAlice_hookOk_map {α β : Type} {fn : State → State}
    {specA : Spec α} {specB : Spec β} (f : β → α)
    (hok : HookOk fn specA)
    (hpre : ∀ b R s0, (s0.mem ⊨ specB.pre b s0 ∗ R) → (s0.mem ⊨ specA.pre (f b) s0 ∗ R))
    (hpost : ∀ b R s0 sf, (s0.mem ⊨ specB.pre b s0 ∗ R) →
      (sf.mem ⊨ specA.post (f b) s0 sf ∗ R) → (sf.mem ⊨ specB.post b s0 sf ∗ R))
    (hpan : ∀ a s0 sf, specA.onPanic a s0 sf = ⌜False⌝ := by intro _ _ _; rfl)
    (hexit : ∀ a c s0 sf, specA.onExit a c s0 sf = ⌜False⌝ := by intro _ _ _ _; rfl)
    (hoom : ∀ a s0 sf, specA.onOom a s0 sf = ⌜False⌝ := by intro _ _ _; rfl) :
    HookOk fn specB := by
  intro b R s0 hrun hb hsp
  obtain ⟨hkf, hsym, hout⟩ := hok (f b) R s0 hrun (hpre b R s0 hb) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hf⟩ | ⟨c, _, hf⟩ | ⟨_, hf⟩
  · exact Or.inl ⟨hret, hcc, hpost b R s0 (fn s0) hb hq⟩
  · rw [hpan] at hf; exact (not_satisfies_false_sepConj hf).elim
  · rw [hexit] at hf; exact (not_satisfies_false_sepConj hf).elim
  · rw [hoom] at hf; exact (not_satisfies_false_sepConj hf).elim

/-- `kyber::encapsulate(&pk, randomness)` (`sret x8`) with by-value 32-byte `coins`
(`memRegion g.coinsPtr 32` after call) and `pqxdhHookStackExt` (`16384` B) stack budget. -/
def kyberEncapsByValSpec (P : Primitives) : Spec KyberEncapsCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.pkPtr ∧ s.readReg64 .x1 = g.coinsPtr ∧ s.readReg64 .x8 = g.outPtr ∧
      g.pk1568.length = 1568 ∧ g.coins32.length = 32 ∧
      (P.kemEncaps g.pk1568 g.coins32).isSome⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
      (g.coinsPtr ↦ₛ bytesToBv8 g.coins32) ∗
      memRegion g.outPtr 1600 ∗ stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
      memRegion g.coinsPtr 32 ∗
      (g.outPtr ↦ₛ fitBv8 1600 (kyberEncapsOutBytes P g.pk1568 g.coins32)) ∗
      stackAt s0.sp pqxdhHookStackExt

theorem hookSat_kyberEncapsByVal_of_kemEncaps_of_len {P : Primitives}
    {Q : CryptoVerification.E2E.PqxdhPrims}
    {ext : String → Option (State → State)}
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        Q.encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (hKem : HookSat ext CryptoVerification.E2E.kemEncapsName
      (SignalSession.CliExt.kemEncapsSpec Q)) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec P) := by
  rcases hKem with ⟨fn, hfn, hok⟩
  have hname : kyberEncapsStub = CryptoVerification.E2E.kemEncapsName := rfl
  refine ⟨fn, hname ▸ hfn, initAlice_hookOk_map
    (fun (g : KyberEncapsCall) =>
      (g.pkPtr, CryptoVerification.E2E.u8Vec 1568 g.pk1568,
       g.coinsPtr, CryptoVerification.E2E.u8Vec 32 g.coins32, g.outPtr))
    hok ?_ ?_⟩
  · intro g R s0 hpre
    simp only [kyberEncapsByValSpec, pqxdhHookStackExt,
      SignalSession.CliExt.kemEncapsSpec, SignalSession.CliExt.withStack,
      extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx8, hpk, hcoins, _⟩, hmem⟩
    rw [ResponderCore.u8Vec_toList_of_length hpk, ResponderCore.u8Vec_toList_of_length hcoins]
    exact ⟨⟨hx0, hx1, hx8⟩, by ac_nf at hmem ⊢⟩
  · intro g R s0 sf hpre hpost
    simp only [kyberEncapsByValSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, _, hpk, _hcoins, _⟩, _⟩
    simp only [kyberEncapsByValSpec, pqxdhHookStackExt,
      SignalSession.CliExt.kemEncapsSpec, SignalSession.CliExt.withStack,
      extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem⟩
    rw [ResponderCore.u8Vec_toList_of_length hpk] at hmem
    let o := Q.encaps (CryptoVerification.E2E.u8Vec 1568 g.pk1568)
      (CryptoVerification.E2E.u8Vec 32 g.coins32)
    have hout : fitBv8 1600 (kyberEncapsOutBytes P g.pk1568 g.coins32) =
        o.1.toList ++ o.2.toList :=
      fitBv8_kyberEncapsOutBytes_eq_extA_of_len Q.encaps hEncapsEq g.pk1568 g.coins32 hpk
    have hmerge : (g.outPtr ↦ₛ (o.1.toList ++ o.2.toList)) =
        (g.outPtr ↦ₛ o.1.toList) ∗ ((g.outPtr + 0x620#64) ↦ₛ o.2.toList) := by
      rw [pointsToBytes_append, o.1.toList_length]
    rw [hout, hmerge]
    exact ⟨htr, by ac_nf at hmem ⊢⟩

theorem hookSat_kyberEncapsByVal_of_kemEncaps {P : Primitives}
    {Q : CryptoVerification.E2E.PqxdhPrims}
    {ext : String → Option (State → State)}
    (hEncapsEq : ∀ pk r : Bytes, P.kemEncaps pk r =
      let (ct, ss) :=
        Q.encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (hKem : HookSat ext CryptoVerification.E2E.kemEncapsName
      (SignalSession.CliExt.kemEncapsSpec Q)) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec P) :=
  hookSat_kyberEncapsByVal_of_kemEncaps_of_len (fun pk r _ => hEncapsEq pk r) hKem

theorem hookSat_kyberEncapsByVal_of_externsOk
    (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives) {P0 : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec (initiatorModelPrims X P0)) :=
  hookSat_kyberEncapsByVal_of_kemEncaps_of_len
    (fun pk r hpk => by
      simp only [initiatorModelPrims, ResponderCore.ofSignalPqxdhPrimitives,
        CryptoVerification.E2E.modelPrims, CryptoVerification.E2E.blockLevelPrims,
        SignalPqxdh.kyberPkLen, hpk, beq_self_eq_true, ↓reduceIte])
    hOk.kemEncaps

theorem hookSat_cliExternsWith_kyberEncapsByVal {P : Primitives}
    {ext : String → Option (State → State)}
    (hEncaps : HookSat ext kyberEncapsStub (kyberEncapsByValSpec P)) :
    HookSat (SignalSession.cliExternsWith ext) kyberEncapsStub (kyberEncapsByValSpec P) := by
  rcases hEncaps with ⟨fn, hfn, hok⟩
  have hnp : CryptoVerification.E2E.isImagePanicSymbol kyberEncapsStub = false := by decide +kernel
  exact ⟨fn, by simp [SignalSession.cliExternsWith, CryptoVerification.E2E.withImagePanics, hnp, hfn], hok⟩

theorem kyberEncapsByVal_ok_at_ext {P : Primitives} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hEncaps : HookSat ext kyberEncapsStub (kyberEncapsByValSpec P))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff kyberEncapsStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (kyberEncapsByValSpec P) :=
  hook_ok_at (hname := kyberEncapsStub) rfl hk
    (by rw [(ls_stub% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")]; decide)
    (fun H => by
      rw [(ls_stub% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")]
      exact (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::encapsulate") H)
    (by decide +kernel)
    (by
      rcases hEncaps with ⟨fn, hfn, hok⟩
      exact ⟨fn, by rw [← hfn], hok⟩)

/-- Hook hypotheses needed by `<PrivateKey>::calculate_agreement` and `initialize_alice_session`
Stage 1 DH steps on `tripleRatchetProgAtExt`. -/
structure InitAliceAgreeHooks (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocHooks A ext
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" SignalSession.CliExt.shimSpec
  memcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec
  blackBox : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec
  dh : HookSat ext dhName (SignalSession.CliExt.dhSpec C)
  staticDrop : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec
  sharedDrop : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec

theorem InitAliceAgreeHooks.of_externsOk
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    InitAliceAgreeHooks P0.C A ext where
  alloc := hOk.alloc
  shim := hOk.shim
  memcpy := hOk.memcpy
  blackBox := hOk.blackBox
  dh := hOk.dh
  staticDrop := hOk.staticDrop
  sharedDrop := hOk.sharedDrop

theorem InitAliceAgreeHooks.to_cliExternsWith
    {C : Crypto} {A : RustAlloc} {ext : String → Option (State → State)}
    (hH : InitAliceAgreeHooks C A ext) :
    InitAliceAgreeHooks C A (SignalSession.cliExternsWith ext) := by
  have heq : ∀ s, CryptoVerification.E2E.isImagePanicSymbol s = false →
      SignalSession.cliExternsWith ext s = ext s := by
    intro s hs; simp [SignalSession.cliExternsWith, CryptoVerification.E2E.withImagePanics, hs]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hH.alloc.alloc with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.alloc.dealloc with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.alloc.realloc with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.shim with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.memcpy with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.blackBox with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.dh with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.staticDrop with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩
  · rcases hH.sharedDrop with ⟨f, hf, hok⟩
    exact ⟨f, (heq _ (by decide +kernel)).trans hf, hok⟩

theorem InitAliceAgreeHooks.of_cliExternsOk
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    InitAliceAgreeHooks P0.C A (SignalSession.cliExternsWith ext) :=
  (InitAliceAgreeHooks.of_externsOk hOk).to_cliExternsWith

def initAliceMemcpyRegionExtSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

private theorem initAlice_hookSat_shim {ext : String → Option (State → State)}
    (h : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" SignalSession.CliExt.shimSpec) :
    HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" pqxdhShimSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, hfn, initAlice_hookOk_map id hok (fun _ _ _ hp => hp) (fun _ _ _ _ _ hq => hq)⟩

private theorem initAlice_hookSat_memcpy {ext : String → Option (State → State)}
    (h : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec) :
    HookSat ext "memcpy" initAliceMemcpyRegionExtSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, initAlice_hookOk_map (fun x => x) hok ?_ ?_⟩
  · rintro ⟨dst, src, bs⟩ R s0 hpre
    simp only [initAliceMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
    have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
      rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact ⟨⟨hx0, hx1, hx2_nat⟩, by ac_nf at hmem ⊢⟩
  · rintro ⟨dst, src, bs⟩ R s0 sf _ hpost
    simp only [initAliceMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem⟩
    exact ⟨hp, by ac_nf at hmem ⊢⟩

theorem initAlice_shim_ok_at_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      SignalSession.CliExt.shimSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) pqxdhShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    (initAlice_hookSat_shim hShim)

theorem initAlice_memcpy_region_ok_at_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      initAliceMemcpyRegionExtSpec :=
  hook_ok_at (hname := "memcpy") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    (initAlice_hookSat_memcpy hMemcpy)

theorem initAlice_alloc_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := "__rustc::__rust_alloc") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hA.alloc

theorem initAlice_dealloc_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := "__rustc::__rust_dealloc") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hA.dealloc

/-- `<PrivateKey>::calculate_agreement` contract on `tripleRatchetProgAtExt` requiring only
`img.FrozenLoaded s` (no `s.symtab = img.symtab` hypothesis) and `initAliceCalcStackExt` (`16608` B). -/
def pqxdhCalculateAgreementFrozenSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜img.FrozenLoaded s ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt sp initAliceCalcStackExt
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp initAliceCalcStackExt
  onPanic := rustPanicOnOom img

def InitAliceCalculateAgreementOkExt (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementSym)
    (pqxdhCalculateAgreementFrozenSpecExt P A img)

/-- Discharges `<PrivateKey>::calculate_agreement` on `tripleRatchetProgAtExt img.base ext`
with only `img.FrozenLoaded s` (usable both in `initialize_alice_session` and in `cliInitiate`
where `s.symtab ≠ libsignalSessionImage.symtab`). -/
theorem calculateAgreement_frozen_ok_ext {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : InitAliceAgreeHooks C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementSym)
      (pqxdhCalculateAgreementFrozenSpecExt P A img) := by
  have hct : ConsumeMessageKeyTransfer.CtEqROOkExt32 img.base ext :=
    ConsumeMessageKeyTransfer.ctEqRO_ok_ext32 img.base hH.blackBox
  have hraw := ResponderCore.calculateAgreement_rodata_ok_ext himg hct
    hH.alloc hH.dh hH.sharedDrop hH.shim hH.staticDrop
  refine subroutine_ok_outcome_intro ?_
  rintro ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hpc hrun hpre hsp
  dsimp only [pqxdhCalculateAgreementFrozenSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hpre⟩
  have hro := rodata_0x7ff6a himg hF.roData hpre
  let xg : CryptoVerification.LibsignalTripleRatchet.CalculateAgreementGhost :=
    ⟨ourA, ⟨CryptoVerification.E2E.u8Vec 32 ourSk32⟩,
     theirA, ⟨CryptoVerification.E2E.u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 :=
    ResponderCore.u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 :=
    ResponderCore.u8Vec_toList_of_length htheir
  have hpre' : s0.mem ⊨
      (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
        (CryptoVerification.LibsignalTripleRatchet.Keys.calculateAgreementSpecAt
          C.X A initAliceCalcSubStackExt).pre xg s0) ∗ R := by
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Keys.calculateAgreementSpecAt,
      initAliceCalcStackExt]
    rw [hour_list, htheir_list]
    have hcomm :
        (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            memRegion ret 24 ∗ A.pool ∗ stackAt s0.sp (160 + initAliceCalcSubStackExt))) ∗ R =
        ⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
          (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
              memRegion ret 24 ∗ A.pool ∗ stackAt s0.sp (160 + initAliceCalcSubStackExt) ∗ R)) := by
      ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by rw [hsp_eq]; ac_nf at hro ⊢⟩
  have hpc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName := hpc
  refine (hraw.to_outcome xg R s0 hpc' hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Keys.calculateAgreementSpecAt,
      pqxdhCalculateAgreementFrozenSpecExt, initAliceCalcStackExt] at hq ⊢
    rw [hour_list, htheir_list, hsp_eq] at hq
    have hE := ResponderCore.calculateAgreementResultAt_entails_pqxdh hP A ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A ret (calculateAgreement C.X xg.their xg.our) ∗
          (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (⌜sf.trace = s0.trace⌝ ∗
              (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
              A.pool ∗ stackAt sp (160 + initAliceCalcSubStackExt) ∗ R)) := by
      ac_nf at hq ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    have hq3 : sf.mem ⊨
        ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          ((⌜sf.trace = s0.trace⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
            stackAt sp (160 + initAliceCalcSubStackExt)) ∗ R) := by
      ac_nf at hq2 ⊢
    exact Satisfies.of_sep_right hq3
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Keys.calculateAgreementSpecAt,
      pqxdhCalculateAgreementFrozenSpecExt, rustPanicOnOom] at hq ⊢
    exact hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem calculateAgreement_frozen_ok_of_externsOk (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives)
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementSym)
      (pqxdhCalculateAgreementFrozenSpecExt (initiatorModelPrims X P0) A img) :=
  calculateAgreement_frozen_ok_ext (ResponderCore.primitivesMatchCrypto_modelPrims X P0)
    himg (InitAliceAgreeHooks.of_externsOk hOk)

theorem calculateAgreement_frozen_ok_of_cliExternsOk (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives)
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr
        calculateAgreementSym)
      (pqxdhCalculateAgreementFrozenSpecExt (initiatorModelPrims X P0) A img) :=
  calculateAgreement_frozen_ok_ext (ResponderCore.primitivesMatchCrypto_modelPrims X P0)
    himg (InitAliceAgreeHooks.of_cliExternsOk hOk)

theorem stackAt_calc_split_alloc_ext (fsp : BitVec 64) :
    stackAt fsp initAliceCalcStackExt =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 16608#64) 12512 := by
  have h1 := initAlice_stackAt_split fsp 12512 allocHookStack (by decide)
  have h2 : (12512 + allocHookStack : Nat) = initAliceCalcStackExt := by decide
  have h3 : BitVec.ofNat 64 (12512 + allocHookStack) = 16608#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

theorem stackAt_calculateAgreement_eq_pqxdh_ext (fsp : BitVec 64) :
    stackAt fsp initAliceCalcStackExt =
      memRegion (fsp - 16608#64) 224 ∗ stackAt fsp pqxdhHookStackExt := by
  have h1 := initAlice_stackAt_split fsp 224 pqxdhHookStackExt (by decide)
  have h2 : (224 + pqxdhHookStackExt : Nat) = initAliceCalcStackExt := by decide
  have h3 : BitVec.ofNat 64 (224 + pqxdhHookStackExt) = 16608#64 := rfl
  rw [h3] at h1
  rw [← h2, h1]

theorem stackAt_pqxdh_split_alloc_ext (fsp : BitVec 64) :
    stackAt fsp pqxdhHookStackExt =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 16384#64) 12288 := by
  have h1 := initAlice_stackAt_split fsp 12288 allocHookStack (by decide)
  have h2 : (12288 + allocHookStack : Nat) = pqxdhHookStackExt := by decide
  have h3 : BitVec.ofNat 64 (12288 + allocHookStack) = 16384#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

end CryptoVerification.E2E.Pqxdh.Initiator
