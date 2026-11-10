/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Invariants

Shared `S2FrameRO`-backed frame invariants (`HFrameExt`, `HCommonExt`, `HPreExt`) and extract-phase
cut predicates at stack budget `hkdfToSliceStackExt` (`17616` B).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

/-! ## `HkdfStubsExt`, `CallingConventionPreserved` / `CalleeSaved` Helpers, & `RunsToE.trans_inv` -/

/-- Bundled contract-backed extern and internal callee contracts used by `spqr::kdf::hkdf_to_slice`. -/
structure HkdfStubsExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop where
  hooks  : SpqrKdfHooksExt img F ext
  nfs_ok : Nfs3GenRunsToEExt img F ext
  fin_ok : Fin3GenRunsToEExt img F ext

theorem cc_sp  {s s' : State} (h : CallingConventionPreserved s s') : s'.sp = s.sp := h.1
theorem cc_x19 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x19 = s.readReg64 .x19 := h.2.1
theorem cc_x20 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x20 = s.readReg64 .x20 := h.2.2.1
theorem cc_x21 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x21 = s.readReg64 .x21 := h.2.2.2.1
theorem cc_x22 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x22 = s.readReg64 .x22 := h.2.2.2.2.1
theorem cc_x23 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.2.1
theorem cc_x24 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.2.1
theorem cc_x25 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.2.1
theorem cc_x26 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.2.1
theorem cc_x27 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x27 = s.readReg64 .x27 := h.2.2.2.2.2.2.2.2.2.1
theorem cc_x28 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cc_x29 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x29 = s.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem cs_x29 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x29 = s.readReg64 .x29 :=
  h.2 .x29 (by simp)

theorem RunsToE.trans_inv {prog : Program} {img : Obj.Image} {s : State} {P Q : State → Prop}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (h1 : RunsToE prog s P)
    (h2 : ∀ s₁, img.FrozenLoaded s₁ → s₁.symtab = img.symtab → P s₁ → RunsToE prog s₁ Q) :
    RunsToE prog s Q := by
  intro hL; obtain ⟨s₁, hst1, htr1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hQ, hL2⟩ := h2 s₁ (hst1.frozenLoaded hfrz) (hst1.symtab_eq.trans hsym) hP hL1
  exact ⟨s₂, hst1.trans hst2, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩, hQ, hL2⟩

theorem RunsTo.trans_toE_inv {prog : Program} {img : Obj.Image} {s : State} {P Q : State → Prop}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (h1 : RunsTo prog s P)
    (h2 : ∀ s₁, img.FrozenLoaded s₁ → s₁.symtab = img.symtab → P s₁ → RunsToE prog s₁ Q) :
    RunsToE prog s Q :=
  RunsToE.trans_inv hfrz hsym (runsTo_toE h1) h2

/-! ## Frame (`HFrameExt`), Common Invariant (`HCommonExt`), and Preconditions (`HPreExt`) -/

/-- Contract-backed frame condition for `spqr::kdf::hkdf_to_slice`: only `[okmA .. okmA + okmLen)`
and `[hsp s₀ - 16928#64 .. hsp s₀ + 688#64)` (`hkdfToSliceStackExt = 17616` B) are modified,
allowing read-only `memcpy` touches on `roRegs`. -/
abbrev HFrameExt (roRegs : List (BitVec 64 × ℕ)) (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2FrameRO roRegs s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 16928#64, 17616)]

/-- Common state invariant across `spqr::kdf::hkdf_to_slice` under `S2FrameRO roRegs`. -/
structure HCommonExt (roRegs : List (BitVec 64 × ℕ)) (okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 592#64
  saved  : HSaved s₀ s.mem
  frame  : HFrameExt roRegs okmLen s₀ s.mem

/-- Bundled entry preconditions of `spqr::kdf::hkdf_to_slice` at stack budget
`hkdfToSliceStackExt = 17616` (`[hsp s₀ - 16928#64, hsp s₀ + 688#64)`). -/
structure HPreExt (b : BitVec 64) (saltRO ikmRO infoRO : Bool) (roRegs : List (BitVec 64 × ℕ))
    (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pc_eq        : s₀.pc = b + bv% (ls_off% hkdfToSliceName)
  status       : s₀.status = .Running
  x0_eq        : s₀.readReg64 .x0 = saltA
  x1_eq        : s₀.readReg64 .x1 = BitVec.ofNat 64 salt.length
  x2_eq        : s₀.readReg64 .x2 = ikmA
  x3_eq        : s₀.readReg64 .x3 = BitVec.ofNat 64 ikm.length
  x4_eq        : s₀.readReg64 .x4 = infoA
  x5_eq        : s₀.readReg64 .x5 = BitVec.ofNat 64 info.length
  x6_eq        : s₀.readReg64 .x6 = okmA
  x7_eq        : s₀.readReg64 .x7 = BitVec.ofNat 64 okmLen
  salt_lt      : salt.length < 2 ^ 63
  ikm_len      : ikm.length < 2 ^ 63
  info_ge      : 32 ≤ info.length
  info_lt      : info.length < 55
  okm_len      : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96
  base_al      : (b &&& 0xfff#64) = 0#64
  ro_iv_bytes  : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV
  ro_iv_read   : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32
  disj_iv_stk  : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (hsp s₀ - 16928#64) 17616
  disj_iv_okm  : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 okmA okmLen
  salt_inv     : KdfSliceInv saltRO roRegs s₀.mem saltA salt (hsp s₀ - 16928#64) 17616 okmA okmLen
  salt_ro_le   : saltRO = true → salt.length ≤ 64
  ikm_inv      : KdfSliceInv ikmRO roRegs s₀.mem ikmA ikm (hsp s₀ - 16928#64) 17616 okmA okmLen
  ikm_ro_lt    : ikmRO = true → ikm.length < 64
  info_inv     : KdfSliceInv infoRO roRegs s₀.mem infoA info (hsp s₀ - 16928#64) 17616 okmA okmLen
  rw_okm       : RW s₀.mem okmA okmLen
  rw_stack     : RW s₀.mem (hsp s₀ - 16928#64) 17616
  disj_okm_stk : DisjointRegions okmA okmLen (hsp s₀ - 16928#64) 17616
  ro_out_stk   : ∀ r ∈ roRegs, ∀ a, InRegion r.1 r.2 a → OutsideRegion (hsp s₀ - 16928#64) 17616 a
  ro_out_okm   : ∀ r ∈ roRegs, ∀ a, InRegion r.1 r.2 a → OutsideRegion okmA okmLen a
  sp_aligned   : (s₀.sp &&& 15#64) = 0#64

theorem HFrameExt.of_agreesOutside_hsp {roRegs : List (BitVec 64 × ℕ)} {okmLen : ℕ} {s₀ : State}
    {m m' : Memory} {off : BitVec 64} {sz : ℕ} (hf : HFrameExt roRegs okmLen s₀ m)
    (hA : AgreesOutside m m' (hsp s₀ + off) sz) (hoff : off.toNat + sz ≤ 688) :
    HFrameExt roRegs okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := hsp s₀ - 16928#64) (rlen := 17616) (by simp) (by clear * - hoff; bv_omega) hA

theorem HFrameExt.of_agreesOutside_okm {roRegs : List (BitVec 64 × ℕ)} {okmLen : ℕ} {s₀ : State}
    {m m' : Memory} {off : BitVec 64} {sz : ℕ} (hf : HFrameExt roRegs okmLen s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x6 + off) sz) (hoff : off.toNat + sz ≤ okmLen) :
    HFrameExt roRegs okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := s₀.readReg64 .x6) (rlen := okmLen) (by simp) (by clear * - hoff; bv_omega) hA

section HFrameExtProps

variable {b : BitVec 64} {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
  {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
  {okmLen : ℕ} {s₀ : State} {m : Memory}

theorem HFrameExt.rw_stack
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW (hsp s₀ - 16928#64) 17616 :=
  hf.rw_of_rw _ _ hpre.ro_out_stk hpre.rw_stack

theorem HFrameExt.rw_hsp
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW (hsp s₀) 688 := (HFrameExt.rw_stack hpre hf).sub (by bv_omega)

theorem HFrameExt.rw_sub_16928
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW (hsp s₀ - 16928#64) 16928 := (HFrameExt.rw_stack hpre hf).sub (by bv_omega)

theorem HFrameExt.rw_sub_16528
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW (hsp s₀ - 16528#64) 16528 := (HFrameExt.rw_stack hpre hf).sub (by bv_omega)

theorem HFrameExt.rw_ext_stk
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW (hsp s₀ - BitVec.ofNat 64 extHookStack) extHookStack :=
  (HFrameExt.rw_stack hpre hf).sub (by dsimp [extHookStack]; bv_omega)

theorem HFrameExt.rw_okm
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.RW okmA okmLen := hf.rw_of_rw _ _ hpre.ro_out_okm hpre.rw_okm

theorem HFrameExt.ro_iv_read
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
  hf.readable_of_readable _ _ hpre.ro_iv_read

theorem HFrameExt.ro_iv_bytes
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
  refine (hf.readBytes_eq hpre.ro_iv_read (fun r hr => ?_) (by decide)).trans hpre.ro_iv_bytes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq]; exact hpre.disj_iv_okm.symm
  · exact hpre.disj_iv_stk.symm

theorem HFrameExt.salt_inv
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    KdfSliceInv saltRO roRegs m saltA salt (hsp s₀ - 16928#64) 17616 okmA okmLen := by
  have hf' : S2FrameRO roRegs s₀.mem m [(okmA, okmLen), (hsp s₀ - 16928#64, 17616)] := by
    simpa [HFrameExt, hpre.x6_eq] using hf
  exact hpre.salt_inv.of_s2FrameRO hf' (by have := hpre.salt_lt; omega)

theorem HFrameExt.ikm_inv
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    KdfSliceInv ikmRO roRegs m ikmA ikm (hsp s₀ - 16928#64) 17616 okmA okmLen := by
  have hf' : S2FrameRO roRegs s₀.mem m [(okmA, okmLen), (hsp s₀ - 16928#64, 17616)] := by
    simpa [HFrameExt, hpre.x6_eq] using hf
  exact hpre.ikm_inv.of_s2FrameRO hf' (by have := hpre.ikm_len; omega)

theorem HFrameExt.info_inv
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    KdfSliceInv infoRO roRegs m infoA info (hsp s₀ - 16928#64) 17616 okmA okmLen := by
  have hf' : S2FrameRO roRegs s₀.mem m [(okmA, okmLen), (hsp s₀ - 16928#64, 17616)] := by
    simpa [HFrameExt, hpre.x6_eq] using hf
  exact hpre.info_inv.of_s2FrameRO hf' (by have := hpre.info_lt; omega)

theorem HFrameExt.salt_read
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.Readable saltA salt.length := (HFrameExt.salt_inv hpre hf).readable

theorem HFrameExt.salt_bytes
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.readBytes saltA salt.length = salt := (HFrameExt.salt_inv hpre hf).bytes_eq

theorem HFrameExt.ikm_read
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.Readable ikmA ikm.length := (HFrameExt.ikm_inv hpre hf).readable

theorem HFrameExt.ikm_bytes
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.readBytes ikmA ikm.length = ikm := (HFrameExt.ikm_inv hpre hf).bytes_eq

theorem HFrameExt.ikm_rw_ge64
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) (hge : 64 ≤ ikm.length) :
    m.RW ikmA ikm.length := by
  have hinv := HFrameExt.ikm_inv hpre hf
  cases hikmRO : ikmRO
  · have hp := hinv.perm_inv
    rw [hikmRO] at hp
    exact hp.1
  · have := hpre.ikm_ro_lt hikmRO
    omega

theorem HFrameExt.info_read
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.Readable infoA info.length := (HFrameExt.info_inv hpre hf).readable

theorem HFrameExt.info_bytes
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m) :
    m.readBytes infoA info.length = info := (HFrameExt.info_inv hpre hf).bytes_eq

theorem HPreExt.disj_salt_stk
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    salt.length = 0 ∨ DisjointRegions saltA salt.length (hsp s₀ - 16928#64) 17616 := by
  by_cases h0 : salt.length = 0
  · exact Or.inl h0
  · exact Or.inr (SpqrKdfExt.disjointRegions_of_outside (by omega) (by decide) hpre.salt_inv.out_stk)

theorem HPreExt.disj_ikm_stk
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    ikm.length = 0 ∨ DisjointRegions ikmA ikm.length (hsp s₀ - 16928#64) 17616 := by
  by_cases h0 : ikm.length = 0
  · exact Or.inl h0
  · exact Or.inr (SpqrKdfExt.disjointRegions_of_outside (by omega) (by decide) hpre.ikm_inv.out_stk)

theorem HPreExt.disj_info_stk
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    DisjointRegions infoA info.length (hsp s₀ - 16928#64) 17616 :=
  SpqrKdfExt.disjointRegions_of_outside (by have := hpre.info_ge; omega) (by decide) hpre.info_inv.out_stk

theorem HSaved.of_agreesOutside_okm_ext {m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hs : HSaved s₀ m) (hA : AgreesOutside m m' (okmA + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) : HSaved s₀ m' := by
  have hd_okm_saved : DisjointRegions (okmA + off) sz (hsp s₀ + 592#64) 96 :=
    (hpre.disj_okm_stk.sub_left (okmA + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ + 592#64) ⟨by decide, by bv_omega⟩
  have hread (k : BitVec 64) (hk : 592 ≤ k.toNat ∧ k.toNat + 8 ≤ 688) :
      m'.read64 (hsp s₀ + k) = m.read64 (hsp s₀ + k) :=
    hA.read64_eq (hd_okm_saved.sub_right (hsp s₀ + k) ⟨by decide, by rcases hk with ⟨_, _⟩; bv_omega⟩)
  exact ⟨(hread 592#64 (by decide)).trans hs.m592, (hread 600#64 (by decide)).trans hs.m600,
    (hread 608#64 (by decide)).trans hs.m608, (hread 616#64 (by decide)).trans hs.m616,
    (hread 624#64 (by decide)).trans hs.m624, (hread 632#64 (by decide)).trans hs.m632,
    (hread 640#64 (by decide)).trans hs.m640, (hread 648#64 (by decide)).trans hs.m648,
    (hread 656#64 (by decide)).trans hs.m656, (hread 664#64 (by decide)).trans hs.m664,
    (hread 672#64 (by decide)).trans hs.m672, (hread 680#64 (by decide)).trans hs.m680⟩

end HFrameExtProps

theorem HSaved.of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m m' : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hs : HSaved s₀ m) (hrw_hsp : m.RW (hsp s₀) 688) (hfr : S2FrameRO roRegs m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96) : HSaved s₀ m' := by
  have h_saved_eq (off : BitVec 64) (hoff : decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true) :
      m'.read64 (hsp s₀ + off) = m.read64 (hsp s₀ + off) := by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    have hrd : m.Readable (hsp s₀ + off) 8 := (hrw_hsp.sub (by bv_omega)).readable
    refine hfr.read64_eq_of_readable hrd fun r hr => ?_
    exact (hd r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  exact ⟨(h_saved_eq 592#64 (by decide)).trans hs.m592, (h_saved_eq 600#64 (by decide)).trans hs.m600,
    (h_saved_eq 608#64 (by decide)).trans hs.m608, (h_saved_eq 616#64 (by decide)).trans hs.m616,
    (h_saved_eq 624#64 (by decide)).trans hs.m624, (h_saved_eq 632#64 (by decide)).trans hs.m632,
    (h_saved_eq 640#64 (by decide)).trans hs.m640, (h_saved_eq 648#64 (by decide)).trans hs.m648,
    (h_saved_eq 656#64 (by decide)).trans hs.m656, (h_saved_eq 664#64 (by decide)).trans hs.m664,
    (h_saved_eq 672#64 (by decide)).trans hs.m672, (h_saved_eq 680#64 (by decide)).trans hs.m680⟩

theorem HSaved.of_s2Frame {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : HSaved s₀ m) (hrw_hsp : m.RW (hsp s₀) 688) (hfr : S2Frame m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96) : HSaved s₀ m' :=
  HSaved.of_s2FrameRO hs hrw_hsp (S2FrameRO.of_s2frame (roRegs := []) hfr) hd

theorem HCommonExt.of_agreesOutside_hsp {roRegs : List (BitVec 64 × ℕ)} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HCommonExt roRegs okmLen s₀ s)
    (hstat : s'.status = .Running) (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    HCommonExt roRegs okmLen s₀ s' := by
  have ⟨h1, h2⟩ : 0 < sz ∧ off.toNat + sz ≤ 592 := of_decide_eq_true hoff
  exact ⟨hstat, hsp_eq, hx29, HSaved.of_agreesOutside_low hc.saved hA ⟨h1, h2⟩,
    HFrameExt.of_agreesOutside_hsp hc.frame hA (by omega)⟩

section HCommonExtProps

variable {b : BitVec 64} {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
  {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
  {okmLen : ℕ} {s₀ s s' : State}

theorem HCommonExt.of_agreesOutside_okm {off : BitVec 64} {sz : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀) (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (okmA + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) : HCommonExt roRegs okmLen s₀ s' := by
  have hA' : AgreesOutside s.mem s'.mem (s₀.readReg64 .x6 + off) sz := by rw [hpre.x6_eq]; exact hA
  exact ⟨hstat, hsp_eq, hx29, HSaved.of_agreesOutside_okm_ext hpre hc.saved hA hoff,
    HFrameExt.of_agreesOutside_okm hc.frame hA' hoff.2⟩

theorem HCommonExt.of_s2FrameRO_hsp {dstOff : BitVec 64} {dstLen stkLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2FrameRO roRegs s.mem s'.mem [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 stkLen, stkLen)])
    (hdst : dstOff.toNat < 592 ∧ dstOff.toNat + dstLen ≤ 592)
    (hstk : 0 < stkLen ∧ stkLen ≤ 16928) : HCommonExt roRegs okmLen s₀ s' := by
  have hsaved' : HSaved s₀ s'.mem := by
    refine HSaved.of_s2FrameRO hc.saved (HFrameExt.rw_hsp hpre hc.frame) hfr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rcases hdst with ⟨_, _⟩; rcases hstk with ⟨_, _⟩; unfold DisjointRegions; bv_omega)
  have hframe' : HFrameExt roRegs okmLen s₀ s'.mem := by
    refine S2FrameRO.trans hc.frame (S2FrameRO.mono hfr ?_); intro a ha r hr
    have hstack := ha (hsp s₀ - 16928#64, 17616) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rcases hdst with ⟨_, _⟩; rcases hstk with ⟨_, _⟩; unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, (cc_sp hcc).trans hc.sp_eq, (cc_x29 hcc).trans hc.x29_eq, hsaved', hframe'⟩

theorem HCommonExt.of_s2Frame_hsp {dstOff : BitVec 64} {dstLen stkLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 stkLen, stkLen)])
    (hdst : dstOff.toNat < 592 ∧ dstOff.toNat + dstLen ≤ 592)
    (hstk : 0 < stkLen ∧ stkLen ≤ 16928) : HCommonExt roRegs okmLen s₀ s' :=
  HCommonExt.of_s2FrameRO_hsp hpre hc hstat hcc (S2FrameRO.of_s2frame hfr) hdst hstk

theorem HCommonExt.of_nfs_frameRO
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2FrameRO roRegs s.mem s'.mem [(hsp s₀ + 32#64, 0x98), (hsp s₀ - 16928#64, 16928)]) :
    HCommonExt roRegs okmLen s₀ s' := by
  have hsaved' : HSaved s₀ s'.mem := by
    refine HSaved.of_s2FrameRO hc.saved (HFrameExt.rw_hsp hpre hc.frame) hfr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hframe' : HFrameExt roRegs okmLen s₀ s'.mem := by
    refine S2FrameRO.trans hc.frame (S2FrameRO.mono hfr ?_); intro a ha r hr
    have hstack := ha (hsp s₀ - 16928#64, 17616) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, hcs.1.trans hc.sp_eq, (cs_x29 hcs).trans hc.x29_eq, hsaved', hframe'⟩

theorem HCommonExt.of_s2FrameRO_okm {okmOff : BitVec 64} {okmSub stkLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2FrameRO roRegs s.mem s'.mem [(okmA + okmOff, okmSub), (hsp s₀ - BitVec.ofNat 64 stkLen, stkLen)])
    (hokm : 0 < okmSub ∧ okmOff.toNat + okmSub ≤ okmLen)
    (hstk : 0 < stkLen ∧ stkLen ≤ 16928) : HCommonExt roRegs okmLen s₀ s' := by
  have hd_okm_saved : DisjointRegions (okmA + okmOff) okmSub (hsp s₀ + 592#64) 96 :=
    (hpre.disj_okm_stk.sub_left (okmA + okmOff)
      ⟨hokm.1, by have := hokm.2; have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ + 592#64) ⟨by decide, by bv_omega⟩
  have hsaved' : HSaved s₀ s'.mem := by
    refine HSaved.of_s2FrameRO hc.saved (HFrameExt.rw_hsp hpre hc.frame) hfr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_okm_saved
    · rcases hstk with ⟨_, _⟩; unfold DisjointRegions; bv_omega
  have hframe' : HFrameExt roRegs okmLen s₀ s'.mem := by
    refine S2FrameRO.trans hc.frame (S2FrameRO.mono hfr ?_); intro a ha r hr
    have hokm_out : OutsideRegion okmA okmLen a := by
      rw [← hpre.x6_eq]; exact ha (s₀.readReg64 .x6, okmLen) (by simp)
    have hstack := ha (hsp s₀ - 16928#64, 17616) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hokm.2; unfold OutsideRegion at *; bv_omega
    · rcases hstk with ⟨_, _⟩; unfold OutsideRegion at *; bv_omega
  exact ⟨hstat, (cc_sp hcc).trans hc.sp_eq, (cc_x29 hcc).trans hc.x29_eq, hsaved', hframe'⟩

theorem HCommonExt.of_s2Frame_okm {okmOff : BitVec 64} {okmSub stkLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem [(okmA + okmOff, okmSub), (hsp s₀ - BitVec.ofNat 64 stkLen, stkLen)])
    (hokm : 0 < okmSub ∧ okmOff.toNat + okmSub ≤ okmLen)
    (hstk : 0 < stkLen ∧ stkLen ≤ 16928) : HCommonExt roRegs okmLen s₀ s' :=
  HCommonExt.of_s2FrameRO_okm hpre hc hstat hcc (S2FrameRO.of_s2frame hfr) hokm hstk

theorem HCommonExt.of_fin_frame {outOff : BitVec 64}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + outOff, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 16528#64, 16528)])
    (hout : decide (outOff.toNat + 32 ≤ 592) = true) : HCommonExt roRegs okmLen s₀ s' := by
  have hout' : outOff.toNat + 32 ≤ 592 := of_decide_eq_true hout
  have hsaved' : HSaved s₀ s'.mem := by
    refine HSaved.of_s2Frame hc.saved (HFrameExt.rw_hsp hpre hc.frame) hfr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hframe' : HFrameExt roRegs okmLen s₀ s'.mem := by
    refine S2FrameRO.trans hc.frame (S2FrameRO.mono (S2FrameRO.of_s2frame hfr) ?_); intro a ha r hr
    have hstack := ha (hsp s₀ - 16928#64, 17616) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, hcs.1.trans hc.sp_eq, (cs_x29 hcs).trans hc.x29_eq, hsaved', hframe'⟩

end HCommonExtProps

/-! ## Extract-Phase Cut Predicates (`hex:63284 → hex:633cc`) -/

structure StateENfs1Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% newFromSlice3Name)
  common : HCommonExt roRegs okmLen s₀ s
  lr_eq  : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 72)
  x0_eq  : s.readReg64 .x0 = hsp s₀ + 32#64
  x1_eq  : s.readReg64 .x1 = saltA
  x2_eq  : s.readReg64 .x2 = BitVec.ofNat 64 salt.length
  x22_eq : s.readReg64 .x22 = okmA
  x23_eq : s.readReg64 .x23 = ikmA
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq : s.readReg64 .x27 = infoA

structure StateERet1Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (ikmA infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 72)
  common  : HCommonExt roRegs okmLen s₀ s
  x22_eq  : s.readReg64 .x22 = okmA
  x23_eq  : s.readReg64 .x23 = ikmA
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  tag_32  : s.mem.read64 (hsp s₀ + 32#64) = 0#64
  hmac_40 : HmacSt s.mem (hsp s₀ + 40#64) F (effectiveHmacKey F salt) []

structure StateE3ccExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% hkdfToSliceName + 328)
  common   : HCommonExt roRegs okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_208 : ∃ pfx tail, pfx ++ tail = ikm ∧ pfx.length % 64 = 0 ∧ tail.length < 64 ∧
               HmacStN s.mem (hsp s₀ + 208#64) F (effectiveHmacKey F salt) pfx tail

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof
