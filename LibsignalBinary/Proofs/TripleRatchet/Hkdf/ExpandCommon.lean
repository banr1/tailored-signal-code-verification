/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common
import LibsignalBinary.Proofs.AesCbc.Bytes

/-!
# Shared Definitions and Cut Invariants for `expand_multi_info`

Defines the `hkdfExpand` block functions `t1`–`t3`, stack-frame invariants, `HmacSt`
transfer lemmas, and cut-point predicates `StateX0p`–`ExpandPost` for
`GenericHkdf<Hmac<Sha256>>::expand_multi_info`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Expand

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [scoped simp, arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

/-! ## Pure HKDF-Expand Block Helpers -/

/-- First 32-byte HKDF-Expand block `T(1) = HMAC(prk, info ‖ [1])`. -/
def t1 (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    List (BitVec 8) :=
  hmacWith F prk (info ++ [1#8])

/-- Second 32-byte HKDF-Expand block `T(2) = HMAC(prk, T(1) ‖ info ‖ [2])`. -/
def t2 (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    List (BitVec 8) :=
  hmacWith F prk (t1 F prk info ++ info ++ [2#8])

/-- Third 32-byte HKDF-Expand block `T(3) = HMAC(prk, T(2) ‖ info ‖ [3])`. -/
def t3 (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    List (BitVec 8) :=
  hmacWith F prk (t2 F prk info ++ info ++ [3#8])

@[scoped simp]
theorem t1_length (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    (t1 F prk info).length = 32 :=
  length_hmacWith F prk (info ++ [1#8])

@[scoped simp]
theorem t2_length (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    (t2 F prk info).length = 32 :=
  length_hmacWith F prk (t1 F prk info ++ info ++ [2#8])

@[scoped simp]
theorem t3_length (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    (t3 F prk info).length = 32 :=
  length_hmacWith F prk (t2 F prk info ++ info ++ [3#8])

theorem hkdfExpand_64_eq (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 64 = t1 F prk info ++ t2 F prk info := by
  dsimp only [hkdfExpand]
  have h2 : (64 + 31) / 32 = 2 := rfl
  have hblocks : (hkdfBlocks F prk info 2).flatten = t1 F prk info ++ t2 F prk info := by
    simp [hkdfBlocks, t1, t2, List.append_assoc]
  rw [h2, hblocks, List.take_of_length_le]
  simp [t1, t2, length_hmacWith]

theorem hkdfExpand_80_eq (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 80 =
      t1 F prk info ++ t2 F prk info ++ (t3 F prk info).take 16 := by
  dsimp only [hkdfExpand]
  have h3 : (80 + 31) / 32 = 3 := rfl
  have hblocks : (hkdfBlocks F prk info 3).flatten =
      (t1 F prk info ++ t2 F prk info) ++ t3 F prk info := by
    simp [hkdfBlocks, t1, t2, t3, List.append_assoc]
  have hlen12 : (t1 F prk info ++ t2 F prk info).length = 64 := by simp
  rw [h3, hblocks, List.take_append, List.take_of_length_le (by omega), hlen12]

/-! ## Stack Frame, Preconditions, and Saved Registers -/

/-- `expand_multi_info`'s stack pointer after the prologue (`s₀.sp - 496#64`). -/
def esp (s₀ : State) : BitVec 64 := s₀.sp - 496#64

theorem esp_eq_add (s₀ : State) : s₀.sp = esp s₀ + 496#64 := by
  unfold esp; bv_lin

@[scoped simp, arm64_norm]
theorem sp_sub_496_eq_esp (s₀ : State) : s₀.sp - 496#64 = esp s₀ := rfl

@[scoped simp, arm64_norm]
theorem sp_add_neg496_eq_esp (s₀ : State) :
    s₀.sp + bv% (2 ^ 64 - 496) = esp s₀ := by
  unfold esp; bv_lin

@[scoped simp, arm64_norm]
theorem esp_add_496_sub_496 (s₀ : State) : (esp s₀ + 496#64) - 496#64 = esp s₀ := by
  bv_lin

theorem esp_aligned {s₀ : State} (h : (s₀.sp &&& 15#64) = 0#64) :
    (esp s₀ &&& 15#64) = 0#64 := by
  unfold esp; bv_bits

theorem esp_add_496_aligned {s₀ : State} (h : (s₀.sp &&& 15#64) = 0#64) :
    ((esp s₀ + 496#64) &&& 15#64) = 0#64 := by
  rw [← esp_eq_add]; exact h

@[scoped simp, arm64_norm]
theorem read8_write64_120_127 (m : Memory) (sp v : BitVec 64) :
    (m.write64 (sp + 120#64) v).read8 (sp + 127#64) = v.extractLsb' 56 8 := by
  dsimp only [Memory.write64]
  simp [arm64_norm]

/-- Saved callee-saved registers in `[esp s₀ + 400, esp s₀ + 496)`. -/
structure ExpandSaved (s₀ : State) (m : Memory) : Prop where
  m400 : m.read64 (esp s₀ + 400#64) = s₀.readReg64 .x29
  m408 : m.read64 (esp s₀ + 408#64) = s₀.readReg64 .lr
  m416 : m.read64 (esp s₀ + 416#64) = s₀.readReg64 .x28
  m424 : m.read64 (esp s₀ + 424#64) = s₀.readReg64 .x27
  m432 : m.read64 (esp s₀ + 432#64) = s₀.readReg64 .x26
  m440 : m.read64 (esp s₀ + 440#64) = s₀.readReg64 .x25
  m448 : m.read64 (esp s₀ + 448#64) = s₀.readReg64 .x24
  m456 : m.read64 (esp s₀ + 456#64) = s₀.readReg64 .x23
  m464 : m.read64 (esp s₀ + 464#64) = s₀.readReg64 .x22
  m472 : m.read64 (esp s₀ + 472#64) = s₀.readReg64 .x21
  m480 : m.read64 (esp s₀ + 480#64) = s₀.readReg64 .x20
  m488 : m.read64 (esp s₀ + 488#64) = s₀.readReg64 .x19

/-- Frame of `expand_multi_info`: only `(s₀.readReg64 .x2, okmLen)` and
    `(s₀.sp - 640#64, 640)` change. -/
abbrev ExpandFrame (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  Frame s₀.mem m [(s₀.readReg64 .x2, okmLen), (s₀.sp - 640#64, 640)]

/-- Bundled preconditions of `expandMultiInfoSpec` at entry state `s₀`. -/
structure ExpandPre (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pc_eq         : s₀.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")
  status        : s₀.status = .Running
  x3_eq         : s₀.readReg64 .x3 = BitVec.ofNat 64 okmLen
  prk_le        : prk.length ≤ 64
  info_lt       : info.length < 23
  okm_len       : okmLen = 64 ∨ okmLen = 80
  hmac_st       : HmacSt s₀.mem (s₀.readReg64 .x0) F prk []
  info_ptr      : s₀.mem.read64 (s₀.readReg64 .x1) = infoPtr
  info_len      : s₀.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length
  info_bytes    : s₀.mem.readBytes infoPtr info.length = info
  read_x0       : s₀.mem.Readable (s₀.readReg64 .x0) 0x90
  read_x1       : s₀.mem.Readable (s₀.readReg64 .x1) 16
  rw_x2         : RW s₀.mem (s₀.readReg64 .x2) okmLen
  rw_stack      : RW s₀.mem (s₀.sp - 640#64) 640
  disj_x2_stack : DisjointRegions (s₀.readReg64 .x2) okmLen (s₀.sp - 640#64) 640
  disj_x0_stack : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.sp - 640#64) 640
  disj_x0_x2    : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x2) okmLen
  disj_x1_stack : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.sp - 640#64) 640
  disj_x1_x2    : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.readReg64 .x2) okmLen
  out_info_stk  : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.sp - 640#64) 640 a
  out_info_x2   : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.readReg64 .x2) okmLen a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

/-- Common state invariant across cuts of `expand_multi_info`. -/
structure ExpandCommon (okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = esp s₀
  x29_eq : s.readReg64 .x29 = esp s₀ + 400#64
  x27_eq : s.readReg64 .x27 = esp s₀ + 64#64
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x0
  m8_eq  : s.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1
  m16_eq : s.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64
  saved  : ExpandSaved s₀ s.mem
  frame  : ExpandFrame okmLen s₀ s.mem

/-! ## Framing and Disjointness Lemmas -/

theorem Frame.readBytes_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {addr : BitVec 64} {len : ℕ}
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (fun r hr => (hd r hr).outside hin hlen)

theorem Frame.read64_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {addr : BitVec 64}
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := Frame.readBytes_eq hf hd (by decide)
  rw [Bytes.readBytes_8_eq, Bytes.readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

theorem Frame.readable_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (m₂.Readable addr len) (m₁.Readable addr len) :=
  ⟨Memory.Readable.of_perm_eq hf.2.1 hf.2.2.2.1⟩

theorem Frame.rw_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (m₂.RW addr len) (m₁.RW addr len) :=
  ⟨Memory.RW.of_perm_eq hf.2.1 hf.2.2.2.1⟩

def KeepsFrozenNoAnon (m m' : Memory) : Prop :=
  ∀ a, m.Frozen a →
    m'.read8 a = m.read8 a ∧ m'.perm a = m.perm a ∧ (m.isLazyFree a = false → m'.isLazyFree a = false)

theorem KeepsFrozenNoAnon.of_perm_eq {m m' : Memory}
    (hperm : m'.perm = m.perm)
    (hlf : ∀ a, m.isLazyFree a = false → m'.isLazyFree a = false)
    (hread : ∀ a, m.Frozen a → m'.read8 a = m.read8 a) :
    KeepsFrozenNoAnon m m' := by
  intro a hf
  exact ⟨hread a hf, congrFun hperm a, hlf a⟩

theorem Program.CodeLoaded.of_keepsFrozenNoAnon {P : Program} {m m' : Memory}
    (hcl : P.CodeLoaded m) (hk : KeepsFrozenNoAnon m m') :
    P.CodeLoaded m' := by
  rw [Program.codeLoaded_iff] at hcl ⊢
  refine ⟨hcl.1, hcl.2.1, fun i hi => ?_⟩
  rcases hcl.2.2 i hi with ⟨hb, hp, hlf⟩
  have hf : m.Frozen (P.base + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  rcases hk (P.base + BitVec.ofNat 64 i) hf with ⟨hb', hp', hlf'⟩
  exact ⟨hb'.trans hb, hp'.trans hp, hlf' hlf⟩

theorem _root_.CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon
    {pl : Obj.MultiPlacement} {m m' : Memory}
    (hcl : LibsignalCodeLoaded pl m) (hk : KeepsFrozenNoAnon m m') :
    LibsignalCodeLoaded pl m' :=
  fun i hi hunmut ext panics svc => Program.CodeLoaded.of_keepsFrozenNoAnon (hcl i hi hunmut ext panics svc) hk

theorem ExpandFrame.rw_esp {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.RW (esp s₀) 496 := by
  have hrw : m.RW (s₀.sp - 640#64) 640 := (Frame.rw_iff hf _ _).mpr hpre.rw_stack
  unfold esp
  exact hrw.sub (by bv_omega)

theorem ExpandFrame.rw_x2 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.RW (s₀.readReg64 .x2) okmLen :=
  (Frame.rw_iff hf _ _).mpr hpre.rw_x2

theorem ExpandFrame.readable_x0 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.Readable (s₀.readReg64 .x0) 0x90 :=
  (Frame.readable_iff hf _ _).mpr hpre.read_x0

theorem ExpandFrame.readable_x1 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.Readable (s₀.readReg64 .x1) 16 :=
  (Frame.readable_iff hf _ _).mpr hpre.read_x1

theorem ExpandFrame.hmac_x0 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    HmacSt m (s₀.readReg64 .x0) F prk [] := by
  have hd : ∀ r ∈ [(s₀.readReg64 .x2, okmLen), (s₀.sp - 640#64, 640)],
      DisjointRegions r.1 r.2 (s₀.readReg64 .x0) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x0_x2.symm
    · exact hpre.disj_x0_stack.symm
  rcases hpre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hf.1 _ (fun r hr => ?_)).trans hpos
    exact (hd r hr).outside (by unfold InRegion; bv_omega) (by decide)
  · refine (Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hin
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x40#64) ⟨by decide, by bv_omega⟩
  · refine (Frame.read64_eq hf (fun r hr => ?_)).trans hcnt1
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x60#64) ⟨by decide, by bv_omega⟩
  · refine (Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hout
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x68#64) ⟨by decide, by bv_omega⟩
  · refine (Frame.read64_eq hf (fun r hr => ?_)).trans hcnt2
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x88#64) ⟨by decide, by bv_omega⟩

theorem ExpandFrame.info_ptr_eq {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.read64 (s₀.readReg64 .x1) = infoPtr := by
  rw [Frame.read64_eq hf]
  · exact hpre.info_ptr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem ExpandFrame.info_len_eq {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length := by
  rw [Frame.read64_eq hf]
  · exact hpre.info_len
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem ExpandFrame.info_bytes_eq {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) (hf : ExpandFrame okmLen s₀ m) :
    m.readBytes infoPtr info.length = info := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < info.length := by simpa using h1
  have hin : InRegion infoPtr info.length (infoPtr + BitVec.ofNat 64 i) :=
    inRegion_base_add infoPtr info.length i hi (by have := hpre.info_lt; omega)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.out_info_x2 _ hin
  · exact hpre.out_info_stk _ hin

theorem ExpandFrame.of_agreesOutside_esp {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrame okmLen s₀ m)
    (hA : AgreesOutside m m' (esp s₀ + off) sz)
    (hoff : off.toNat + sz ≤ 496) :
    ExpandFrame okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := s₀.sp - 640#64) (rlen := 640) (by simp) (by unfold esp; clear * - hoff; bv_omega) hA

theorem ExpandFrame.of_agreesOutside_x2 {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrame okmLen s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : off.toNat + sz ≤ okmLen) :
    ExpandFrame okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := s₀.readReg64 .x2) (rlen := okmLen) (by simp) (by clear * - hoff; bv_omega) hA

theorem ExpandSaved.of_agreesOutside_low {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hs : ExpandSaved s₀ m)
    (hA : AgreesOutside m m' (esp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 400) :
    ExpandSaved s₀ m' := by
  have hread (k : BitVec 64) (hk : 400 ≤ k.toNat ∧ k.toNat + 8 ≤ 496) :
      m'.read64 (esp s₀ + k) = m.read64 (esp s₀ + k) := by
    refine hA.read64_eq ?_
    rcases hoff with ⟨_, _⟩
    rcases hk with ⟨_, _⟩
    unfold DisjointRegions
    bv_omega
  exact
    { m400 := (hread 400#64 (by decide)).trans hs.m400
      m408 := (hread 408#64 (by decide)).trans hs.m408
      m416 := (hread 416#64 (by decide)).trans hs.m416
      m424 := (hread 424#64 (by decide)).trans hs.m424
      m432 := (hread 432#64 (by decide)).trans hs.m432
      m440 := (hread 440#64 (by decide)).trans hs.m440
      m448 := (hread 448#64 (by decide)).trans hs.m448
      m456 := (hread 456#64 (by decide)).trans hs.m456
      m464 := (hread 464#64 (by decide)).trans hs.m464
      m472 := (hread 472#64 (by decide)).trans hs.m472
      m480 := (hread 480#64 (by decide)).trans hs.m480
      m488 := (hread 488#64 (by decide)).trans hs.m488 }

theorem ExpandSaved.of_agreesOutside_x2 {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (hs : ExpandSaved s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) :
    ExpandSaved s₀ m' := by
  have hd_x2_saved : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀ + 400#64) 96 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64 + 400#64) ⟨by decide, by bv_omega⟩
  have hread (k : BitVec 64) (hk : 400 ≤ k.toNat ∧ k.toNat + 8 ≤ 496) :
      m'.read64 (esp s₀ + k) = m.read64 (esp s₀ + k) := by
    refine hA.read64_eq (hd_x2_saved.sub_right (esp s₀ + k) ⟨by decide, ?_⟩)
    rcases hk with ⟨_, _⟩
    bv_omega
  exact
    { m400 := (hread 400#64 (by decide)).trans hs.m400
      m408 := (hread 408#64 (by decide)).trans hs.m408
      m416 := (hread 416#64 (by decide)).trans hs.m416
      m424 := (hread 424#64 (by decide)).trans hs.m424
      m432 := (hread 432#64 (by decide)).trans hs.m432
      m440 := (hread 440#64 (by decide)).trans hs.m440
      m448 := (hread 448#64 (by decide)).trans hs.m448
      m456 := (hread 456#64 (by decide)).trans hs.m456
      m464 := (hread 464#64 (by decide)).trans hs.m464
      m472 := (hread 472#64 (by decide)).trans hs.m472
      m480 := (hread 480#64 (by decide)).trans hs.m480
      m488 := (hread 488#64 (by decide)).trans hs.m488 }

theorem read64_x0_write64_esp {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) :
    (∀ (m : Memory) (off v : BitVec 64),
      decide (off.toNat + 8 ≤ 496) = true →
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0) = m.read64 (s₀.readReg64 .x0)) ∧
    (∀ (m : Memory) (off a_off v : BitVec 64),
      decide (off.toNat + 8 ≤ 496) = true →
      decide (a_off.toNat + 8 ≤ 144) = true →
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0 + a_off) =
        m.read64 (s₀.readReg64 .x0 + a_off)) := by
  refine ⟨fun m off v hoff => ?_, fun m off a_off v hoff ha => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 8 :=
      h1.sub_right (s₀.readReg64 .x0) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have ha' : a_off.toNat + 8 ≤ 144 := of_decide_eq_true ha
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0 + a_off) 8 :=
      h1.sub_right (s₀.readReg64 .x0 + a_off) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd

theorem read64_x1_write_esp {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀) :
    (∀ (m : Memory) (off v : BitVec 64),
      decide (off.toNat + 8 ≤ 496) = true →
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off v : BitVec 64),
      decide (off.toNat + 8 ≤ 496) = true →
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8),
      decide (off.toNat < 496) = true →
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8),
      decide (off.toNat < 496) = true →
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) := by
  refine ⟨fun m off v hoff => ?_, fun m off v hoff => ?_, fun m off v hoff => ?_, fun m off v hoff => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd

/-! ## `HmacSt` Transfer Lemmas -/

theorem writeBytes_readBytes_disj (m : Memory) (a₁ : BitVec 64) (bs : List (BitVec 8))
    (a₂ : BitVec 64) (n : ℕ)
    (hd : 0 < bs.length → 0 < n → DisjointRegions a₁ bs.length a₂ n)
    (hn : n ≤ 2 ^ 64 := by decide) :
    (m.writeBytes a₁ bs).readBytes a₂ n = m.readBytes a₂ n := by
  rcases bs with _ | ⟨b0, tl⟩
  · rfl
  · by_cases hn0 : n = 0
    · subst hn0; rfl
    · exact (ProofLib.AgreesOutside.writeBytes_self m a₁ (b0 :: tl)).readBytes_eq
        (hd (by simp) (by omega)) hn

theorem writeBytes_read64_disj (m : Memory) (a₁ : BitVec 64) (bs : List (BitVec 8))
    (a₂ : BitVec 64)
    (hd : 0 < bs.length → DisjointRegions a₁ bs.length a₂ 8) :
    (m.writeBytes a₁ bs).read64 a₂ = m.read64 a₂ := by
  rcases bs with _ | ⟨b0, tl⟩
  · rfl
  · exact (ProofLib.AgreesOutside.writeBytes_self m a₁ (b0 :: tl)).read64_eq
      (hd (by simp))

/-- Updating an `HmacSt m₀ a F key pmsg` (with `pmsg.length ≤ 32`) by `memcpy`ing `info`
(`info.length < 23`) at `a + pmsg.length` and writing counter byte `c` at
`a + pmsg.length + info.length` and new cursor `pmsg.length + info.length + 1` at `a + 63`
(plus scratch writes at `a + 63` and `a + 176`). -/
theorem HmacSt.of_memcpy_counter {m₀ : Memory} {a : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pmsg info : List (BitVec 8)}
    {b1 c : BitVec 8}
    (h₀ : HmacSt m₀ a F key pmsg)
    (hp : pmsg.length ≤ 32)
    (hinfo : info.length < 23) :
    let m₁ := m₀.writeBytes (a + BitVec.ofNat 64 pmsg.length) info
    let m₂ := (((m₁.write8 (a + 63#64) b1).write8 (a + 176#64) c).write8
      (a + BitVec.ofNat 64 (pmsg.length + info.length)) c).write8
      (a + 63#64) (BitVec.ofNat 8 (pmsg.length + info.length + 1))
    HmacSt m₂ a F key (pmsg ++ info ++ [c]) := by
  intro m₁ m₂
  rcases h₀ with ⟨_, hpmsg, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (pmsg ++ info ++ [c]).length = pmsg.length + info.length + 1 := by
    simp; omega
  have hag_w : AgreesOutside m₁ m₂ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen,
        Bytes.readBytes_add m₂ a (pmsg.length + info.length) 1,
        Bytes.readBytes_add m₂ a pmsg.length info.length]
    have h_pmsg : m₂.readBytes a pmsg.length = pmsg := by
      by_cases hp0 : pmsg.length = 0
      · simp [hp0] at hpmsg ⊢; exact hpmsg
      · have hd2 : DisjointRegions (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177 a pmsg.length := by
          unfold DisjointRegions; bv_omega
        rw [hag_w.readBytes_eq hd2 (by omega)]
        dsimp only [m₁]
        rw [writeBytes_readBytes_disj m₀ _ info a pmsg.length
              (fun _ _ => by unfold DisjointRegions; bv_omega) (by omega),
            hpmsg]
    have h_info : m₂.readBytes (a + BitVec.ofNat 64 pmsg.length) info.length = info := by
      by_cases hi0 : info.length = 0
      · have hnil : info = [] := List.eq_nil_of_length_eq_zero hi0
        subst hnil; rfl
      · have hd2 : DisjointRegions (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177
            (a + BitVec.ofNat 64 pmsg.length) info.length := by
          unfold DisjointRegions; bv_omega
        rw [hag_w.readBytes_eq hd2 (by omega)]
        dsimp only [m₁]
        exact Bytes.readBytes_writeBytes_same m₀ _ info (by omega)
    have h_c : m₂.readBytes (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_pmsg, h_info, h_c, List.append_assoc]
  · rw [hlen, show (0x3f#64 : BitVec 64) = 63#64 from rfl]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ),
        0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
        m₂.readBytes (a + off) sz = m₀.readBytes (a + off) sz := by
      intro off sz hsz0 h64 h144
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          writeBytes_readBytes_disj m₀ _ info (a + off) sz
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by omega)]
    exact (h_ag_st 0x40#64 32 (by decide) (by decide) (by decide)).trans hin
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x60#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt1]
  · have h_ag_out : m₂.readBytes (a + 0x68#64) 32 = m₀.readBytes (a + 0x68#64) 32 := by
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          writeBytes_readBytes_disj m₀ _ info (a + 0x68#64) 32
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag_out.trans hout
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x88#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt2]

/-- Writing a 32-byte block `t` (4 words from `t_addr`) at `a` and setting `pos = 32` at `a + 63`
in an empty `HmacSt m₀ a F key []` produces `HmacSt m a F key t`. -/
theorem HmacSt.of_write32_empty {m₀ m : Memory} {a t_addr : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key t : List (BitVec 8)}
    (htmpl : HmacSt m₀ a F key [])
    (ht : m₀.readBytes t_addr 32 = t)
    (ht_len : t.length = 32)
    (h0   : m.read64 a            = m₀.read64 t_addr)
    (h8   : m.read64 (a + 8#64)   = m₀.read64 (t_addr + 8#64))
    (h16  : m.read64 (a + 16#64)  = m₀.read64 (t_addr + 16#64))
    (h24  : m.read64 (a + 24#64)  = m₀.read64 (t_addr + 24#64))
    (hpos : m.read8  (a + 63#64)  = 32#8)
    (h64  : m.read64 (a + 64#64)  = m₀.read64 (a + 64#64))
    (h72  : m.read64 (a + 72#64)  = m₀.read64 (a + 72#64))
    (h80  : m.read64 (a + 80#64)  = m₀.read64 (a + 80#64))
    (h88  : m.read64 (a + 88#64)  = m₀.read64 (a + 88#64))
    (h96  : m.read64 (a + 96#64)  = m₀.read64 (a + 96#64))
    (h104 : m.read64 (a + 104#64) = m₀.read64 (a + 104#64))
    (h112 : m.read64 (a + 112#64) = m₀.read64 (a + 112#64))
    (h120 : m.read64 (a + 120#64) = m₀.read64 (a + 120#64))
    (h128 : m.read64 (a + 128#64) = m₀.read64 (a + 128#64))
    (h136 : m.read64 (a + 136#64) = m₀.read64 (a + 136#64)) :
    HmacSt m a F key t := by
  rcases htmpl with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht_len, readBytes_32_eq_of_read64_eq h0 h8 h16 h24, ht]
  · rw [ht_len, show (0x3f#64 : BitVec 64) = 63#64 from rfl, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64
          (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80)
          (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104
          (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120)
          (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

/-! ## Cut-Point Predicates -/

theorem cmp_lt64_lemmas {n : ℕ} (h : n < 64) :
    BitVec.ule 64#64 (BitVec.ofNat 64 n) = false ∧
    BitVec.ult (BitVec.ofNat 64 n) 64#64 = true ∧
    (AddWithCarry64 (BitVec.ofNat 64 n) (bv% (2 ^ 64 - 65)) true).2.c = false := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  generalize BitVec.ofNat 64 n = x at hbv ⊢
  have hx : x = (x.truncate 8).zeroExtend 64 := by bv_bits
  have hx8 : x.truncate 8 < 64#8 := by bv_bits
  rw [hx]
  generalize x.truncate 8 = b at hx8 ⊢
  revert b hx8; decide

theorem cmp_lt32_lemmas {n : ℕ} (h : n < 32) :
    BitVec.ule 32#64 (BitVec.ofNat 64 n) = false ∧
    BitVec.ult (BitVec.ofNat 64 n) 32#64 = true ∧
    (AddWithCarry64 (BitVec.ofNat 64 n) (bv% (2 ^ 64 - 33)) true).2.c = false := by
  have hbv : BitVec.ofNat 64 n < 32#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  generalize BitVec.ofNat 64 n = x at hbv ⊢
  have hx : x = (x.truncate 8).zeroExtend 64 := by bv_bits
  have hx8 : x.truncate 8 < 32#8 := by bv_bits
  rw [hx]
  generalize x.truncate 8 = b at hx8 ⊢
  revert b hx8; decide

theorem cmp32_lt63_lemmas {n : ℕ} (h : n < 63) :
    (BitVec.truncate 32 (BitVec.ofNat 64 n) == 63#32) = false ∧
    (BitVec.truncate 32 (BitVec.ofNat 64 n) != 63#32) = true ∧
    (AddWithCarry32 (BitVec.truncate 32 (BitVec.ofNat 64 n)) 4294967232#32 true).2.z = false := by
  have hbv : BitVec.ofNat 64 n < 63#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  generalize BitVec.ofNat 64 n = x at hbv ⊢
  have hx : x = (x.truncate 8).zeroExtend 64 := by bv_bits
  have hx8 : x.truncate 8 < 63#8 := by bv_bits
  rw [hx]
  generalize x.truncate 8 = b at hx8 ⊢
  revert b hx8; decide

theorem zeroExtend64_and255_truncate32_ofNat64 {n : ℕ} (h : n < 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n) &&& 255#32) =
      BitVec.ofNat 64 n := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  revert hbv
  generalize BitVec.ofNat 64 n = x
  intro hbv
  bv_bits

theorem zeroExtend64_add1_truncate32_ofNat64 {n : ℕ} (h : n < 63) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n) + 1#32) =
      BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem zeroExtend64_add32_truncate32_ofNat64 {n : ℕ} (h : n < 32) :
    BitVec.zeroExtend 64 (32#32 + BitVec.truncate 32 (BitVec.ofNat 64 n)) =
      BitVec.ofNat 64 (32 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

@[scoped simp, arm64_norm]
theorem truncate8_ofNat64 (n : ℕ) :
    BitVec.truncate 8 (BitVec.ofNat 64 n) = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem agreesOutside_esp_write64 {m₁ m₂ : Memory} {s₀ : State} {off w_off v : BitVec 64} {sz : ℕ}
    (h : AgreesOutside m₁ m₂ (esp s₀ + off) sz)
    (hw : decide (off.toNat ≤ w_off.toNat ∧ w_off.toNat + 8 ≤ off.toNat + sz ∧ off.toNat + sz ≤ 496) = true) :
    AgreesOutside m₁ (m₂.write64 (esp s₀ + w_off) v) (esp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hw
  exact h.write64 (by bv_omega) (by omega)

theorem agreesOutside_esp_write8 {m₁ m₂ : Memory} {s₀ : State} {off w_off : BitVec 64}
    {v : BitVec 8} {sz : ℕ}
    (h : AgreesOutside m₁ m₂ (esp s₀ + off) sz)
    (hw : decide (off.toNat ≤ w_off.toNat ∧ w_off.toNat + 1 ≤ off.toNat + sz ∧ off.toNat + sz ≤ 496) = true) :
    AgreesOutside m₁ (m₂.write8 (esp s₀ + w_off) v) (esp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hw
  exact h.write8 (by simp only [InRegion]; bv_omega)

theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[scoped simp, arm64_norm]
theorem bv32_zero_add (x : BitVec 32) : 0#32 + x = x := BitVec.zero_add x

@[scoped simp, arm64_norm]
theorem bv8_zero_add (x : BitVec 8) : 0#8 + x = x := BitVec.zero_add x

theorem and64_255_ofNat64 {n : ℕ} (h : n < 64) :
    BitVec.ofNat 64 n &&& 255#64 = BitVec.ofNat 64 n := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  revert hbv; generalize BitVec.ofNat 64 n = x; intro hbv; bv_bits

theorem and_0xffffffffff_ofNat64 {n : ℕ} (h : n < 64) :
    BitVec.ofNat 64 n &&& 1095216660735#64 = BitVec.ofNat 64 n := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  revert hbv; generalize BitVec.ofNat 64 n = x; intro hbv; bv_bits

theorem zeroExtend32_ofNat8_eq_truncate32 {n : ℕ} (h : n < 64) :
    BitVec.zeroExtend 32 (BitVec.ofNat 8 n) = BitVec.truncate 32 (BitVec.ofNat 64 n) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem zeroExtend64_ofNat8 {n : ℕ} (h : n < 64) :
    BitVec.zeroExtend 64 (BitVec.ofNat 8 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp; omega

macro "prove_agrees_esp" : tactic =>
  `(tactic| (
    repeat' rw [mem_setMem]
    repeat' (first
      | ((with_reducible refine agreesOutside_esp_write64 ?_ ?hw); case hw => decide)
      | ((with_reducible refine AgreesOutside.write8 ?_ ?hw); case hw => (simp only [InRegion]; bv_omega)))
    exact AgreesOutside.rfl' _ _ _))

theorem readBytes_eq_of_agreesOutside_esp (s₀ : State) (m : Memory) {m' : Memory}
    (off : BitVec 64) (sz : ℕ) {addr : BitVec 64} {len : ℕ} {rhs : List (BitVec 8)}
    (hd : DisjointRegions (esp s₀ + off) sz addr len)
    (hA : AgreesOutside m m' (esp s₀ + off) sz)
    (hlen : len ≤ 2 ^ 64)
    (hrhs : m.readBytes addr len = rhs) :
    m'.readBytes addr len = rhs :=
  (hA.readBytes_eq hd hlen).trans hrhs

theorem agreesOutside_writeBytes_le (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (sz : ℕ) (hle : bs.length ≤ sz) :
    AgreesOutside m (m.writeBytes addr bs) addr sz :=
  (ProofLib.AgreesOutside.writeBytes_self m addr bs).mono hle

theorem ExpandCommon.of_agreesOutside_low32 {okmLen : ℕ} {s₀ s s' : State}
    {off : BitVec 64} {sz : ℕ}
    (hc : ExpandCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (esp s₀ + off) sz)
    (hoff  : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400) = true) :
    ExpandCommon okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ : 32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400 := of_decide_eq_true hoff
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_low hc.saved hA ⟨h2, h3⟩,
    ExpandFrame.of_agreesOutside_esp hc.frame hA (by omega)⟩

theorem ExpandCommon.of_agreesOutside_x2 {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s s' : State}
    {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (hc : ExpandCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (s₀.readReg64 .x2 + off) sz)
    (hoff  : 0 < sz ∧ off.toNat + sz ≤ okmLen) :
    ExpandCommon okmLen s₀ s' := by
  have hd_x2_esp : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀) 32 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64) ⟨by decide, by bv_omega⟩
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_x2 hpre hc.saved hA hoff,
    ExpandFrame.of_agreesOutside_x2 hc.frame hA hoff.2⟩

/-- Cut `X0p` at `b + 0x1a894` (after 8-step prologue). -/
structure StateX0p (b : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 32)
  status : s.status = .Running
  sp_eq  : s.sp = esp s₀
  x29_eq : s.readReg64 .x29 = esp s₀ + 400#64
  x0_eq  : s.readReg64 .x0 = s₀.readReg64 .x0
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq  : s.readReg64 .x2 = s₀.readReg64 .x2
  x3_eq  : s.readReg64 .x3 = BitVec.ofNat 64 okmLen
  saved  : ExpandSaved s₀ s.mem
  frame  : ExpandFrame okmLen s₀ s.mem

/-- Cut `X1` at `b + 0x47f50` (`memcpy` #1 stub, reached after 40 steps from `X0p`). -/
structure StateX1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 192)
  x0_eq   : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x19_eq  : s.readReg64 .x19 = 0#64
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 okmLen
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 info.length
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk []

/-- Cut `X1b` at `b + 0x1aa34` (after `memcpy` #1 and 13 steps appending `1#8`). -/
structure StateX1b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 448)
  common  : ExpandCommon okmLen s₀ s
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq  : s.readReg64 .x23 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk (info ++ [1#8])

/-- Cut `X2` at `b + 0x30680` (`finalize_fixed` #1 entry, reached after 13 steps from `X1b`). -/
structure StateX2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  common   : ExpandCommon okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 500)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  hmac_240 : HmacSt s.mem (esp s₀ + 240#64) F prk (info ++ [1#8])

/-- Cut `X2r` at `b + 0x1aa68` (after `finalize_fixed` #1 returns). -/
structure StateX2r (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 500)
  common : ExpandCommon okmLen s₀ s
  x22_eq : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq : s.readReg64 .x23 = 32#64
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  t1_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = t1 F prk info

/-- Loop header cut at `b + 0x1ab3c` for iteration `i ∈ {1, 2}`:
- `tPrev` (32 B) is cached at `esp s₀ + 32#64`
- `okmSoFar` (`dstOff` bytes) is written at `s₀.readReg64 .x2`
- `rem = okmLen - dstOff` bytes remain (`x26 = BitVec.ofNat 64 rem`). -/
structure StateLoop (b : BitVec 64) (okmLen : ℕ)
    (tPrev okmSoFar : List (BitVec 8)) (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 712)
  common  : ExpandCommon okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  t_cache : s.mem.readBytes (esp s₀ + 32#64) 32 = tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Epilogue entry cut at `b + 0x1ad0c`: all `okmLen` bytes of `hkdfExpand F prk info okmLen`
have been written to `s₀.readReg64 .x2`. -/
structure StateDone (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1176)
  common  : ExpandCommon okmLen s₀ s
  okm_all : s.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen

/-- Postcondition of `expand_multi_info` at return (`s'.pc = s₀.readReg64 .lr`). -/
def ExpandPost (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s' : State) : Prop :=
  s'.pc = s₀.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s₀ s' ∧
  s'.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen ∧
  ExpandFrame okmLen s₀ s'.mem

/-! ## Copy and `finalize_fixed` Frame Helpers -/

theorem read64_add_off_left {m : Memory} {a b₁ c d rhs : BitVec 64}
    (h : m.read64 (a + d) = rhs) (h1 : b₁ + c = d := by rfl) :
    m.read64 (a + b₁ + c) = rhs := by
  rw [BitVec.add_assoc, h1]; exact h

theorem read64_add_off {m m₀ : Memory} {a b₁ b₂ c d₁ d₂ : BitVec 64}
    (h : m.read64 (a + d₁) = m₀.read64 (a + d₂))
    (h1 : b₁ + c = d₁ := by rfl) (h2 : b₂ + c = d₂ := by rfl) :
    m.read64 (a + b₁ + c) = m₀.read64 (a + b₂ + c) := by
  rw [BitVec.add_assoc, h1, BitVec.add_assoc, h2]; exact h

theorem HmacSt.of_copy_empty_esp_64 {m₀ m : Memory} {s₀ : State} {src : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (hsrc : HmacSt m₀ src F key [])
    (h56  : m.read64 (esp s₀ + 120#64) = m₀.read64 (src + 56#64))
    (h64  : m.read64 (esp s₀ + 128#64) = m₀.read64 (src + 64#64))
    (h72  : m.read64 (esp s₀ + 136#64) = m₀.read64 (src + 72#64))
    (h80  : m.read64 (esp s₀ + 144#64) = m₀.read64 (src + 80#64))
    (h88  : m.read64 (esp s₀ + 152#64) = m₀.read64 (src + 88#64))
    (h96  : m.read64 (esp s₀ + 160#64) = m₀.read64 (src + 96#64))
    (h104 : m.read64 (esp s₀ + 168#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (esp s₀ + 176#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (esp s₀ + 184#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (esp s₀ + 192#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (esp s₀ + 200#64) = m₀.read64 (src + 136#64)) :
    HmacSt m (esp s₀ + 64#64) F key [] :=
  HmacSt.of_copy_empty hsrc
    (read64_add_off_left h56)
    (read64_add_off_left h64)
    (read64_add_off_left h72)
    (read64_add_off_left h80)
    (read64_add_off_left h88)
    (read64_add_off_left h96)
    (read64_add_off_left h104)
    (read64_add_off_left h112)
    (read64_add_off_left h120)
    (read64_add_off_left h128)
    (read64_add_off_left h136)

theorem HmacSt.of_copy_esp_64_240 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (hsrc : HmacSt m₀ (esp s₀ + 64#64) F key msg)
    (h0   : m.read64 (esp s₀ + 240#64) = m₀.read64 (esp s₀ + 64#64))
    (h8   : m.read64 (esp s₀ + 248#64) = m₀.read64 (esp s₀ + 72#64))
    (h16  : m.read64 (esp s₀ + 256#64) = m₀.read64 (esp s₀ + 80#64))
    (h24  : m.read64 (esp s₀ + 264#64) = m₀.read64 (esp s₀ + 88#64))
    (h32  : m.read64 (esp s₀ + 272#64) = m₀.read64 (esp s₀ + 96#64))
    (h40  : m.read64 (esp s₀ + 280#64) = m₀.read64 (esp s₀ + 104#64))
    (h48  : m.read64 (esp s₀ + 288#64) = m₀.read64 (esp s₀ + 112#64))
    (h56  : m.read64 (esp s₀ + 296#64) = m₀.read64 (esp s₀ + 120#64))
    (h64  : m.read64 (esp s₀ + 304#64) = m₀.read64 (esp s₀ + 128#64))
    (h72  : m.read64 (esp s₀ + 312#64) = m₀.read64 (esp s₀ + 136#64))
    (h80  : m.read64 (esp s₀ + 320#64) = m₀.read64 (esp s₀ + 144#64))
    (h88  : m.read64 (esp s₀ + 328#64) = m₀.read64 (esp s₀ + 152#64))
    (h96  : m.read64 (esp s₀ + 336#64) = m₀.read64 (esp s₀ + 160#64))
    (h104 : m.read64 (esp s₀ + 344#64) = m₀.read64 (esp s₀ + 168#64))
    (h112 : m.read64 (esp s₀ + 352#64) = m₀.read64 (esp s₀ + 176#64))
    (h120 : m.read64 (esp s₀ + 360#64) = m₀.read64 (esp s₀ + 184#64))
    (h128 : m.read64 (esp s₀ + 368#64) = m₀.read64 (esp s₀ + 192#64))
    (h136 : m.read64 (esp s₀ + 376#64) = m₀.read64 (esp s₀ + 200#64)) :
    HmacSt m (esp s₀ + 240#64) F key msg :=
  HmacSt.of_copy_19 hsrc h0
    (read64_add_off h8)
    (read64_add_off h16)
    (read64_add_off h24)
    (read64_add_off h32)
    (read64_add_off h40)
    (read64_add_off h48)
    (read64_add_off h56)
    (read64_add_off h64)
    (read64_add_off h72)
    (read64_add_off h80)
    (read64_add_off h88)
    (read64_add_off h96)
    (read64_add_off h104)
    (read64_add_off h112)
    (read64_add_off h120)
    (read64_add_off h128)
    (read64_add_off h136)

theorem readBytes_32_esp_32_of_208 {m m₀ : Memory} {s₀ : State} {rhs : List (BitVec 8)}
    (hrhs : m₀.readBytes (esp s₀ + 208#64) 32 = rhs)
    (h0  : m.read64 (esp s₀ + 32#64) = m₀.read64 (esp s₀ + 208#64))
    (h8  : m.read64 (esp s₀ + 40#64) = m₀.read64 (esp s₀ + 216#64))
    (h16 : m.read64 (esp s₀ + 48#64) = m₀.read64 (esp s₀ + 224#64))
    (h24 : m.read64 (esp s₀ + 56#64) = m₀.read64 (esp s₀ + 232#64)) :
    m.readBytes (esp s₀ + 32#64) 32 = rhs := by
  rw [readBytes_32_eq_of_read64_eq h0
        (read64_add_off h8)
        (read64_add_off h16)
        (read64_add_off h24),
      hrhs]

theorem fin_side_conditions {b : BitVec 64} {C : Crypto}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hf : ExpandFrame okmLen s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧
    RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 144#64) 144 := by
  have hrw_stack : s.mem.RW (s₀.sp - 640#64) 640 :=
    (Frame.rw_iff hf _ _).mpr hpre.rw_stack
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega),
    by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega⟩

theorem ExpandSaved.of_fin_frame {s₀ : State} {m m' : Memory}
    (hs : ExpandSaved s₀ m)
    (hfr : Frame m m' [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)]) :
    ExpandSaved s₀ m' := by
  have hd_saved : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496) = true →
      m'.read64 (esp s₀ + off) = m.read64 (esp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine Frame.read64_eq hfr ?_
    intro r hr
    exact (hd_saved r hr).sub_right (esp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact
    { m400 := (h_saved_eq 400#64 (by decide)).trans h0
      m408 := (h_saved_eq 408#64 (by decide)).trans h1
      m416 := (h_saved_eq 416#64 (by decide)).trans h2
      m424 := (h_saved_eq 424#64 (by decide)).trans h3
      m432 := (h_saved_eq 432#64 (by decide)).trans h4
      m440 := (h_saved_eq 440#64 (by decide)).trans h5
      m448 := (h_saved_eq 448#64 (by decide)).trans h6
      m456 := (h_saved_eq 456#64 (by decide)).trans h7
      m464 := (h_saved_eq 464#64 (by decide)).trans h8
      m472 := (h_saved_eq 472#64 (by decide)).trans h9
      m480 := (h_saved_eq 480#64 (by decide)).trans h10
      m488 := (h_saved_eq 488#64 (by decide)).trans h11 }

theorem ExpandFrame.of_fin_frame {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    (hf : ExpandFrame okmLen s₀ m)
    (hfr : Frame m m' [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)]) :
    ExpandFrame okmLen s₀ m' := by
  refine Frame.trans hf (Frame.mono hfr ?_)
  intro a ha r hr
  have hstack := ha (s₀.sp - 640#64, 640) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion esp at *; bv_omega)

theorem ExpandCommon.of_fin_frame {okmLen : ℕ} {s₀ s s' : State}
    (hc : ExpandCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : Frame s.mem s'.mem [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)]) :
    ExpandCommon okmLen s₀ s' := by
  have hd_low : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [Frame.read64_eq hfr (fun r hr => (hd_low r hr).sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [Frame.read64_eq hfr (fun r hr => (hd_low r hr).sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact
    ⟨hstat,
     hcs.sp_eq.trans hc.sp_eq,
     (CalleeSaved.x29 hcs).trans hc.x29_eq,
     (CalleeSaved.x27 hcs).trans hc.x27_eq,
     (CalleeSaved.x20 hcs).trans hc.x20_eq,
     hm8, hm16,
     ExpandSaved.of_fin_frame hc.saved hfr,
     ExpandFrame.of_fin_frame hc.frame hfr⟩

/-- Relocatable cut `X1` at `lsρ lsMemcpySym` (`memcpy` #1 stub, reached after 40 steps from `X0p`). -/
structure StateX1Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = lsρ lsMemcpySym
  common  : ExpandCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = (blkPl_53).base + 192#64
  x0_eq   : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x19_eq  : s.readReg64 .x19 = 0#64
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 okmLen
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 info.length
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk []

/-- Relocatable cut `X2` at `(blkPl_123).base` (`finalize_fixed` #1 entry, reached after 13 steps from `X1b`). -/
structure StateX2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = (blkPl_123).base
  common   : ExpandCommon okmLen s₀ s
  lr_eq    : s.readReg64 .lr = (blkPl_53).base + 500#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  hmac_240 : HmacSt s.mem (esp s₀ + 240#64) F prk (info ++ [1#8])

end Expand
end CryptoVerification.LibsignalTripleRatchet
