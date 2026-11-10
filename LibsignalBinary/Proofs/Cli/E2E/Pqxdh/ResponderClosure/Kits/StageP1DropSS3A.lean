/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp

/-!
# `drop_session_structure3` Separation-Logic Helpers — Part A

Separation-logic decomposition and initial basic-block segment lemmas (`+16 → +100`) for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#5]` (344-byte
`SessionStructure` teardown).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.DropSS3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev dropSessionStructure3Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"

gen_decodes libsignalSessionCode_tree dropSs3BinCliKits [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" + 0) → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" + 272)]

theorem stackAt_split_bottom' (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem dealloc_hookSat_tripleRatchetExterns {A : RustAlloc} (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
    CryptoVerification.LibsignalSession.sessionExterns, dhName, pubFromSecretName,
    staticDropName, sharedDropName, rngFillName, uuidTryParseName,
    varintSlowName, noHookNames] using hA.dealloc

theorem dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (dealloc_hookSat_tripleRatchetExterns C ctl hA)

theorem seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## Separation-logic deallocation helpers for `SessionStructure` (344 bytes) -/

def vecPinDealloc (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

def sgnPinDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

theorem vecU8At_entails_pin_dealloc (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro _
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (pointsTo64_entails_memRegion _ _)))

theorem vecGhostAt_entails_pin_dealloc (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_dealloc A a ⟨g.cap, g.ptr⟩ g.bytes

theorem header_cells_entails_memRegion_24 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl
        (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem header_cells_entails_memRegion_32 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16) ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl
        (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem header_cells_entails_memRegion_48 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl
        (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem optTailVecAt_entails_dealloc (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDealloc A cap ptr := by
  cases opt with
  | none =>
    unfold optTailVecAt sgnPinDealloc
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit,
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        ProofLib.memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some g =>
    unfold optTailVecAt sgnPinDealloc
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      exact Entails.refl _
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
          memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit,
          ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail
      rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by
      ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

/-- Proves that a non-negative 64-bit capacity satisfies
`cap + 1#64 ≠ 0#64`. -/
theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have h0 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add] at h0
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hlt : cap.toNat + 1 < 2 ^ 64 := by omega
  rw [h1, Nat.mod_eq_of_lt hlt] at h0
  omega

theorem sender_none_entails_memRegion_104 (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96) ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

def srkRest (A : RustAlloc) (a : BitVec 64) (g : VecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_eq_srkRest (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ srkRest A a g := by
  unfold vecGhostAt vecU8At vecHeader srkRest
  ac_rfl

theorem optSenderChainAt_some_expose (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ⌜PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey ∧
        g.srk.bytes.length ≤ g.srk.cap.toNat ∧ g.srk.cap.toNat < 2 ^ 63 ∧ g.srk.ptr ≠ 0 ∧
        g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ srkRest A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨hpk, _, _, _⟩
  rw [vecGhostAt_eq_srkRest A g.srk a, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr_ne⟩
  refine Entails.pure_right ⟨hpk, hlen, hcap_lt, hptr_ne, cap_add_one_ne_zero hcap_lt⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem chainAt_of_exposed_sender (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain)
    (hpk : PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey)
    (hlen : g.srk.bytes.length ≤ g.srk.cap.toNat)
    (hcap_lt : g.srk.cap.toNat < 2 ^ 63)
    (hptr_ne : g.srk.ptr ≠ 0) :
    (a ↦₆₄ g.srk.cap) ∗ srkRest A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) ⊢
    protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
      ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a := by
  unfold protoChainAt
  dsimp only [List.length_nil, List.zip_nil_left]
  refine Entails.pure_right ⟨hpk, by decide, rfl⟩ ?_
  rw [vecGhostAt_eq_srkRest A g.srk a, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem sessionTail_entails_memRegion_16 (ss : BitVec 64)
    (v1 v2 : BitVec 32) (regIds : List (BitVec 8)) (hreg : regIds.length = 8) :
    ((ss + 0x148#64) ↦₃₂ v1) ∗ ((ss + 0x14c#64) ↦₃₂ v2) ∗ ((ss + 0x150#64) ↦ₛ regIds) ⊢
      memRegion (ss + 328#64) 16 := by
  rw [ProofLib.memRegion_split' (b := ss + 328#64) (n := 4) (k := 12)
        (b' := ss + 332#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 332#64) (n := 4) (k := 8)
        (b' := ss + 336#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) ?_)
  have hb := pointsToBytes_entails_memRegion (ss + 336#64) regIds
  rwa [hreg] at hb

theorem session_memRegions_entails_344 (ss : BitVec 64) :
    memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
      memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 120#64) 24 ∗
      memRegion (ss + 144#64) 104 ∗ memRegion (ss + 248#64) 48 ∗
      memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16 ⊢
      memRegion ss 344 := by
  rw [ProofLib.memRegion_split' (b := ss) (n := 24) (k := 320) (b' := ss + 24#64) rfl rfl
    (by decide),
      ProofLib.memRegion_split' (b := ss + 24#64) (n := 24) (k := 296) (b' := ss + 48#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 48#64) (n := 24) (k := 272) (b' := ss + 72#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 72#64) (n := 24) (k := 248) (b' := ss + 96#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 96#64) (n := 24) (k := 224) (b' := ss + 120#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 120#64) (n := 24) (k := 200) (b' := ss + 144#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 104) (k := 96) (b' := ss + 248#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 248#64) (n := 48) (k := 48) (b' := ss + 296#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 296#64) (n := 32) (k := 16) (b' := ss + 328#64) rfl
        (by bv_omega) (by decide)]
  exact Entails.refl _

@[reducible]
def ssFirst3HeadersAt (ss : BitVec 64) (G : SessionGhost) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
  ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8 ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8

theorem ssFirst3_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    vecGhostAt A G.localIk ss ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ⊢
    ssFirst3HeadersAt ss G ∗
      vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root := by
  have h1 := vecGhostAt_entails_pin_dealloc A G.localIk ss
  have h2 := vecGhostAt_entails_pin_dealloc A G.remoteIk (ss + 24#64)
  have h3 := vecU8At_entails_pin_dealloc A (ss + 48#64) G.root (keyToBytes32 st.rootKey)
  have ha1 : (ss + 24#64) + 8#64 = ss + 32#64 := by bv_omega
  have ha2 : (ss + 24#64) + 16#64 = ss + 40#64 := by bv_omega
  have hb1 : (ss + 48#64) + 8#64 = ss + 56#64 := by bv_omega
  have hb2 : (ss + 48#64) + 16#64 = ss + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  unfold ssFirst3HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem ssFirst3HeadersAt_entails_memRegions (ss : BitVec 64) (G : SessionGhost) :
    ssFirst3HeadersAt ss G ⊢
      memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 := by
  unfold ssFirst3HeadersAt
  have h1 := header_cells_entails_memRegion_24 ss G.localIk.cap G.localIk.ptr
  have h2 := header_cells_entails_memRegion_24 (ss + 24#64) G.remoteIk.cap G.remoteIk.ptr
  have h3 := header_cells_entails_memRegion_24 (ss + 48#64) G.root.cap G.root.ptr
  have ha1 : (ss + 24#64) + 8#64 = ss + 32#64 := by bv_omega
  have ha2 : (ss + 24#64) + 16#64 = ss + 40#64 := by bv_omega
  have hb1 : (ss + 48#64) + 8#64 = ss + 56#64 := by bv_omega
  have hb2 : (ss + 48#64) + 16#64 = ss + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  have hgroup :
      ((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
        ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗
          memRegion (ss + 40#64) 8 ∗
        ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8) =
      (((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8) ∗
       (((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗
         memRegion (ss + 40#64) 8) ∗
       (((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
         memRegion (ss + 64#64) 8)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

@[reducible]
def ssTail3HeadersAt (ss : BitVec 64) (pCap pPtr kCap kPtr : BitVec 64)
    (G : SessionGhost) : SepProp :=
  ((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
  ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
  ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8

theorem ssTail3_entails_dealloc (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A pCap pPtr ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_dealloc A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_dealloc A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_dealloc A G.alice (ss + 96#64)
  have ha1 : (ss + 248#64) + 8#64 = ss + 256#64 := by bv_omega
  have ha2 : (ss + 248#64) + 16#64 = ss + 264#64 := by bv_omega
  have hb1 : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_omega
  have hb2 : (ss + 296#64) + 16#64 = ss + 312#64 := by bv_omega
  have hc1 : (ss + 96#64) + 8#64 = ss + 104#64 := by bv_omega
  have hc2 : (ss + 96#64) + 16#64 = ss + 112#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kPtr
  refine Entails.sepExists_right pCap (Entails.sepExists_right pPtr
    (Entails.sepExists_right kCap (Entails.sepExists_right kPtr ?_)))
  unfold ssTail3HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem ssTail3HeadersAt_entails_memRegions (ss : BitVec 64)
    (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) :
    ssTail3HeadersAt ss pCap pPtr kCap kPtr G ⊢
      memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24 := by
  unfold ssTail3HeadersAt
  have h1 := header_cells_entails_memRegion_48 (ss + 248#64) pCap pPtr
  have h2 := header_cells_entails_memRegion_32 (ss + 296#64) kCap kPtr
  have h3 := header_cells_entails_memRegion_24 (ss + 96#64) G.alice.cap G.alice.ptr
  have ha1 : (ss + 248#64) + 8#64 = ss + 256#64 := by bv_omega
  have ha2 : (ss + 248#64) + 16#64 = ss + 264#64 := by bv_omega
  have hb1 : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_omega
  have hb2 : (ss + 296#64) + 16#64 = ss + 312#64 := by bv_omega
  have hc1 : (ss + 96#64) + 8#64 = ss + 104#64 := by bv_omega
  have hc2 : (ss + 96#64) + 16#64 = ss + 112#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  have hgroup :
      (((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
        ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
        ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗
          memRegion (ss + 112#64) 8) =
      ((((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32) ∗
       (((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16) ∗
       (((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗
         memRegion (ss + 112#64) 8)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem sessionStateAt_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
        (ssFirst3HeadersAt ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (ss + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        memRegion (ss + 328#64) 16 := by
  unfold sessionStateAt
  apply Entails.pure_left; rintro ⟨_, _, _, _, hreg, _, _⟩
  have hreord :
      (vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      ((vecGhostAt A G.localIk ss ∗
          vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
          vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey)) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
          optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
          vecGhostAt A G.alice (ss + 0x60#64)) ∗
        vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        (((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          ((ss + 0x150#64) ↦ₛ G.regIds))) := by ac_rfl
  rw [hreord]
  have h1 := ssFirst3_entails_dealloc A ss G st
  have h2 := ssTail3_entails_dealloc A ss G
  have h3 := vecU8At_entails_pin_dealloc A (ss + 120#64) G.pq st.pqRatchetState
  have hpq1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
  have hpq2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
  rw [hpq1, hpq2] at h3
  have h4 := sessionTail_entails_memRegion_16 ss st.sessionVersion st.previousCounter G.regIds hreg
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono h2
      (sepConj_mono h3 h4))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pCap; refine Entails.sepExists_right pCap ?_
  apply Entails.sepExists_elim; intro pPtr; refine Entails.sepExists_right pPtr ?_
  apply Entails.sepExists_elim; intro kCap; refine Entails.sepExists_right kCap ?_
  apply Entails.sepExists_elim; intro kPtr; refine Entails.sepExists_right kPtr ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## Common WP and stack helpers -/

theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

theorem false_elim_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

theorem header24_weaken (v cap ptr : BitVec 64) (Rest : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest ⊢
      memRegion v 24 ∗ Rest := by
  have heq :
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest) =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗ Rest) := by ac_rfl
  rw [heq]
  exact sepConj_mono_left (header_cells_entails_memRegion_24 v cap ptr)

theorem pq_header24_weaken (ss cap ptr : BitVec 64) (Rest : SepProp) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ Rest ⊢
      memRegion (ss + 120#64) 24 ∗ Rest := by
  have h1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
  have h2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
  rw [← h1, ← h2]
  exact header24_weaken (ss + 120#64) cap ptr Rest

theorem drop6_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro x_4; refine Entails.sepExists_right x_4 ?_
  apply Entails.sepExists_elim; intro x_5; refine Entails.sepExists_right x_5 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

/-! ## Callee-saved predicate, stack splits, and first two segments (`+16 -> +100`) -/

@[reducible]
def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem stackAt_ss2_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp dropChainStack 6 (by decide)

theorem stackAt_dropChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropChainStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropChainStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

theorem tail_stack_ss2_96_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom' sp allocHookStack 96 (by decide),
      show allocHookStack + 96 = dropSessionStructureLocal2Stack from rfl,
      ← stackAt_ss2_split sp]

theorem tail_dealloc_ss2_pre_weaken (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 48#64) dropChainStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_ss2_96_from_bottom sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x22 (Entails.sepExists_right x21
        (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 48#64) dropChainStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem fnAddr_dropChain_eq_ss2_add (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name =
      (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64) := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  bv_omega

theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos hpos hlt

theorem ofNat_add_one_beq_one_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos hpos hlt h0

theorem tail_len_mul_lt {α : Type} {x : α} {xs : List α} {k m : Nat}
    (h : (x :: xs).length * k < m) : xs.length * k < m := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega

theorem cons_len_mul {α : Type} (x : α) (xs : List α) (k : Nat) :
    (x :: xs).length * k = k + xs.length * k := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

theorem sep_pull_body (M Arr Pool Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by ac_rfl

theorem sep_push_body (M Arr Pool Stk Frame : SepProp) :
    M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Pool ∗ Stk ∗ (M ∗ Frame) := by ac_rfl

theorem sep_rejoin_loop (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by ac_rfl

theorem vecAt_expose_loop_at_72 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (ss cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (ss + 72#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt elem sz ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * sz) align ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz))) := by
  unfold vecAt vecHeader
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A sz align elem cap ptr xs)) ?_
  have h1 : (ss + 72#64) + 8#64 = ss + 80#64 := by bv_omega
  have h2 : (ss + 72#64) + 16#64 = ss + 88#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_rejoin_vecBuf (A : RustAlloc) (sz align : Nat) (cap ptr : BitVec 64)
    (n : Nat) (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * sz < 2 ^ 63) :
    memRegion ptr (n * sz) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (n * sz)) ((cap.toNat - n) * sz)) ⊢
    (if (cap == 0#64) = true then emp
     else A.live ptr (cap.toNat * sz) align ∗ memRegion ptr (cap.toNat * sz)) := by
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  by_cases hcap : cap = 0
  · subst hcap
    have hn : n = 0 := Nat.eq_zero_of_le_zero hle
    subst hn
    simp only [Nat.zero_mul, memRegion_zero, ↓reduceIte, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hsplit : cap.toNat * sz = n * sz + (cap.toNat - n) * sz := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hle]
    have hbound : n * sz + (cap.toNat - n) * sz ≤ 2 ^ 64 := by omega
    rw [hsplit, ProofLib.memRegion_split ptr (n * sz) ((cap.toNat - n) * sz) hbound]
    have heq :
        memRegion ptr (n * sz) ∗
          (A.live ptr (n * sz + (cap.toNat - n) * sz) align ∗
            memRegion (ptr + BitVec.ofNat 64 (n * sz)) ((cap.toNat - n) * sz)) =
        A.live ptr (n * sz + (cap.toNat - n) * sz) align ∗
          (memRegion ptr (n * sz) ∗
            memRegion (ptr + BitVec.ofNat 64 (n * sz)) ((cap.toNat - n) * sz)) := by
      ac_rfl
    rw [heq]
    exact Entails.refl _

theorem post_loop_weaken_at_72 (A : RustAlloc) (ss cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (Rest : SepProp) :
    ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗ ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion ptr (n * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) ∗
      Rest ⊢
    ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗ memRegion (ss + 88#64) 8 ∗
      (if (cap == 0#64) = true then emp
       else A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
      Rest := by
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono
    (pointsTo64_entails_memRegion _ _) ?_))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (memRegion_rejoin_vecBuf A 104 8 cap ptr n hle hcap_lt)

theorem chains_header24_weaken (ss cap ptr : BitVec 64) (Rest : SepProp) :
    ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗ memRegion (ss + 88#64) 8 ∗ Rest ⊢
      memRegion (ss + 72#64) 24 ∗ Rest := by
  have h1 : (ss + 72#64) + 8#64 = ss + 80#64 := by bv_omega
  have h2 : (ss + 72#64) + 16#64 = ss + 88#64 := by bv_omega
  rw [← h1, ← h2]
  exact header24_weaken (ss + 72#64) cap ptr Rest

set_option maxHeartbeats 2000000 in
theorem drop_ss2_first3 {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 80#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 16 64
  examples_generalize_entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean (mid := entry + 40#64) (P_mid :=
    (ssFirst3HeadersAt ss G ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := entry + 60#64) (P_mid :=
      (ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (tripleRatchetExterns C ctl abs))) (entry + 80#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗ A.pool ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1)
          refine align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

set_option maxHeartbeats 2000000 in
theorem drop_ss2_sender {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 80#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 100#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [dropProtoChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 80 20
  examples_generalize_entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (tripleRatchetExterns C ctl abs))) (entry + 100#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps
        wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104 (ss + 144#64))),
          h.2⟩)
    | some _ =>
      simp only [optSenderChainAt]
      exact false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_expose A
        (ss + 144#64) sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hpk, hlen, hcap_lt, hptr_ne, hcmn⟩
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_left (chainAt_of_exposed_sender A
          (ss + 144#64) sg sc hpk hlen hcap_lt hptr_ne)) ?_
      wp_call hdrop_chain ⟨ss + 144#64, (⟨sg.srk, sg.priv, sg.mkCap, sg.mkPtr, [], sg.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)⟩
      refine align_pre (by rw [hsp]) ?_
      wp_done

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.DropSS3
