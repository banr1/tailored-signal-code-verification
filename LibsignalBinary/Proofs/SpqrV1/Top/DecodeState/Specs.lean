/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Repr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Fetch

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`) — Relocation & Specifications

**Checked by Lean.**

Defines `Relocatable` spatial combinators across `memcpy` and `grow_one`, capacity-bounded
(`CapOk`) protobuf state predicates, callee specifications, and the top-level specification
`decodeStateSpecX`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `Relocatable` Combinators for `memcpy` and `grow_one` -/

/-- `Relocatable F n H` states that for any base address `a`, the spatial predicate `F a`
    factors into an `n`-byte contiguous byte array `a ↦ₛ bs` and an address-independent
    resource `H bs`, and can be reassembled at any new base address `a'` from `(a' ↦ₛ bs) ∗ H bs`. -/
structure Relocatable (F : BitVec 64 → SepProp) (n : Nat) (H : List (BitVec 8) → SepProp) : Prop where
  to_bytes : ∀ a, F a ⊢ ∃∗ bs, ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) ∗ H bs
  of_bytes : ∀ a bs, bs.length = n → (a ↦ₛ bs) ∗ H bs ⊢ F a

theorem reloc_of_iff {F1 F2 : BitVec 64 → SepProp} {n : Nat} {H : List (BitVec 8) → SepProp}
    (h1 : Relocatable F1 n H)
    (hto : ∀ a, F2 a ⊢ F1 a) (hof : ∀ a, F1 a ⊢ F2 a) :
    Relocatable F2 n H where
  to_bytes a := Entails.trans (hto a) (h1.to_bytes a)
  of_bytes a bs hlen := Entails.trans (h1.of_bytes a bs hlen) (hof a)

theorem reloc_congr {F1 F2 : BitVec 64 → SepProp} {n : Nat} {H : List (BitVec 8) → SepProp}
    (h1 : Relocatable F1 n H) (heq : ∀ a, F1 a = F2 a) : Relocatable F2 n H :=
  reloc_of_iff h1 (fun a => Entails.of_eq (heq a).symm) (fun a => Entails.of_eq (heq a))

theorem reloc_emp : Relocatable (fun _ => emp) 0 (fun _ => emp) where
  to_bytes a := by
    refine Entails.sepExists_right [] ?_
    rw [pointsToBytes_nil]
    apply Entails.pure_right rfl
    rw [sepConj_emp]
    exact Entails.refl _
  of_bytes a bs hlen := by
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hbs
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _

theorem reloc_memRegion (n : Nat) (hn : n ≤ 2 ^ 64) :
    Relocatable (fun a => memRegion a n) n (fun _ => emp) where
  to_bytes a := by
    rw [memRegion_eq_exists_bytes a n hn]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    rw [sepConj_emp]
    exact Entails.refl _
  of_bytes a bs hlen := by
    rw [sepConj_emp, ← hlen]
    exact pointsToBytes_entails_memRegion a bs

theorem reloc_pointsTo64 (w : BitVec 64) :
    Relocatable (fun a => a ↦₆₄ w) 8 (fun bs => ⌜bs = unpack64 w⌝) where
  to_bytes a := by
    rw [pointsTo64_eq_pointsToBytes]
    refine Entails.sepExists_right (unpack64 w) ?_
    apply Entails.pure_right (rfl : (unpack64 w).length = 8)
    rw [sepConj_comm]
    apply Entails.pure_right rfl
    exact Entails.refl _
  of_bytes a bs _ := by
    rw [sepConj_comm]
    apply Entails.pure_left; intro hbs
    subst hbs
    rw [← pointsTo64_eq_pointsToBytes]
    exact Entails.refl _

theorem reloc_pointsTo32 (w : BitVec 32) :
    Relocatable (fun a => a ↦₃₂ w) 4 (fun bs => ⌜bs = unpack32 w⌝) where
  to_bytes a := by
    rw [pointsTo32_eq_pointsToBytes]
    refine Entails.sepExists_right (unpack32 w) ?_
    apply Entails.pure_right (rfl : (unpack32 w).length = 4)
    rw [sepConj_comm]
    apply Entails.pure_right rfl
    exact Entails.refl _
  of_bytes a bs _ := by
    rw [sepConj_comm]
    apply Entails.pure_left; intro hbs
    subst hbs
    rw [← pointsTo32_eq_pointsToBytes]
    exact Entails.refl _

theorem reloc_sepConj_const {F : BitVec 64 → SepProp} {n : Nat} {H : List (BitVec 8) → SepProp}
    (hF : Relocatable F n H) (P : SepProp) :
    Relocatable (fun a => F a ∗ P) n (fun bs => H bs ∗ P) where
  to_bytes a := by
    refine Entails.trans (sepConj_mono_left (hF.to_bytes a)) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    exact Entails.of_eq (by ac_rfl)
  of_bytes a bs hlen := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (hF.of_bytes a bs hlen)

theorem reloc_const_sepConj {F : BitVec 64 → SepProp} {n : Nat} {H : List (BitVec 8) → SepProp}
    (P : SepProp) (hF : Relocatable F n H) :
    Relocatable (fun a => P ∗ F a) n (fun bs => P ∗ H bs) where
  to_bytes a := by
    refine Entails.trans (sepConj_mono_right (hF.to_bytes a)) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    exact Entails.of_eq (by ac_rfl)
  of_bytes a bs hlen := by
    have h : (a ↦ₛ bs) ∗ (P ∗ H bs) = P ∗ ((a ↦ₛ bs) ∗ H bs) := by ac_rfl
    rw [h]
    exact sepConj_mono_right (hF.of_bytes a bs hlen)

theorem reloc_sepExists {α : Type} {F : α → BitVec 64 → SepProp} {n : Nat}
    {H : α → List (BitVec 8) → SepProp} (hF : ∀ x, Relocatable (F x) n (H x)) :
    Relocatable (fun a => ∃∗ x, F x a) n (fun bs => ∃∗ x, H x bs) where
  to_bytes a := by
    apply Entails.sepExists_elim; intro x
    refine Entails.trans ((hF x).to_bytes a) ?_
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    exact sepConj_mono_right (sepConj_mono_right (Entails.sepExists_right x (Entails.refl _)))
  of_bytes a bs hlen := by
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro x
    exact Entails.sepExists_right x ((hF x).of_bytes a bs hlen)

theorem reloc_append {F1 F2 : BitVec 64 → SepProp} {n1 n2 : Nat}
    (n : Nat) (off : BitVec 64)
    {H1 H2 : List (BitVec 8) → SepProp}
    (h1 : Relocatable F1 n1 H1) (h2 : Relocatable F2 n2 H2)
    (hoff : BitVec.ofNat 64 n1 = off) (hn : n1 + n2 = n) :
    Relocatable (fun a => F1 a ∗ F2 (a + off)) n
      (fun bs => H1 (bs.take n1) ∗ H2 (bs.drop n1)) where
  to_bytes a := by
    refine Entails.trans (sepConj_mono (h1.to_bytes a) (h2.to_bytes (a + off))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    apply Entails.sepExists_elim; intro bs1
    have hpull :
        ((⌜bs1.length = n1⌝ ∗ (a ↦ₛ bs1) ∗ H1 bs1) ∗
         ⌜bs2.length = n2⌝ ∗ ((a + off) ↦ₛ bs2) ∗ H2 bs2) =
        ⌜bs1.length = n1⌝ ∗ ⌜bs2.length = n2⌝ ∗
          (((a ↦ₛ bs1) ∗ ((a + off) ↦ₛ bs2)) ∗ H1 bs1 ∗ H2 bs2) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hl1
    apply Entails.pure_left; intro hl2
    refine Entails.sepExists_right (bs1 ++ bs2) ?_
    have hlen : (bs1 ++ bs2).length = n := by rw [List.length_append, hl1, hl2, hn]
    have htake : (bs1 ++ bs2).take n1 = bs1 := by subst hl1; exact List.take_left
    have hdrop : (bs1 ++ bs2).drop n1 = bs2 := by subst hl1; exact List.drop_left
    have hpts : (a ↦ₛ (bs1 ++ bs2)) = (a ↦ₛ bs1) ∗ ((a + off) ↦ₛ bs2) := by
      rw [pointsToBytes_append, hl1, hoff]
    rw [htake, hdrop, hpts]
    apply Entails.pure_right hlen
    exact Entails.of_eq (by ac_rfl)
  of_bytes a bs hlen := by
    have hl1 : (bs.take n1).length = n1 := by simp [hlen]; omega
    have hl2 : (bs.drop n1).length = n2 := by simp [hlen]; omega
    have hbs : bs = bs.take n1 ++ bs.drop n1 := (List.take_append_drop n1 bs).symm
    have hpts : (a ↦ₛ bs) = (a ↦ₛ bs.take n1) ∗ ((a + off) ↦ₛ bs.drop n1) := by
      conv_lhs => rw [hbs]
      rw [pointsToBytes_append, hl1, hoff]
    rw [hpts]
    have harrange :
        (((a ↦ₛ bs.take n1) ∗ ((a + off) ↦ₛ bs.drop n1)) ∗ H1 (bs.take n1) ∗ H2 (bs.drop n1)) =
        ((a ↦ₛ bs.take n1) ∗ H1 (bs.take n1)) ∗ (((a + off) ↦ₛ bs.drop n1) ∗ H2 (bs.drop n1)) := by
      ac_rfl
    rw [harrange]
    exact sepConj_mono (h1.of_bytes a (bs.take n1) hl1) (h2.of_bytes (a + off) (bs.drop n1) hl2)

/-! ### `Relocatable` Instances for `Quads7`, `Quads14`, `Quads28`, and Protobuf Types -/

def relocQuads7 (q : Quads7) :
    Σ' H, Relocatable (fun a => quads7At a q) 56 H :=
  let (w0, w1, w2, w3, w4, w5, w6) := q
  let h1 := reloc_append 16 8#64 (reloc_pointsTo64 w0) (reloc_pointsTo64 w1) rfl rfl
  let h2 := reloc_append 24 16#64 h1 (reloc_pointsTo64 w2) rfl rfl
  let h3 := reloc_append 32 24#64 h2 (reloc_pointsTo64 w3) rfl rfl
  let h4 := reloc_append 40 32#64 h3 (reloc_pointsTo64 w4) rfl rfl
  let h5 := reloc_append 48 40#64 h4 (reloc_pointsTo64 w5) rfl rfl
  let h6 := reloc_append 56 48#64 h5 (reloc_pointsTo64 w6) rfl rfl
  ⟨_, reloc_congr h6 (fun a => by unfold quads7At; dsimp only; ac_rfl)⟩

def relocQuads14 (q : Quads14) :
    Σ' H, Relocatable (fun a => quads14At a q) 112 H :=
  ⟨_, reloc_append 112 56#64 (relocQuads7 q.1).2 (relocQuads7 q.2).2 rfl rfl⟩

def relocQuads28 (q : Quads28) :
    Σ' H, Relocatable (fun a => quads28At a q) 224 H :=
  ⟨_, reloc_append 224 112#64 (relocQuads14 q.1).2 (relocQuads14 q.2).2 rfl rfl⟩

def relocChainEpochPBAt (A : RustAlloc) (ep : ChainEpochPB) :
    Σ' H, Relocatable (fun a => chainEpochPBAt A a ep) 112 H :=
  let hq : ∀ q : Quads14,
      Relocatable (fun a => quads14At a q ∗ chainEpochPBHeap A q ep) 112
        (fun bs => (relocQuads14 q).1 bs ∗ chainEpochPBHeap A q ep) :=
    fun q => reloc_sepConj_const (relocQuads14 q).2 (chainEpochPBHeap A q ep)
  ⟨_, reloc_of_iff (reloc_sepExists hq)
    (fun a => chainEpochPBAt_entails_quads14 A a ep)
    (fun a => by
      apply Entails.sepExists_elim; intro q
      exact quads14_entails_chainEpochPBAt A a q ep)⟩

def relocArrayAtChainEpochPB (A : RustAlloc) :
    ∀ (xs : List ChainEpochPB),
      Σ' H, Relocatable
        (fun a => arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 a xs)
        (xs.length * 112) H
  | [] => ⟨_, reloc_emp⟩
  | x :: xs =>
    let hx := (relocChainEpochPBAt A x).2
    let hxs := (relocArrayAtChainEpochPB A xs).2
    ⟨_, reloc_congr
      (reloc_append ((x :: xs).length * 112) 112#64 hx hxs rfl (by simp [Nat.succ_mul, Nat.add_comm]))
      (fun _ => rfl)⟩

def relocOptProtoInnerStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (opt : Option V1State.InnerState) :
    Σ' H, Relocatable (fun a => optProtoInnerStateAt H_inner A a opt) 224 H :=
  let hq : ∀ q : Quads28,
      Relocatable (fun a => quads28At a q ∗ optProtoInnerStateHeap H_inner A q opt) 224
        (fun bs => (relocQuads28 q).1 bs ∗ optProtoInnerStateHeap H_inner A q opt) :=
    fun q => reloc_sepConj_const (relocQuads28 q).2 (optProtoInnerStateHeap H_inner A q opt)
  ⟨_, reloc_of_iff (reloc_sepExists hq)
    (fun a => optProtoInnerStateAt_entails_quads28 H_inner A a opt)
    (fun a => by
      apply Entails.sepExists_elim; intro q
      exact quads28_entails_optProtoInnerStateAt H_inner A a q opt)⟩

def relocOptProtoPqRatchetInnerAt (H_inner : V1InnerHeapPred) (A : RustAlloc) :
    ∀ (opt : Option PqRatchetState.Inner),
      Σ' H, Relocatable (fun a => optProtoPqRatchetInnerAt H_inner A a opt) 224 H
  | none =>
    ⟨_, reloc_append 224 8#64 (reloc_pointsTo64 none3Cap) (reloc_memRegion 216 (by decide)) rfl rfl⟩
  | some (.v1 v1) => relocOptProtoInnerStateAt H_inner A v1.innerState

def relocVecHeader (cap ptr len : BitVec 64) :
    Σ' H, Relocatable (fun a => vecHeader a cap ptr len) 24 H :=
  let h1 := reloc_append 16 8#64 (reloc_pointsTo64 cap) (reloc_pointsTo64 ptr) rfl rfl
  let h2 := reloc_append 24 16#64 h1 (reloc_pointsTo64 len) rfl rfl
  ⟨_, reloc_congr h2 (fun a => by unfold vecHeader; ac_rfl)⟩

def relocVecU8At (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Σ' H, Relocatable (fun a => vecU8At A a cap ptr bs) 24 H :=
  let h := reloc_sepConj_const (relocVecHeader cap ptr (BitVec.ofNat 64 bs.length)).2 (vecU8Heap A cap ptr bs)
  ⟨_, reloc_congr h (fun a => (vecU8At_eq_header_heap A a cap ptr bs).symm)⟩

def relocRustBytesVecAt (A : RustAlloc) (bs : List (BitVec 8)) :
    Σ' H, Relocatable (fun a => rustBytesVecAt A a bs) 24 H :=
  let h1 : ∀ cap : BitVec 64,
      Σ' H, Relocatable (fun a => ∃∗ ptr : BitVec 64, vecU8At A a cap ptr bs) 24 H :=
    fun cap => ⟨_, reloc_sepExists (fun ptr => (relocVecU8At A cap ptr bs).2)⟩
  ⟨_, reloc_sepExists (fun cap => (h1 cap).2)⟩

def relocVecOf {α : Type} (A : RustAlloc) (stride align : Nat)
    (elemAt : α → BitVec 64 → SepProp) (xs : List α) :
    Σ' H, Relocatable (fun a => vecOf A stride align elemAt a xs) 24 H :=
  let h0 : ∀ cap ptr : BitVec 64,
      Σ' H, Relocatable (fun a => vecAt A stride align elemAt a cap ptr xs) 24 H :=
    fun cap ptr =>
      ⟨_, reloc_sepConj_const (relocVecHeader cap ptr (BitVec.ofNat 64 xs.length)).2
        (vecBuf A stride align elemAt cap ptr xs)⟩
  let h1 : ∀ cap : BitVec 64,
      Σ' H, Relocatable (fun a => ∃∗ ptr : BitVec 64, vecAt A stride align elemAt a cap ptr xs) 24 H :=
    fun cap => ⟨_, reloc_sepExists (fun ptr => (h0 cap ptr).2)⟩
  ⟨_, reloc_sepExists (fun cap => (h1 cap).2)⟩

def relocOptChainParamsPBAt :
    ∀ (opt : Option ChainParamsPB), Σ' H, Relocatable (fun a => optChainParamsPBAt a opt) 12 H
  | none =>
    ⟨_, reloc_append 12 4#64 (reloc_pointsTo32 0#32) (reloc_memRegion 8 (by decide)) rfl rfl⟩
  | some cp =>
    let h1 := reloc_append 8 4#64 (reloc_pointsTo32 1#32) (reloc_pointsTo32 cp.maxJump) rfl rfl
    let h2 := reloc_append 12 8#64 h1 (reloc_pointsTo32 cp.maxOooKeys) rfl rfl
    ⟨_, reloc_congr h2 (fun a => by
      unfold optChainParamsPBAt chainParamsPBAt
      have ha4 : (a + 4#64) + 4#64 = a + 8#64 := by bv_omega
      rw [ha4]; ac_rfl)⟩

def relocVersionNegotiationPBAt (A : RustAlloc) (v : VersionNegotiationPB) :
    Σ' H, Relocatable (fun a => versionNegotiationPBAt A a v) 48 H :=
  let h1 := reloc_append 36 24#64 (relocRustBytesVecAt A v.authKey).2 (relocOptChainParamsPBAt v.chainParams).2 rfl rfl
  let h2 := reloc_append 40 36#64 h1 (reloc_pointsTo32 v.direction) rfl rfl
  let h3 := reloc_append 44 40#64 h2 (reloc_pointsTo32 v.minVersion) rfl rfl
  let h4 := reloc_append 48 44#64 h3 (reloc_memRegion 4 (by decide)) rfl rfl
  ⟨_, reloc_congr h4 (fun a => by unfold versionNegotiationPBAt; ac_rfl)⟩

def relocOptVersionNegotiationPBAt (A : RustAlloc) :
    ∀ (opt : Option VersionNegotiationPB),
      Σ' H, Relocatable (fun a => optVersionNegotiationPBAt A a opt) 48 H
  | none =>
    ⟨_, reloc_append 48 8#64 (reloc_pointsTo64 noneCap) (reloc_memRegion 40 (by decide)) rfl rfl⟩
  | some v => relocVersionNegotiationPBAt A v

def relocChainPBAt (A : RustAlloc) (c : ChainPB) :
    Σ' H, Relocatable (fun a => chainPBAt A a c) 80 H :=
  let h1 := reloc_append 48 24#64
              (relocVecOf A chainEpochPBSize 8 (fun ep addr => chainEpochPBAt A addr ep) c.links).2
              (relocRustBytesVecAt A c.nextRoot).2 rfl rfl
  let h2 := reloc_append 56 48#64 h1 (reloc_pointsTo64 c.currentEpoch) rfl rfl
  let h3 := reloc_append 64 56#64 h2 (reloc_pointsTo64 c.sendEpoch) rfl rfl
  let h4 := reloc_append 76 64#64 h3 (relocOptChainParamsPBAt c.params).2 rfl rfl
  let h5 := reloc_append 80 76#64 h4 (reloc_pointsTo32 c.direction) rfl rfl
  ⟨_, reloc_congr h5 (fun a => by unfold chainPBAt chainLinksVecAt; ac_rfl)⟩

def relocOptChainPBAt (A : RustAlloc) :
    ∀ (opt : Option ChainPB), Σ' H, Relocatable (fun a => optChainPBAt A a opt) 80 H
  | none =>
    ⟨_, reloc_append 80 8#64 (reloc_pointsTo64 noneCap) (reloc_memRegion 72 (by decide)) rfl rfl⟩
  | some c => relocChainPBAt A c

def relocProtoPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (st : PqRatchetState) :
    Σ' H, Relocatable (fun a => protoPqRatchetStateAt H_inner A a st) 352 H :=
  let h1 := reloc_append 128 48#64 (relocOptVersionNegotiationPBAt A st.versionNegotiation).2
              (relocOptChainPBAt A st.chain).2 rfl rfl
  let h2 := reloc_append 352 128#64 h1 (relocOptProtoPqRatchetInnerAt H_inner A st.inner).2 rfl rfl
  ⟨_, reloc_congr h2 (fun a => by unfold protoPqRatchetStateAt; ac_rfl)⟩

/-! ### `16 + 336`B Split of `protoPqRatchetStateAt` (`0x53b28..0x53b54`) -/

/-- The 32-byte tail (`+16..+48`) of `VersionNegotiationPB`. -/
def versionNegotiationPBTailAt (a16 : BitVec 64) (v : VersionNegotiationPB) : SepProp :=
  (a16 ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
    optChainParamsPBAt (a16 + 8#64) v.chainParams ∗
    ((a16 + 20#64) ↦₃₂ v.direction) ∗
    ((a16 + 24#64) ↦₃₂ v.minVersion) ∗
    memRegion (a16 + 28#64) 4

def relocVersionNegotiationPBTailAt (v : VersionNegotiationPB) :
    Σ' H, Relocatable (fun a16 => versionNegotiationPBTailAt a16 v) 32 H :=
  let h1 := reloc_append 20 8#64 (reloc_pointsTo64 (BitVec.ofNat 64 v.authKey.length))
              (relocOptChainParamsPBAt v.chainParams).2 rfl rfl
  let h2 := reloc_append 24 20#64 h1 (reloc_pointsTo32 v.direction) rfl rfl
  let h3 := reloc_append 28 24#64 h2 (reloc_pointsTo32 v.minVersion) rfl rfl
  let h4 := reloc_append 32 28#64 h3 (reloc_memRegion 4 (by decide)) rfl rfl
  ⟨_, reloc_congr h4 (fun a16 => by unfold versionNegotiationPBTailAt; ac_rfl)⟩

/-- The 32-byte tail (`+16..+48`) of `Option<VersionNegotiationPB>` given its first two words `w0, w1`. -/
def optVersionNegotiationPBTailAt (A : RustAlloc) (w0 w1 : BitVec 64) (a16 : BitVec 64) :
    Option VersionNegotiationPB → SepProp
  | none => ⌜w0 = noneCap⌝ ∗ memRegion a16 32
  | some v => versionNegotiationPBTailAt a16 v ∗ vecU8Heap A w0 w1 v.authKey

def relocOptVersionNegotiationPBTailAt (A : RustAlloc) (w0 w1 : BitVec 64) :
    ∀ (opt : Option VersionNegotiationPB),
      Σ' H, Relocatable (fun a16 => optVersionNegotiationPBTailAt A w0 w1 a16 opt) 32 H
  | none =>
    ⟨_, reloc_const_sepConj ⌜w0 = noneCap⌝ (reloc_memRegion 32 (by decide))⟩
  | some v =>
    ⟨_, reloc_sepConj_const (relocVersionNegotiationPBTailAt v).2 (vecU8Heap A w0 w1 v.authKey)⟩

/-- The 336-byte tail (`+16..+352`) of `PqRatchetState` given its first two words `w0, w1`. -/
def protoPqRatchetStateTailAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (w0 w1 : BitVec 64) (a16 : BitVec 64) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBTailAt A w0 w1 a16 st.versionNegotiation ∗
    optChainPBAt A (a16 + 32#64) st.chain ∗
    optProtoPqRatchetInnerAt H_inner A (a16 + 112#64) st.inner

def relocProtoPqRatchetStateTailAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (w0 w1 : BitVec 64) (st : PqRatchetState) :
    Σ' H, Relocatable (fun a16 => protoPqRatchetStateTailAt H_inner A w0 w1 a16 st) 336 H :=
  let h1 := reloc_append 112 32#64
              (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).2
              (relocOptChainPBAt A st.chain).2 rfl rfl
  let h2 := reloc_append 336 112#64 h1 (relocOptProtoPqRatchetInnerAt H_inner A st.inner).2 rfl rfl
  ⟨_, reloc_congr h2 (fun a16 => by unfold protoPqRatchetStateTailAt; ac_rfl)⟩

theorem optVersionNegotiationPBAt_entails_head16_tail32 (A : RustAlloc) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) :
    optVersionNegotiationPBAt A a opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜w0 ≠ none2Cap⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) opt := by
  cases opt with
  | none =>
    unfold optVersionNegotiationPBAt optVersionNegotiationPBTailAt
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w1 ?_)
    have hne : noneCap ≠ none2Cap := by decide
    apply Entails.pure_right hne
    have h : ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ⌜noneCap = noneCap⌝ ∗ memRegion (a + 16#64) 32) =
        ⌜noneCap = noneCap⌝ ∗ ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32) := by
      ac_rfl
    rw [h]
    apply Entails.pure_right rfl
    exact Entails.of_eq (by ac_rfl)
  | some v =>
    unfold optVersionNegotiationPBAt versionNegotiationPBAt rustBytesVecAt vecU8
      optVersionNegotiationPBTailAt versionNegotiationPBTailAt
    simp only [vecU8At_eq_header_heap, vecHeader, sepExists_sepConj_left, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    unfold vecU8Heap
    have hpull :
        ((((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length)) ∗
          ⌜v.authKey.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ v.authKey) ∗
            memRegion (ptr + BitVec.ofNat 64 v.authKey.length) (cap.toNat - v.authKey.length))) ∗
          optChainParamsPBAt (a + 24#64) v.chainParams ∗ ((a + 36#64) ↦₃₂ v.direction) ∗
          ((a + 40#64) ↦₃₂ v.minVersion) ∗ memRegion (a + 44#64) 4) =
        ⌜v.authKey.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
           optChainParamsPBAt (a + 24#64) v.chainParams ∗ ((a + 36#64) ↦₃₂ v.direction) ∗
           ((a + 40#64) ↦₃₂ v.minVersion) ∗ memRegion (a + 44#64) 4 ∗
           (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ v.authKey) ∗
            memRegion (ptr + BitVec.ofNat 64 v.authKey.length) (cap.toNat - v.authKey.length))) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hpure
    have hne : cap ≠ none2Cap := by
      intro hc; subst hc
      have : none2Cap.toNat = 18446744073709551614 := rfl
      omega
    apply Entails.pure_right hne
    have hpush :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
         (((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
          optChainParamsPBAt (a + 24#64) v.chainParams ∗ ((a + 36#64) ↦₃₂ v.direction) ∗
          ((a + 40#64) ↦₃₂ v.minVersion) ∗ memRegion (a + 44#64) 4) ∗
         ⌜v.authKey.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ v.authKey) ∗
          memRegion (ptr + BitVec.ofNat 64 v.authKey.length) (cap.toNat - v.authKey.length))) =
        ⌜v.authKey.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
           optChainParamsPBAt (a + 24#64) v.chainParams ∗ ((a + 36#64) ↦₃₂ v.direction) ∗
           ((a + 40#64) ↦₃₂ v.minVersion) ∗ memRegion (a + 44#64) 4 ∗
           (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ v.authKey) ∗
            memRegion (ptr + BitVec.ofNat 64 v.authKey.length) (cap.toNat - v.authKey.length))) := by
      ac_rfl
    rw [hpush]
    apply Entails.pure_right hpure
    exact Entails.of_eq (by ac_rfl)

theorem head16_tail32_entails_optVersionNegotiationPBAt (A : RustAlloc) (a w0 w1 : BitVec 64)
    (opt : Option VersionNegotiationPB) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) opt ⊢
      optVersionNegotiationPBAt A a opt := by
  cases opt with
  | none =>
    unfold optVersionNegotiationPBTailAt optVersionNegotiationPBAt
    dsimp only
    have hpull :
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ⌜w0 = noneCap⌝ ∗ memRegion (a + 16#64) 32) =
        ⌜w0 = noneCap⌝ ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hw0
    subst hw0
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1))
  | some v =>
    unfold optVersionNegotiationPBTailAt versionNegotiationPBTailAt optVersionNegotiationPBAt
      versionNegotiationPBAt rustBytesVecAt vecU8
    simp only [vecU8At_eq_header_heap, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left]
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_)
    exact Entails.of_eq (by ac_rfl)

theorem protoPqRatchetStateAt_entails_head16_tail336 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (st : PqRatchetState) :
    protoPqRatchetStateAt H_inner A a st ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ bs336 : List (BitVec 8),
        ⌜w0 ≠ none2Cap ∧ bs336.length = 336⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs336) ∗
        (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1 bs336 := by
  unfold protoPqRatchetStateAt
  refine Entails.trans (sepConj_mono_left (optVersionNegotiationPBAt_entails_head16_tail32 A a st.versionNegotiation)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  have hpull :
      ((⌜w0 ≠ none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation) ∗
        optChainPBAt A (a + 48#64) st.chain ∗
        optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner) =
      ⌜w0 ≠ none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        protoPqRatchetStateTailAt H_inner A w0 w1 (a + 16#64) st := by
    unfold protoPqRatchetStateTailAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw0
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      ((relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).2.to_bytes (a + 16#64)))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs336
  have hpull2 :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ⌜bs336.length = 336⌝ ∗
        ((a + 16#64) ↦ₛ bs336) ∗ (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1 bs336) =
      ⌜bs336.length = 336⌝ ∗
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs336) ∗
         (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1 bs336) := by
    ac_rfl
  rw [hpull2]
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right bs336 ?_))
  apply Entails.pure_right ⟨hw0, hlen⟩
  exact Entails.of_eq (by ac_rfl)

theorem head16_tail336_entails_protoPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a w0 w1 : BitVec 64) (bs336 : List (BitVec 8)) (st : PqRatchetState)
    (hlen : bs336.length = 336) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs336) ∗
      (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1 bs336 ⊢
      protoPqRatchetStateAt H_inner A a st := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      ((relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).2.of_bytes (a + 16#64) bs336 hlen))) ?_
  unfold protoPqRatchetStateTailAt protoPqRatchetStateAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hgroup :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation ∗
       optChainPBAt A (a + 48#64) st.chain ∗
       optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation) ∗
      optChainPBAt A (a + 48#64) st.chain ∗
      optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (head16_tail32_entails_optVersionNegotiationPBAt A a w0 w1 st.versionNegotiation)

/-! ## 2. `CapOk` Variants for `prost::encoding::bytes::merge` and `grow_one` -/

/-- `Vec<u8>` at `v` whose capacity satisfies `BytesMergeCapOk cap remLen`. -/
def vecU8CapOkAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap remLen⌝ ∗ vecU8At A v cap ptr bs

theorem vecU8CapOkAt_mono {A : RustAlloc} {v : BitVec 64} {rem1 rem2 : Nat} {bs : List (BitVec 8)}
    (hle : rem2 ≤ rem1) :
    vecU8CapOkAt A v rem1 bs ⊢ vecU8CapOkAt A v rem2 bs := by
  unfold vecU8CapOkAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro hcap
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.pure_right (bytesMergeCapOk_mono hcap hle) (Entails.refl _)

theorem vecU8CapOkAt_entails_rustBytesVecAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat)
    (bs : List (BitVec 8)) :
    vecU8CapOkAt A v remLen bs ⊢ rustBytesVecAt A v bs := by
  unfold vecU8CapOkAt rustBytesVecAt vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro _
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecU8At_zero_entails_vecU8CapOkAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat) :
    vecU8At A v 0#64 1#64 [] ⊢ vecU8CapOkAt A v remLen [] := by
  unfold vecU8CapOkAt
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  exact Entails.pure_right (bytesMergeCapOk_zero remLen) (Entails.refl _)

theorem vecU8CapOkAt_default_init (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8CapOkAt A a remLen [] :=
  Entails.trans (vecU8At_nil_zero_one A a) (vecU8At_zero_entails_vecU8CapOkAt A a remLen)

/-- `EpochDirectionPB` at `a` (`56` bytes) whose `next` and `prev` `Vec<u8>` capacities satisfy
    `BytesMergeCapOk _ remLen`. -/
def epochDirectionPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) : SepProp :=
  vecU8CapOkAt A a remLen d.next ∗
    vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
    ((a + 0x30#64) ↦₃₂ d.ctr) ∗
    memRegion (a + 0x34#64) 4

theorem epochDirectionPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {d : EpochDirectionPB} (hle : rem2 ≤ rem1) :
    epochDirectionPBCapOkAt A a rem1 d ⊢ epochDirectionPBCapOkAt A a rem2 d := by
  unfold epochDirectionPBCapOkAt
  exact sepConj_mono (vecU8CapOkAt_mono hle)
    (sepConj_mono (vecU8CapOkAt_mono hle) (Entails.refl _))

theorem epochDirectionPBCapOkAt_entails_epochDirectionPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢ epochDirectionPBAt A a d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBAt
  exact sepConj_mono (vecU8CapOkAt_entails_rustBytesVecAt A a remLen d.next)
    (sepConj_mono (vecU8CapOkAt_entails_rustBytesVecAt A (a + 0x18#64) remLen d.prev) (Entails.refl _))

theorem epochDirectionPBCapOkAt_default_init (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      ((a + 48#64) ↦₃₂ 0#32) ∗ memRegion (a + 52#64) 4 ⊢
    epochDirectionPBCapOkAt A a remLen default := by
  rw [epochDirectionPB_default_eq]
  unfold epochDirectionPBCapOkAt
  dsimp only
  have h1 := vecU8CapOkAt_default_init A a remLen
  have h2 := vecU8CapOkAt_default_init A (a + 24#64) remLen
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  exact sepConj_mono h1 (sepConj_mono_left h2)

/-- `Option EpochDirectionPB` at `a` (`56` bytes) with `CapOk` on `some d`. -/
def optEpochDirectionPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    Option EpochDirectionPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48
  | some d => epochDirectionPBCapOkAt A a remLen d

theorem optEpochDirectionPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {opt : Option EpochDirectionPB} (hle : rem2 ≤ rem1) :
    optEpochDirectionPBCapOkAt A a rem1 opt ⊢ optEpochDirectionPBCapOkAt A a rem2 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some d => exact epochDirectionPBCapOkAt_mono hle

theorem optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (opt : Option EpochDirectionPB) :
    optEpochDirectionPBCapOkAt A a remLen opt ⊢ optEpochDirectionPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some d => exact epochDirectionPBCapOkAt_entails_epochDirectionPBAt A a remLen d

/-- `ChainEpochPB` at `a` (`112` bytes) with `CapOk` on `send` and `recv`. -/
def chainEpochPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (ep : ChainEpochPB) : SepProp :=
  optEpochDirectionPBCapOkAt A a remLen ep.send ∗
    optEpochDirectionPBCapOkAt A (a + 0x38#64) remLen ep.recv

theorem chainEpochPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {ep : ChainEpochPB} (hle : rem2 ≤ rem1) :
    chainEpochPBCapOkAt A a rem1 ep ⊢ chainEpochPBCapOkAt A a rem2 ep :=
  sepConj_mono (optEpochDirectionPBCapOkAt_mono hle) (optEpochDirectionPBCapOkAt_mono hle)

theorem chainEpochPBCapOkAt_entails_chainEpochPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (ep : ChainEpochPB) :
    chainEpochPBCapOkAt A a remLen ep ⊢ chainEpochPBAt A a ep :=
  sepConj_mono
    (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A a remLen ep.send)
    (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A (a + 0x38#64) remLen ep.recv)

/-- `VersionNegotiationPB` at `a` (`48` bytes) with `CapOk` on `authKey`. -/
def versionNegotiationPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (v : VersionNegotiationPB) : SepProp :=
  vecU8CapOkAt A a remLen v.authKey ∗
    optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
    ((a + 0x24#64) ↦₃₂ v.direction) ∗
    ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
    memRegion (a + 0x2c#64) 4

theorem versionNegotiationPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {v : VersionNegotiationPB} (hle : rem2 ≤ rem1) :
    versionNegotiationPBCapOkAt A a rem1 v ⊢ versionNegotiationPBCapOkAt A a rem2 v :=
  sepConj_mono_left (vecU8CapOkAt_mono hle)

theorem versionNegotiationPBCapOkAt_entails_versionNegotiationPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (v : VersionNegotiationPB) :
    versionNegotiationPBCapOkAt A a remLen v ⊢ versionNegotiationPBAt A a v :=
  sepConj_mono_left (vecU8CapOkAt_entails_rustBytesVecAt A a remLen v.authKey)

theorem versionNegotiationPBCapOkAt_default_init (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      ((a + 24#64) ↦₃₂ 0#32) ∗ memRegion (a + 28#64) 8 ∗
      ((a + 36#64) ↦₆₄ 0#64) ∗ memRegion (a + 44#64) 4 ⊢
    versionNegotiationPBCapOkAt A a remLen default := by
  rw [versionNegotiationPB_default_eq]
  unfold versionNegotiationPBCapOkAt optChainParamsPBAt
  dsimp only
  have h1 := vecU8CapOkAt_default_init A a remLen
  have h36 : ((a + 36#64) ↦₆₄ 0#64) = ((a + 36#64) ↦₃₂ 0#32) ∗ ((a + 40#64) ↦₃₂ 0#32) := by
    rw [pointsTo64_zero_split32 (a + 36#64)]
    have : (a + 36#64) + 4#64 = a + 40#64 := by bv_omega
    rw [this]
  have ha28 : (a + 24#64) + 4#64 = a + 28#64 := by bv_omega
  rw [h36, ha28]
  refine Entails.trans (sepConj_mono_left h1) ?_
  exact Entails.of_eq (by ac_rfl)

/-- `Option VersionNegotiationPB` at `a` (`48` bytes) with `CapOk` on `some v`. -/
def optVersionNegotiationPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    Option VersionNegotiationPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some v => versionNegotiationPBCapOkAt A a remLen v

theorem optVersionNegotiationPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {opt : Option VersionNegotiationPB} (hle : rem2 ≤ rem1) :
    optVersionNegotiationPBCapOkAt A a rem1 opt ⊢ optVersionNegotiationPBCapOkAt A a rem2 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some v => exact versionNegotiationPBCapOkAt_mono hle

theorem optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (opt : Option VersionNegotiationPB) :
    optVersionNegotiationPBCapOkAt A a remLen opt ⊢ optVersionNegotiationPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some v => exact versionNegotiationPBCapOkAt_entails_versionNegotiationPBAt A a remLen v

/-- `ChainPB` at `a` (`80` bytes) with `ch.links.length + remLen ≤ 2 ^ 54` (for `grow_one` on
    `ch.links`) and `CapOk` on `ch.nextRoot` (for `bytes::merge` on `ch.nextRoot`). -/
def chainPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (ch : ChainPB) : SepProp :=
  ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
    chainLinksVecAt A a ch.links ∗
    vecU8CapOkAt A (a + 0x18#64) remLen ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

theorem chainPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {ch : ChainPB} (hle : rem2 ≤ rem1) :
    chainPBCapOkAt A a rem1 ch ⊢ chainPBCapOkAt A a rem2 ch := by
  unfold chainPBCapOkAt
  apply Entails.pure_left; intro hlen
  apply Entails.pure_right (by omega)
  exact sepConj_mono_right (sepConj_mono_left (vecU8CapOkAt_mono hle))

theorem chainPBCapOkAt_entails_chainPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (ch : ChainPB) :
    chainPBCapOkAt A a remLen ch ⊢ chainPBAt A a ch := by
  unfold chainPBCapOkAt chainPBAt
  apply Entails.pure_left; intro _
  exact sepConj_mono_right
    (sepConj_mono_left (vecU8CapOkAt_entails_rustBytesVecAt A (a + 0x18#64) remLen ch.nextRoot))

theorem chainPBCapOkAt_default_init (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (hrem : remLen ≤ 2 ^ 54) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 0#64) ∗
      ((a + 64#64) ↦₃₂ 0#32) ∗ memRegion (a + 68#64) 8 ∗
      ((a + 76#64) ↦₃₂ 0#32) ⊢
    chainPBCapOkAt A a remLen default := by
  rw [chainPB_default_eq]
  unfold chainPBCapOkAt optChainParamsPBAt
  dsimp only
  apply Entails.pure_right (by simpa using hrem)
  have h1 := chainLinksVecAt_default_init A a
  have h2 := vecU8CapOkAt_default_init A (a + 24#64) remLen
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha68 : (a + 64#64) + 4#64 = a + 68#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [ha68]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  exact Entails.of_eq (by ac_rfl)

/-- `Option ChainPB` at `a` (`80` bytes) with `CapOk` on `some ch`. -/
def optChainPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    Option ChainPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some ch => chainPBCapOkAt A a remLen ch

theorem optChainPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat}
    {opt : Option ChainPB} (hle : rem2 ≤ rem1) :
    optChainPBCapOkAt A a rem1 opt ⊢ optChainPBCapOkAt A a rem2 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some ch => exact chainPBCapOkAt_mono hle

theorem optChainPBCapOkAt_entails_optChainPBAt (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (opt : Option ChainPB) :
    optChainPBCapOkAt A a remLen opt ⊢ optChainPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some ch => exact chainPBCapOkAt_entails_chainPBAt A a remLen ch

/-- `PqRatchetState` at `a` (`352` bytes) with `CapOk` on `versionNegotiation`, `chain`, and `inner`. -/
def protoPqRatchetStateCapOkAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBCapOkAt A a remLen st.versionNegotiation ∗
    optChainPBCapOkAt A (a + 48#64) remLen st.chain ∗
    optProtoPqRatchetInnerCapOkAt H_inner A (a + 128#64) remLen st.inner

theorem protoPqRatchetStateCapOkAt_mono {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {a : BitVec 64} {rem1 rem2 : Nat} {st : PqRatchetState} (hle : rem2 ≤ rem1) :
    protoPqRatchetStateCapOkAt H_inner A a rem1 st ⊢
      protoPqRatchetStateCapOkAt H_inner A a rem2 st :=
  sepConj_mono (optVersionNegotiationPBCapOkAt_mono hle)
    (sepConj_mono (optChainPBCapOkAt_mono hle) (optProtoPqRatchetInnerCapOkAt_mono hle))

theorem protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (st : PqRatchetState) :
    protoPqRatchetStateCapOkAt H_inner A a remLen st ⊢ protoPqRatchetStateAt H_inner A a st :=
  sepConj_mono
    (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A a remLen st.versionNegotiation)
    (sepConj_mono
      (optChainPBCapOkAt_entails_optChainPBAt A (a + 48#64) remLen st.chain)
      (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A (a + 128#64) remLen st.inner))

/-! ## 3. Callee Specifications & `decodeStateSpecX` -/

/-- Stack budget for `prost::encoding::message::merge::<ChainParams, &mut &[u8]>` (`0x4dcf8`). -/
abbrev chainParamsMergeStack : Nat := skipField3Stack 99

/-- Ghost arguments of `prost::encoding::message::merge::<ChainParams, &mut &[u8]>` (`0x4dcf8`). -/
structure ChainParamsMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : ChainParamsPB
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>`
(`0x4dcf8`, 144 instructions). Bound `x.bs.length < 2 ^ 63` is discharged by caller `decode_state`
from the input slice length invariant (`st.bytes.length < 2 ^ 32` via `DEV-SPQR3`). -/
def chainParamsMergeSpec (A : RustAlloc) : Spec ChainParamsMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      chainParamsPBAt x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp chainParamsMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp chainParamsMergeStack ∗
      match (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chainParamsPBAt x.msgPtr m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ChainParamsPB, chainParamsPBAt x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget for `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`). -/
abbrev epochDirectionMergeStack : Nat := skipField3Stack 98

/-- Ghost arguments of `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`). -/
structure EpochDirectionMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : EpochDirectionPB
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
(`0x4f544`, 145 instructions). Bound `x.bs.length < 2 ^ 63` and `epochDirectionPBCapOkAt` are
discharged by caller `decode_state` from the input slice invariant and `epochDirectionPBCapOkAt_default_init` /
`epochDirectionPBCapOkAt_mono`. -/
def epochDirectionMergeSpec (A : RustAlloc) : Spec EpochDirectionMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧ s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      epochDirectionPBCapOkAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp epochDirectionMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp epochDirectionMergeStack ∗
      match (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ epochDirectionPBCapOkAt A x.msgPtr rest.length m' ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : EpochDirectionPB, epochDirectionPBAt A x.msgPtr m') ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! Note: The contract `Prost.MessageMerge.v1StateMergeSpec A b` and stack budget
    `Prost.MessageMerge.v1StateMergeStack` (`816 + chunkedInlStack = 14,640` bytes) for
    `prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>`
    (`0x4e7e8`, 855 instructions) are imported from
    `LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs`. -/

/-- Stack budget for `0x4c0d4` (`Option<InnerState>`) and `0x4c460` (`PqRatchetState`):
    `0x60 + allocHookStack` (`4,192` bytes). -/
abbrev dropOptProtoInnerStateStack : Nat := 0x60 + allocHookStack

/-- Ghost arguments for `drop_glue::<Option<spqr::proto::pq_ratchet::v1_state::InnerState>>` (`0x4c0d4`). -/
structure DropOptProtoInnerStateGhost where
  a : BitVec 64
  st : Option V1State.InnerState

/-- Contract for `core::ptr::drop_glue::<Option<spqr::proto::pq_ratchet::v1_state::InnerState>>` (`0x4c0d4`). -/
def dropOptProtoInnerStateSpec (H_inner : V1InnerHeapPred) (A : RustAlloc) (b : BitVec 64) :
    Spec DropOptProtoInnerStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optProtoInnerStateAt H_inner A x.a x.st ∗
      v1StateJumpTablesAt b ∗
      A.pool ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 224 ∗
      v1StateJumpTablesAt b ∗
      A.pool ∗ stackAt s0.sp dropOptProtoInnerStateStack
  onPanic := fun _ _ _ => ⌜False⌝

/-- Ghost arguments for `drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (`0x4c460`). -/
structure DropProtoPqRatchetStateGhost where
  a : BitVec 64
  st : PqRatchetState

/-- Contract for `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (`0x4c460`). -/
def dropProtoPqRatchetStateSpec (H_inner : V1InnerHeapPred) (A : RustAlloc) (b : BitVec 64) :
    Spec DropProtoPqRatchetStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoPqRatchetStateAt H_inner A x.a x.st ∗
      v1StateJumpTablesAt b ∗
      A.pool ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 352 ∗
      v1StateJumpTablesAt b ∗
      A.pool ∗ stackAt s0.sp dropOptProtoInnerStateStack
  onPanic := fun _ _ _ => ⌜False⌝

/-- Bundle of callee contracts used by `spqr::decode_state` (`0x5349c`). -/
structure DecodeStateCalleeContracts (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  b_page_aligned : b &&& 0xfff#64 = 0#64
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt ⊢
      optProtoInnerStateAt H_inner A a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen opt
  alloc : AllocContracts b A ext
  decodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A)
  decodeErrorPush : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName) (decodeErrorPushSpec A)
  decodeVarint2 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr Varint.decodeVarint2Name) (Varint.decodeVarint2Spec A)
  skipField3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name) (skipField3Spec A)
  chainParamsMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainParamsMergeName) (chainParamsMergeSpec A)
  growOneChainEpoch : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName) (growOneStrideFullSpec A 112 8)
  dropOptProtoInnerState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
    (dropOptProtoInnerStateSpec H_inner A b)
  dropProtoPqRatchetState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropProtoPqRatchetStateName)
    (dropProtoPqRatchetStateSpec H_inner A b)

/-- Full callee contracts for `spqr::decode_state` (`0x5349c`), extending
    `DecodeStateCalleeContracts` with `.inImage img` contracts for callees that invoke
    `bytes::merge [local#3]` (`bytesMerge3`, `epochDirectionMerge`, `v1StateMerge`). -/
structure DecodeStateCalleeContractsX (H_inner : V1InnerHeapPred) (img : Obj.Image)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContracts H_inner b A ext where
  bytesMerge3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img)
  epochDirectionMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr epochDirectionMergeName)
    ((epochDirectionMergeSpec A).inImage img)
  v1StateMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr v1StateMergeName)
    ((Prost.MessageMerge.v1StateMergeSpec A b).inImage img)

/-- Minimal 4K-stack allocator/memcpy projection required by `spqr::decode_state`. -/
structure DecodeStateAllocContracts (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A)
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.memcpyName)
      (libcMemcpySpec hookStack)
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.memcpyName)
      (sessionMemcpySpec hookStack)

/-- 4K-stack bundle of callee contracts used by `spqr::decode_state`. -/
structure DecodeStateCalleeContracts4K (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  b_page_aligned : b &&& 0xfff#64 = 0#64
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt ⊢
      optProtoInnerStateAt H_inner A a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen opt
  alloc : DecodeStateAllocContracts b A ext
  decodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A)
  decodeErrorPush : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName) (decodeErrorPushSpec A)
  decodeVarint2 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr Varint.decodeVarint2Name) (Varint.decodeVarint2Spec A)
  skipField3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name) (skipField3Spec A)
  chainParamsMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainParamsMergeName) (chainParamsMergeSpec A)
  growOneChainEpoch : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName) (growOneStrideFullSpec A 112 8)
  dropOptProtoInnerState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
    (dropOptProtoInnerStateSpec H_inner A b)
  dropProtoPqRatchetState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropProtoPqRatchetStateName)
    (dropProtoPqRatchetStateSpec H_inner A b)

/-- Full 4K-stack callee contracts for `spqr::decode_state`, extending
    `DecodeStateCalleeContracts4K` with `.inImage img` contracts for `bytesMerge3`,
    `epochDirectionMerge`, and `v1StateMerge`. -/
structure DecodeStateCalleeContractsX4K (H_inner : V1InnerHeapPred) (img : Obj.Image)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContracts4K H_inner b A ext where
  bytesMerge3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img)
  epochDirectionMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr epochDirectionMergeName)
    ((epochDirectionMergeSpec A).inImage img)
  v1StateMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr v1StateMergeName)
    ((Prost.MessageMerge.v1StateMergeSpec A b).inImage img)

theorem DecodeStateCalleeContracts.to4K {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts H_inner b A ext) :
    DecodeStateCalleeContracts4K H_inner b A ext :=
  { b_page_aligned := hc.b_page_aligned
    of_drop_inner := hc.of_drop_inner
    of_cap_inner := hc.of_cap_inner
    alloc := ⟨hc.alloc.dealloc, fun stk _ _ => hc.alloc.memcpy stk,
      fun stk _ _ => hc.alloc.session_memcpy stk⟩
    decodeErrorFrom := hc.decodeErrorFrom
    decodeErrorPush := hc.decodeErrorPush
    decodeVarint2 := hc.decodeVarint2
    skipField3 := hc.skipField3
    chainParamsMerge := hc.chainParamsMerge
    growOneChainEpoch := hc.growOneChainEpoch
    dropOptProtoInnerState := hc.dropOptProtoInnerState
    dropProtoPqRatchetState := hc.dropProtoPqRatchetState }

theorem DecodeStateCalleeContractsX.to4K {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX H_inner img b A ext) :
    DecodeStateCalleeContractsX4K H_inner img b A ext :=
  { hc.toDecodeStateCalleeContracts.to4K with
    bytesMerge3 := hc.bytesMerge3
    epochDirectionMerge := hc.epochDirectionMerge
    v1StateMerge := hc.v1StateMerge }

/-- Stack budget for `spqr::decode_state` (`0x5349c`):
    own frame `0x570` (`1,392` bytes) plus `v1StateMergeStack` (`14,640` bytes) = `16,032` bytes. -/
abbrev decodeStateStackX : Nat := 0x570 + v1StateMergeStack

/-- Ghost arguments of `spqr::decode_state` (`0x5349c`). -/
structure DecodeStateGhost where
  st : VecArg
  outPtr : BitVec 64

/-- Specification of `spqr::decode_state` (`0x5349c`, 745 instructions) against
    `Proto.spqrDecodeState` (`LibsignalSpqrV1.decodeState`).

    * `x8 = x.outPtr` (sret `*mut Result<PqRatchetState, spqr::Error>`, `352` bytes),
      `x0 = x.st.v` (`s: &SerializedState`, i.e. `&Vec<u8>`).
    * Input bound `x.st.bytes.length < 2 ^ 32` is discharged by callers `spqr::send` and `spqr::recv`
      from `st.bytes.length < 2 ^ 32` (`DEV-SPQR3` in `spqrSendSpecT` / `spqrRecvSpecExactKeyBounded`). -/
def decodeStateSpecX (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc) :
    Spec DecodeStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32⌝ ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗ stackAt s.sp decodeStateStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool ∗ stackAt s0.sp decodeStateStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `spqr::decode_state` (`0x5349c`) meets `(decodeStateSpecX H_inner img.base A).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def DecodeStateOkX (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodeStateName)
    ((decodeStateSpecX H_inner img.base A).inImage img)

end CryptoVerification.SpqrV1.Top.DecodeState

