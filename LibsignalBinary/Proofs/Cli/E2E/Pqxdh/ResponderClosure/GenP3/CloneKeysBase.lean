/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Shared Keys Base

External callee hooks, `sessionStateAt` front/tail decompositions, OOM panic tails
(`+0x375c`, `+0x3768`, `+0x3774`), and OOM-aware `__rust_alloc(sz, 1)` wrappers shared across
Segments 1 and 4.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. External Callee Hooks and `SessionState` / Quad Helpers -/

theorem closure_shim_4k_ok (b : BitVec 64) {A : RustAlloc}
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec :=
  hA.shim_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem closure_alloc_4k_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustAllocSpec A) :=
  hA.alloc_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem closure_memcpy_4k_ok (b : BitVec 64) {A : RustAlloc}
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "memcpy" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (withStack sessionMemcpyRegionSpec allocHookStack) := by
  have hok := hA.session_memcpy_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "memcpy" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])
  refine subroutine_ok_mono hok (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · simpa only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec,
      withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hpre
  · simpa only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec,
      withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hpost

theorem closure_shim_ok (b : BitVec 64) {A : RustAlloc}
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec :=
  closure_shim_4k_ok b ext (AllocContractsMem4K.of_AllocContracts hA)

theorem closure_alloc_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustAllocSpec A) :=
  closure_alloc_4k_ok (AllocContractsMem4K.of_AllocContracts hA)

theorem closure_memcpy_ok (b : BitVec 64) {A : RustAlloc}
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "memcpy" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "memcpy" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem closure_panic_at_handle_error (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

def sessionStatePure (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

def frontSessionRestAt (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecAt A 104 8 (chainAt A) (coroPtr + 0x140#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
    vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x248#64) ↦ₛ G.regIds)

theorem sessionStateAt_front_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜sessionStatePure G st⌝ ∗
        vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
        vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
        vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
        ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
        ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
        frontSessionRestAt A coroPtr G st := by
  unfold sessionStateAt sessionStatePure frontSessionRestAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

def tailSessionRestAt (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
    vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
    vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (coroPtr + 0x140#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
    ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter)

theorem sessionStateAt_tail_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜sessionStatePure G st⌝ ∗
        vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
        vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((coroPtr + 0x248#64) ↦ₛ G.regIds) ∗
        tailSessionRestAt A coroPtr G st := by
  unfold sessionStateAt sessionStatePure tailSessionRestAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

theorem cat128_lo (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := by
  bv_kernel

theorem cat128_hi (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := by
  bv_kernel

theorem chunks104W6QAt_sp_0x3e0 (sp w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0x3e0#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0x3e0#64) ↦₆₄ w0) ∗
        ((sp + 0x3e8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0x3f0#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp + 0x3f8#64) ↦₆₄ q1.extractLsb' 0 64) ∗
        ((sp + 0x400#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0x408#64) ↦₆₄ q2.extractLsb' 0 64) ∗
        ((sp + 0x410#64) ↦₆₄ q2.extractLsb' 64 64) ∗
        ((sp + 0x418#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0x420#64) ↦₆₄ q3.extractLsb' 64 64) ∗
        ((sp + 0x428#64) ↦₆₄ q4.extractLsb' 0 64) ∗
        ((sp + 0x430#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0x438#64) ↦₆₄ q5.extractLsb' 0 64) ∗
        ((sp + 0x440#64) ↦₆₄ q5.extractLsb' 64 64) := by
  unfold chunks104W6QAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 2. OOM Panic Tails (`+0x375c`, `+0x3768`, `+0x3774`) and `__rust_alloc(sz, 1)` Wrapper -/

/- OOM panic tail at `+0x375c`: `mov w0, #1; mov x1, x26; bl handle_error`. -/
set_option maxHeartbeats 400000 in
theorem oom_tail_375c_ok (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x375c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hpanic := closure_panic_at_handle_error b ext
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      s emp (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics ext) 0x375c 0x3764
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/- OOM panic tail at `+0x3768`: `mov w0, #1; mov x1, x24; bl handle_error`. -/
set_option maxHeartbeats 400000 in
theorem oom_tail_3768_ok (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3768#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hpanic := closure_panic_at_handle_error b ext
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      s emp (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics ext) 0x3768 0x3770
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/- OOM panic tail at `+0x3774`: `ldr x1, [sp, #0xd0]; mov w0, #1; bl handle_error`. -/
set_option maxHeartbeats 400000 in
theorem oom_tail_3774_ok (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 s : State) (ret v_d0 : BitVec 64) (F : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3774#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s
      (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) Q (P3P4.PanicOomProp s0) := by
  have hpanic := closure_panic_at_handle_error b ext
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      s ((s.sp + 0xd0#64) ↦₆₄ v_d0)
      (fun s1 P_f => (P_f ⊢ (s.sp + 0xd0#64) ↦₆₄ v_d0) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics ext) 0x3774 0x377c
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep rfl
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/- Generic OOM-aware `__rust_alloc(sz, 1)` call wrapper on `tripleRatchetProgAtExt b ext` (4K stack). -/
set_option maxHeartbeats 400000 in
theorem alloc_call_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧
        s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off))
    (hcbz : ∀ s2 : State,
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off →
      s2.status = .Running →
      s2.readReg64 .x0 = 0#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off)
        s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace))
    (hoom_tail : ∀ s3 : State,
      img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off →
      s3.status = .Running →
      s3.sp = s.sp →
      s3.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s3
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : LayoutOk sz 1 := ⟨hsz_pos, ⟨0, rfl⟩, by omega⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk sz 1 :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay⟩
  refine P3P4.SepWPp.call_frame_frozen_nopanic (spec := rustAllocSpec A) (x := (sz, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hF1 hsym1 (closure_alloc_4k_ok hA) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]
  rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 (hcbz s2 hpc2 hrun2 hoom) (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact hoom_tail s3 hF3 hsym3 hpc3 hrun3 (hsp3.trans hsp2) (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hF2, hsym2⟩

theorem alloc_call_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
            ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
        s emp
        (fun s1 P_f =>
          (P_f ⊢ emp) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧
          s1.readReg64 .x1 = 1#64 ∧
          CalleeSavedPreserved s s1 ∧
          s1.readReg64 .x30 =
            (tripleRatchetProgAtExt b ext).fnAddr
              CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) →
      (∀ s2 : State,
        s2.pc = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off →
        s2.status = .Running →
        s2.readReg64 .x0 = 0#64 →
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off)
          s2 emp
          (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace)) →
      (∀ s3 : State,
        img.FrozenLoaded s3 → s3.symtab = img.symtab →
        s3.pc = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off →
        s3.status = .Running →
        s3.sp = s.sp →
        s3.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s3
          ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
          (fun s2 P_f =>
            (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                    A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
            s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
            CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
          (P3P4.PanicOomProp s0)) →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_call_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

/- OOM-aware `__rust_alloc(sz, 1)` at `+0x179c → +0x17a0` (OOM jumps to `+0x3774`). -/
set_option maxHeartbeats 400000 in
theorem alloc_179c_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (v_d0 : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F))
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F)) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_4k_ok img b ext hA s0 s 0x17a0#64 0x3774#64 sz
    (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x179c 0x179c
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x17a0 0x17a0
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 hsp3 htr3
    have halign3 : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
    rw [show (A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) =
      ((s3.sp + 0xd0#64) ↦₆₄ v_d0) ∗ ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F) by
      rw [hsp3]; ac_rfl]
    exact oom_tail_3774_ok img b ext s0 s3 _ v_d0 _ _ hF3 hsym3 hpc3 hrun3 halign3 htr3

theorem alloc_179c_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (v_d0 : BitVec 64) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = BitVec.ofNat 64 sz →
      s.readReg64 .x1 = 1#64 →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F))
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F)) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_179c_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

/- OOM-aware `__rust_alloc(sz, 1)` at `+0x18fc → +0x1900` (OOM jumps to `+0x3768`). -/
set_option maxHeartbeats 400000 in
theorem alloc_18fc_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_4k_ok img b ext hA s0 s 0x1900#64 0x3768#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x18fc 0x18fc
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x1900 0x1900
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact oom_tail_3768_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

theorem alloc_18fc_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = BitVec.ofNat 64 sz →
      s.readReg64 .x1 = 1#64 →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_18fc_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

/- OOM-aware `__rust_alloc(sz, 1)` at `+0x1938 → +0x193c` (OOM jumps to `+0x375c`). -/
set_option maxHeartbeats 400000 in
theorem alloc_1938_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_4k_ok img b ext hA s0 s 0x193c#64 0x375c#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x1938 0x1938
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x193c 0x193c
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact oom_tail_375c_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

theorem alloc_1938_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = BitVec.ofNat 64 sz →
      s.readReg64 .x1 = 1#64 →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_1938_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

/- OOM-aware `__rust_alloc(sz, 1)` at `+0x1b48 → +0x1b4c` (OOM jumps to `+0x3768`). -/
set_option maxHeartbeats 400000 in
theorem alloc_1b48_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_4k_ok img b ext hA s0 s 0x1b4c#64 0x3768#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x1b48 0x1b48
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x1b4c 0x1b4c
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact oom_tail_3768_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

theorem alloc_1b48_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = BitVec.ofNat 64 sz →
      s.readReg64 .x1 = 1#64 →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_1b48_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

/- OOM-aware `__rust_alloc(sz, 1)` at `+0x1b84 → +0x1b88` (OOM jumps to `+0x375c`). -/
set_option maxHeartbeats 400000 in
theorem alloc_1b84_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b84#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b88#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_4k_ok img b ext hA s0 s 0x1b88#64 0x375c#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x1b84 0x1b84
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x1b88 0x1b88
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact oom_tail_375c_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

theorem alloc_1b84_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (sz : Nat) (F : SepProp),
      0 < sz → sz < 2 ^ 63 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b84#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = BitVec.ofNat 64 sz →
      s.readReg64 .x1 = 1#64 →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b88#64) s
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0) :=
  alloc_1b84_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

theorem sepWPp_pure_4th {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 P4 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ P4) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4) Q Qp := by
  rw [show P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ P4 by ac_rfl]
  exact SepWPp.pure_elim h

theorem entails_pure_3rd {P P1 P2 P3 : SepProp} {φ : Prop}
    (hφ : φ) (h : P ⊢ P1 ∗ P2 ∗ P3) :
    P ⊢ P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact Entails.pure_right hφ h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
