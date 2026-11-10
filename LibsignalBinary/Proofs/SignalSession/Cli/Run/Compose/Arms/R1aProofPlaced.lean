/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
public import ProofLib.SepLogic.WPp
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import all Init.Data.String.Defs

/-!
# Relocatable Arm `R1a` Proof for `signal_session::run`

Proves `run_hop_init1_of_slots` and `run_hop_init1_placed_ok` (`R+0x214 → R+0x74c / R+0x2c7c`) on
Block `579` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib Arm64.Process CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `.rodata` Literals and Placed Callee Bridges -/

private abbrev r1a_CodeOk [LibsignalPlacement] : Memory → Prop := LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl
private def r1a_idKeySym : String := "libsignal_cli:.rodata..Lanon.50"
private def r1a_unreadSym : String := "libsignal_cli:.rodata..Lanon.65"
private def r1a_herrSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

private theorem r1a_rodata_idkey_intro [LibsignalPlacement] {m : Memory} {P : SepProp} (hcrl : r1a_CodeOk m) (hm : m ⊨ P) :
    m ⊨ (lsρ r1a_idKeySym ↦ᵣ utf8 "identity-key") ∗ P := lsro_intro_chk hcrl.2 (sym := r1a_idKeySym) (bs := utf8 "identity-key") (by decide +kernel) hm
private theorem r1a_rodata_unreadable_intro [LibsignalPlacement] {m : Memory} {P : SepProp} (hcrl : r1a_CodeOk m) (hm : m ⊨ P) :
    m ⊨ (lsρ r1a_unreadSym ↦ᵣ utf8 "file could not be read") ∗ P := lsro_intro_chk hcrl.2 (sym := r1a_unreadSym) (bs := utf8 "file could not be read") (by decide +kernel) hm
private theorem r1a_panic_handle_error [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hh : RunHooksPlaced A H) :
    (runProgPlaced H).externAt? (lsρ r1a_herrSym) = some Rust.panicked := ls_panicAt_of_cliPanic (prog := runProgPlaced H) (i := 579) hh.panics (sym := r1a_herrSym)
private theorem r1a_shim_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustNoAllocShimSymCli) (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)) :=
  shim_lscro_of_cli (callerProg := runProgPlaced H) (i := 579) hh.alloc (stk := extHookStack)
private theorem r1a_alloc_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustAllocSymCli) (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  alloc_lscro_of_cli (callerProg := runProgPlaced H) (i := 579) hh.alloc
private theorem r1a_dealloc_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustDeallocSymCli) (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := runProgPlaced H) (i := 579) hh.alloc
private theorem r1a_memRegion_zero (p : BitVec 64) (n : Nat) : memRegion p n = memRegion (p + 0#64) n := by rw [BitVec.add_zero]

/-! ## Pure Semantics, Trace, and Path-Bound Bridges -/
private theorem r1a_spAligned_of_fsp {s0 s : State} (hsp : s.sp = runFsp s0) (h0 : s0.spAligned = true) : s.spAligned = true := by
  unfold State.spAligned; rw [hsp, runFsp]; exact ProofLib.spAligned_sub s0.sp runFrame h0 (by decide)
private theorem r1a_low64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
private theorem r1a_high64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
private theorem r1a_pointsTo64_congr {a x y : BitVec 64} (h : x = y) : (a ↦₆₄ x) = (a ↦₆₄ y) := h ▸ rfl
private theorem r1a_idKey_path_bounds [LibsignalPlacement] {S : RunSem} {g : RunCall} {peerV : AddrV} {dir : Bytes} {s0 : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hc : g.c = .init peerV dir) :
    cliWrOk (dir ++ [0x2f#8] ++ utf8 "identity-key") ∧ dir.length < 2 ^ 32 ∧ (utf8 "identity-key").length < 2 ^ 32 ∧ (dir ++ [0x2f#8] ++ utf8 "identity-key").length < 2 ^ 32 := by
  have hwr := he.init_bundlePaths_ok hc "identity-key" (by decide); have hlen := hwr.2
  have hidlen : (utf8 "identity-key").length = 12 := by decide +kernel
  refine ⟨hwr, ?_, by omega, hlen⟩; simp only [bundlePath, List.length_append, List.length_singleton, hidlen] at hlen; omega
private theorem r1a_reject_of_read_err [LibsignalPlacement] {S : RunSem} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s) (hcall : g.c = .init peerV dir)
    (herr : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .error ()) : g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩; have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) := hcall ▸ he.parse
  have herr' : cliIo.rd (runFiles g.i) (bundlePath dir "identity-key") = .error () := herr
  have hbf : bundleFile (runFiles g.i) dir "identity-key" = none := by unfold bundleFile; rw [herr']; rfl
  have hrb : readBundleV (runFiles g.i) dir peerV.device = none := by simp [readBundleV, hbf]
  rw [he.rel.2.2.2.2.2]; unfold runAns; simp [hparse, hget, hme, hrb]
private theorem r1a_reject_of_decode_err [LibsignalPlacement] {S : RunSem} {g : RunCall} {peerV : AddrV} {dir ikB : Bytes} {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s) (hcall : g.c = .init peerV dir)
    (hik : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB) (hdec : exceptOpt (decodeIdentityKey ikB) = none) : g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩; have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) := hcall ▸ he.parse
  have hik' : cliIo.rd (runFiles g.i) (bundlePath dir "identity-key") = .ok ikB := hik
  have hbf : bundleFile (runFiles g.i) dir "identity-key" = some ikB := by unfold bundleFile; rw [hik']; rfl
  have hrb : readBundleV (runFiles g.i) dir peerV.device = none := by simp [readBundleV, hbf, hdec]
  rw [he.rel.2.2.2.2.2]; unfold runAns; simp [hparse, hget, hme, hrb]
private theorem r1a_ikOk_sem {F : FsFiles} {dir ikB : Bytes} {idKey : IdentityKey}
    (hik : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB) (hdec : decodeIdentityKey ikB = .ok idKey) :
    bundleFile F dir "identity-key" = some ikB ∧ exceptOpt (decodeIdentityKey ikB) = some idKey := by
  have hik' : cliIo.rd F (bundlePath dir "identity-key") = .ok ikB := hik; exact ⟨by unfold bundleFile; rw [hik']; rfl, by rw [hdec]; rfl⟩
private theorem r1a_allocFailedIn_of_append {s1 s2 : State} (htr : s2.trace = s1.trace ++ [allocFailedEvent]) : allocFailedIn s1 s2 := by
  unfold allocFailedIn; rw [htr, List.drop_left]; exact List.Mem.head _
private theorem r1a_hist_ans_step {i : Inputs} {g : RunCall} {s0 s1 s2 : State} (h : RunHistOk i s0 s1 ∧ g.a = some none)
    (htr : s2.trace = s1.trace) (hfs : s2.fs.files = s1.fs.files) : RunHistOk i s0 s2 ∧ g.a = some none :=
  ⟨⟨hfs.trans h.1.1, by simpa [htr] using h.1.2⟩, h.2⟩

/-! ## Spatial, Stack-Frame, and Placed Call Combinators -/

private theorem r1a_pointsTo32_entails_memRegion (a : BitVec 64) (w : BitVec 32) : (a ↦₃₂ w) ⊢ memRegion a 4 := by
  rw [ProofLib.pointsTo32_eq_pointsToBytes]; exact MainHops.pointsToBytes_to_memRegion a (unpack32 w)
private theorem r1a_pointsTo8_entails_memRegion (a : BitVec 64) (b : BitVec 8) : (a ↦₈ b) ⊢ memRegion a 1 := by
  rw [Path.Helpers.memRegion_1_eq_pointsTo8]; exact Entails.sepExists_intro b
private theorem r1a_memRegion_exists_bytes (n : Nat) :
    ∀ (p : BitVec 64), n ≤ 2 ^ 63 → memRegion p n ⊢ ∃∗ bs : Bytes, ⌜bs.length = n⌝ ∗ (p ↦ₛ bs) := by
  induction n with
  | zero => intro p _; rw [ProofLib.memRegion_zero]; exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.of_eq (pointsToBytes_nil p).symm))
  | succ n ih =>
    intro p hn; rw [show n + 1 = 1 + n by omega, ProofLib.memRegion_split p 1 n (by omega), Path.Helpers.memRegion_1_eq_pointsTo8]
    refine Entails.trans (sepConj_mono_right (ih (p + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0; rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
    have hc : (p ↦₈ b0) ∗ ⌜rest.length = n⌝ ∗ ((p + 1#64) ↦ₛ rest) = ⌜rest.length = n⌝ ∗ (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ rest) := by ac_rfl
    rw [hc]; apply Entails.pure_left; intro hlen
    exact Entails.sepExists_right (b0 :: rest) (Entails.pure_right (by simp [hlen]; omega) (Entails.of_eq (by rw [pointsToBytes_cons])))
private theorem r1a_exists_word64 (bs : Bytes) (hlen : bs.length = 8) : ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦₆₄ w) = (a ↦ₛ bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;> try simp at hlen
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen); subst hnil
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun a => (ProofLib.pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7).symm⟩
private theorem r1a_exists_words32 (bs : Bytes) (hlen : bs.length = 32) : ∃ w0 w1 w2 w3 : BitVec 64, Words32Eq bs w0 w1 w2 w3 := by
  let c0 := bs.take 8; let c1 := (bs.drop 8).take 8; let c2 := (bs.drop 16).take 8; let c3 := bs.drop 24
  obtain ⟨w0, hw0⟩ := r1a_exists_word64 c0 (by simp [c0, hlen]); obtain ⟨w1, hw1⟩ := r1a_exists_word64 c1 (by simp [c1, hlen])
  obtain ⟨w2, hw2⟩ := r1a_exists_word64 c2 (by simp [c2, hlen]); obtain ⟨w3, hw3⟩ := r1a_exists_word64 c3 (by simp [c3, hlen])
  have hbs : bs = c0 ++ (c1 ++ (c2 ++ c3)) := by
    have h1 := (List.take_append_drop 8 bs).symm; have h2 := (List.take_append_drop 8 (bs.drop 8)).symm; have h3 := (List.take_append_drop 8 (bs.drop 16)).symm
    simp only [List.drop_drop] at h2 h3; dsimp only [c0, c1, c2, c3]; rw [← h3, ← h2, ← h1]
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  have hc0 : c0.length = 8 := (by simp [c0, hlen]); have hc1 : c1.length = 8 := (by simp [c1, hlen]); have hc2 : c2.length = 8 := (by simp [c2, hlen])
  rw [hbs, pointsToBytes_append a c0, hw0 a, hc0, pointsToBytes_append (a + BitVec.ofNat 64 8) c1, hw1 (a + 8#64), hc1,
    pointsToBytes_append (a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) c2, hw2 (a + 16#64), hc2]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hw3 (a + 24#64)]
private theorem r1a_addrUpperAt_open (a : BitVec 64) (meG : AddrGhost) :
    addrUpperAt a meG ⊢ ∃∗ w1 : BitVec 64, ⌜w1.setWidth 8 = meG.device⌝ ∗ (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1) := by
  unfold addrUpperAt; refine Entails.trans (sepConj_mono_right (sepConj_mono_right (r1a_memRegion_exists_bytes 7 (a + 9#64) (by decide)))) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
  have hc : (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₈ meG.device) ∗ ⌜bs.length = 7⌝ ∗ ((a + 9#64) ↦ₛ bs) =
    ⌜bs.length = 7⌝ ∗ (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ bs) := by ac_rfl
  rw [hc]; apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩ <;> try simp at hlen
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen); subst hnil
  let w1 : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ meG.device
  have hw1 : w1.setWidth 8 = meG.device := by dsimp [w1]; bv_bits
  have hcell : ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) = ((a + 8#64) ↦₆₄ w1) := by
    have hcons := pointsToBytes_cons (a + 8#64) meG.device [b1, b2, b3, b4, b5, b6, b7]
    have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
    rw [← ha9, ← hcons, ProofLib.pointsToBytes8_eq_pointsTo64]
  refine Entails.sepExists_right w1 (Entails.pure_right hw1 ?_)
  have assocEq : (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) =
    (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ (((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7])) := by ac_rfl
  rw [assocEq, hcell]; exact Entails.refl _
private theorem r1a_addrUpperAt_close (a : BitVec 64) (meG : AddrGhost) (w1 : BitVec 64) (hw1 : w1.setWidth 8 = meG.device) :
    ((a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢ addrUpperAt a meG := by
  unfold addrUpperAt; have hunp : (unpack64 w1).length = 8 := by simp [unpack64]
  rcases hlist : unpack64 w1 with _ | ⟨b0, tail⟩
  · rw [hlist] at hunp; simp at hunp
  have hb0 : b0 = meG.device := by simp only [unpack64] at hlist; injection hlist with hb0_eq _; rw [← hw1, ← hb0_eq]; bv_bits
  subst hb0; have htl : tail.length = 7 := by rw [hlist] at hunp; simpa using hunp
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ProofLib.pointsTo64_eq_pointsToBytes (a + 8#64) w1, hlist, pointsToBytes_cons (a + 8#64), ha9]
  exact sepConj_mono_right (sepConj_mono_right (htl ▸ MainHops.pointsToBytes_to_memRegion (a + 9#64) tail))
private def r1a_peerGhostOf (peerV : AddrV) (w : CallW) : AddrGhost := { name := { cap := w.w0, ptr := w.w1, bytes := peerV.name }, device := peerV.device }
private theorem r1a_pack_peer (A : RustAlloc) (a : BitVec 64) (peerV : AddrV) (w : CallW) :
    ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ ⌜w.w3.setWidth 8 = peerV.device⌝) ⊢
      protocolAddressAt A (r1a_peerGhostOf peerV w) a := by
  rw [protocolAddressAt_eq_parts, M3Helpers.ownedBytes_pure A w.w0 w.w1 w.w2 peerV.name]
  refine Entails.trans (Entails.of_eq (show _ = ⌜w.w2 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w0.toNat ∧ w.w0.toNat < 2 ^ 63 ∧ w.w1 ≠ 0⌝ ∗
    ⌜w.w3.setWidth 8 = peerV.device⌝ ∗ ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ (((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3)) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hw2, _⟩; apply Entails.pure_left; intro hw3
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hup := r1a_addrUpperAt_close (a + 16#64) (r1a_peerGhostOf peerV w) w.w3 hw3
  have hown : addrNameHeap A (r1a_peerGhostOf peerV w) = ownedBytes A w.w0 w.w1 (BitVec.ofNat 64 peerV.name.length) peerV.name := by unfold addrNameHeap ownedBytes r1a_peerGhostOf; simp only [true_and]
  rw [hw2, ← ha24, hown]; exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup))
private theorem r1a_call7_to_memRegion56 (a : BitVec 64) (w : CallW) :
    ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗ ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6)) ⊢ memRegion a 56 := by
  have hs : ∀ k, 8 + k ≤ 56 → ∀ p, memRegion p 8 ∗ memRegion (p + 8#64) k = memRegion p (8 + k) := fun k hk p => (ProofLib.memRegion_split p 8 k (by omega)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))) ?_
  have e40 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 8 = memRegion (a + 40#64) 16 := by simpa [BitVec.add_assoc] using hs 8 (by decide) (a + 40#64)
  have e32 : memRegion (a + 32#64) 8 ∗ memRegion (a + 40#64) 16 = memRegion (a + 32#64) 24 := by simpa [BitVec.add_assoc] using hs 16 (by decide) (a + 32#64)
  have e24 : memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 24 = memRegion (a + 24#64) 32 := by simpa [BitVec.add_assoc] using hs 24 (by decide) (a + 24#64)
  have e16 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 32 = memRegion (a + 16#64) 40 := by simpa [BitVec.add_assoc] using hs 32 (by decide) (a + 16#64)
  have e08 : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 40 = memRegion (a + 8#64) 48 := by simpa [BitVec.add_assoc] using hs 40 (by decide) (a + 8#64)
  rw [e40, e32, e24, e16, e08, hs 48 (by decide) a]; exact Entails.refl _
private theorem r1a_vec22_withString_intro (A : RustAlloc) (a buf w4 w5 : BitVec 64) (hbuf : buf ≠ 0) :
    ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ A.live buf 22 1 ∗ memRegion buf 22) ⊢
      RunDrop.speOwnedAt A a (.withString 1 (by decide)) := by
  have htail : ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 0x20#64) 16 := by
    have hsplit := (ProofLib.memRegion_split (a + 0x20#64) 8 8 (by decide)).symm; have ha40 : a + 0x20#64 + 8#64 = a + 40#64 := by bv_omega
    rw [ha40] at hsplit; rw [← hsplit]; exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have hg : ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ A.live buf 22 1 ∗ memRegion buf 22) =
    (((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗ memRegion buf 22 ∗ ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1) := by ac_rfl
  rw [hg]; refine Entails.trans (sepConj_mono htail (sepConj_mono_left (r1a_memRegion_exists_bytes 22 buf (by decide)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
  have hperm : memRegion (a + 0x20#64) 16 ∗ (⌜bs.length = 22⌝ ∗ (buf ↦ₛ bs)) ∗ ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1) =
    ⌜bs.length = 22⌝ ∗ (a ↦₆₄ speWord 1) ∗ (((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1 ∗ (buf ↦ₛ bs)) ∗ memRegion (a + 0x20#64) 16 := by ac_rfl
  rw [hperm]; apply Entails.pure_left; intro hlen; unfold RunDrop.speOwnedAt
  refine sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right bs (Entails.sepExists_right 22#64 (Entails.sepExists_right buf ?_))))
  unfold vecU8At vecHeader; simp only [show ¬(22#64 : BitVec 64) = 0 from by decide, ↓reduceIte, hlen, show (22#64 : BitVec 64).toNat = 22 from rfl, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hbuf⟩ (Entails.refl _)))
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := (by bv_omega); have ha24 : (a + 8#64) + 16#64 = a + 24#64 := (by bv_omega)
  rw [ha16, ha24]; ac_rfl
private theorem r1a_decode_err_unified (A : RustAlloc) (a : BitVec 64) (ikB : Bytes) (hnotOk : ∀ ik, decodeIdentityKey ikB ≠ .ok ik) :
    ∃ i : Nat, RunDrop.PlainSpeTag i ∧ (speWord i + 2#64 == 0#64) = false ∧ (identityKeyResultAt A a (decodeIdentityKey ikB) ⊢ (a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40) := by
  rcases RecordCodecsBinary.IdentityKeyDecode.Helpers.publicKey_deserialize_cases ikB with ⟨pk, _, hok⟩ | ⟨_, herr⟩ | ⟨t, _, herr⟩ | ⟨n, _, herr⟩
  · exact False.elim (hnotOk ⟨pk⟩ hok)
  · refine ⟨7, by decide, by decide, ?_⟩; rw [herr]; exact Entails.refl _
  · refine ⟨8, by decide, by decide, ?_⟩; rw [herr]; dsimp only [identityKeyResultAt, speAt]
    have hm : memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 = memRegion (a + 8#64) 40 := by simpa [BitVec.add_assoc] using (ProofLib.memRegion_split (a + 8#64) 1 39 (by decide)).symm
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_pointsTo8_entails_memRegion _ _))) (Entails.of_eq (by rw [hm]))
  · refine ⟨9, by decide, by decide, ?_⟩; rw [herr]; dsimp only [identityKeyResultAt, speAt]
    have hm : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 = memRegion (a + 8#64) 40 := by simpa [BitVec.add_assoc] using (ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)).symm
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) (Entails.of_eq (by rw [hm]))

private def r1a_localsBound : List (Nat × Nat × SepProp) → Nat | [] => runLocalBytes | (o, _, _) :: _ => o
private def r1a_localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat | [] => off | (o, n, _) :: cs => r1a_localsEnd (o + n) cs

private def r1a_localsCtx (fsp : BitVec 64) : Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ => memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ runLocalsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ => memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗ r1a_localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

private theorem r1a_locals_focus (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp) (cs₂ : List (Nat × Nat × SepProp)) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) = P ∗ r1a_localsCtx fsp 0 cs₁ o n cs₂ := by
  suffices ∀ off, runLocalsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) = P ∗ r1a_localsCtx fsp off cs₁ o n cs₂ from this 0
  intro off; induction cs₁ generalizing off with
  | nil => simp only [List.nil_append, runLocalsFrom, r1a_localsCtx]; ac_rfl
  | cons c cs₁ ih => rcases c with ⟨o₁, n₁, P₁⟩; simp only [List.cons_append, runLocalsFrom, r1a_localsCtx, ih (o₁ + n₁)]; ac_rfl

private theorem r1a_localsFrom_carve (fsp : BitVec 64) (off o n : Nat) (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o) (hhi : o + n ≤ r1a_localsBound cs) (hbnd : r1a_localsBound cs ≤ runLocalBytes) :
    runLocalsFrom fsp off cs = runLocalsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hlb : runLocalBytes = 0x29f0 := rfl
  have hs1 : memRegion (fsp + BitVec.ofNat 64 off) (r1a_localsBound cs - off) =
      memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ memRegion (fsp + BitVec.ofNat 64 o) (r1a_localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := r1a_localsBound cs - o) (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hs2 : memRegion (fsp + BitVec.ofNat 64 o) (r1a_localsBound cs - o) =
      memRegion (fsp + BitVec.ofNat 64 o) n ∗ memRegion (fsp + BitVec.ofNat 64 (o + n)) (r1a_localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := r1a_localsBound cs - (o + n)) (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil => simp only [r1a_localsBound] at hhi hbnd hs1 hs2; simp only [runLocalsFrom, hs1, hs2]
  | cons c cs' => rcases c with ⟨o', n', P'⟩; simp only [r1a_localsBound] at hhi hbnd hs1 hs2; simp only [runLocalsFrom, hs1, hs2]; ac_rfl

private theorem r1a_locals_carve_region (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1a_localsEnd 0 cs₁ ≤ o := by simp +zeta +zetaDelta only [r1a_localsEnd, init1Cells, List.cons_append, List.append_assoc, List.nil_append]; omega)
    (hhi : o + n ≤ r1a_localsBound cs₂ := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs₂ ≤ runLocalBytes := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega) :
    runLocals fsp (cs₁ ++ cs₂) = runLocals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  suffices ∀ off, r1a_localsEnd off cs₁ ≤ o → runLocalsFrom fsp off (cs₁ ++ cs₂) =
      runLocalsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) from this 0 hlo
  clear hlo; intro off hlo'; induction cs₁ generalizing off with
  | nil => exact r1a_localsFrom_carve fsp off o n cs₂ hlo' hhi hbnd
  | cons c cs₁ ih => rcases c with ⟨o₁, n₁, P₁⟩; simp only [List.cons_append, runLocalsFrom]; rw [ih (o₁ + n₁) hlo']

private theorem r1a_locals_drop_mid (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp) (cs₂ : List (Nat × Nat × SepProp))
    (hP : P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n)
    (hlo : r1a_localsEnd 0 cs₁ ≤ o := by simp +zeta +zetaDelta only [r1a_localsEnd, init1Cells, List.cons_append, List.append_assoc, List.nil_append]; omega)
    (hhi : o + n ≤ r1a_localsBound cs₂ := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs₂ ≤ runLocalBytes := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) ⊢ runLocals fsp (cs₁ ++ cs₂) := by
  rw [r1a_locals_focus fsp cs₁ o n P cs₂, r1a_locals_carve_region fsp cs₁ o n cs₂ hlo hhi hbnd,
    r1a_locals_focus fsp cs₁ o n (memRegion (fsp + BitVec.ofNat 64 o) n) cs₂]; exact sepConj_mono_left hP

private theorem r1a_locals_drop_head (fsp : BitVec 64) (o n : Nat) (P : SepProp) (cs : List (Nat × Nat × SepProp))
    (hP : P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n)
    (hhi : o + n ≤ r1a_localsBound cs := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs ≤ runLocalBytes := by simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc, List.nil_append, runLocalBytes]; omega) :
    runLocals fsp ((o, n, P) :: cs) ⊢ runLocals fsp cs :=
  r1a_locals_drop_mid fsp [] o n P cs hP (Nat.zero_le o) hhi hbnd

private theorem r1a_ownedBytes_zero {A : RustAlloc} {cap ptr len : BitVec 64} {bs : Bytes} (hz : cap = 0) : ownedBytes A cap ptr len bs ⊢ emp := by
  unfold ownedBytes; simp only [hz, ↓reduceIte]; exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
private theorem r1a_ownedBytes_dealloc {A : RustAlloc} {cap ptr len : BitVec 64} {bs : Bytes} (hne : cap ≠ 0) :
    ownedBytes A cap ptr len bs ⊢ ⌜ptr ≠ 0 ∧ LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  rw [M3Helpers.ownedBytes_pure A cap ptr len bs]; apply M3Helpers.entails_pure_elim_left; rintro ⟨_, _, hlt, hptr⟩
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (by intro hz; exact hne (BitVec.eq_of_toNat_eq hz))
  exact M3Helpers.entails_pure_intro_left ⟨hptr, ⟨hpos, ⟨0, rfl⟩, by omega⟩⟩ (M3Helpers.ownedBytes_to_dealloc A hne)
private theorem r1a_addrNameHeap_zero {A : RustAlloc} {g : AddrGhost} (hz : g.name.cap = 0) : addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap; simp only [hz, ↓reduceIte]; exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
private theorem r1a_addrNameHeap_eq_owned {A : RustAlloc} (g : AddrGhost) :
    addrNameHeap A g = ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by unfold addrNameHeap ownedBytes; simp only [true_and]
private theorem r1a_stackAt_split (sp : BitVec 64) {need sub : Nat} (hle : need ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt sp sub = memRegion (sp - BitVec.ofNat 64 sub) (sub - need) ∗ stackAt sp need := by
  have h1 := ProofLib.stackAt_split_bottom sp need (sub - need) (by omega); rwa [Nat.add_sub_of_le hle] at h1
private theorem r1a_sepWPp_exists_pre {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State} {P : α → SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : ∀ x : α, ProofLib.SepWPp prog ret s (P x) Q Qp oom) : ProofLib.SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨x, hx⟩ := hm; exact h x R hx hL
private theorem r1a_sepWPp_pure_pre {p : Prop} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : p → ProofLib.SepWPp prog ret s P Q Qp oom) : ProofLib.SepWPp prog ret s (⌜p⌝ ∗ P) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact h hm.1 R hm.2 hL
private abbrev r1a_sepWPp_pure_left := @r1a_sepWPp_pure_pre
private theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : P ⊢ P') (hw : ProofLib.SepWPp prog ret s P' Q Qp oom) :
    ProofLib.SepWPp prog ret s P Q Qp oom := fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL
private theorem r1a_bind_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (h : let st := s; ProofLib.SepWPp prog ret st P Q Qp oom) : ProofLib.SepWPp prog ret s P Q Qp oom := h
private theorem r1a_false_entails {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q := by rw [← sepConj_emp (⌜False⌝ : SepProp)]; exact Entails.pure_left False.elim
private theorem r1a_memRegion32_eq_words (a : BitVec 64) :
    memRegion a 32 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  apply sepProp_eq_of_entails
  · rw [ProofLib.memRegion_split a 8 24 (by decide), ProofLib.memRegion_split (a + 8#64) 8 16 (by decide), ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))
  · refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 => ?_
    have s1 := (ProofLib.memRegion_split a 8 24 (by decide)).symm; have s2 := (ProofLib.memRegion_split (a + 8#64) 8 16 (by decide)).symm; have s3 := (ProofLib.memRegion_split (a + 16#64) 8 8 (by decide)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3; rw [← s1, ← s2, ← s3]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))
private theorem r1a_readFile_lscro_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots} (hc : RunCalleesPlaced A H B σ) :
    subroutine_ok (runProgPlaced H) (lsρ lsReadFileSym) (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A B.readFile)) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hc.readFile

private theorem r1a_call_lscro [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {g : RunCall} {target lr : BitVec 64} {spec : Spec α} {x : α}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop} (hFs : TraceFsSound (runProgPlaced H))
    (hok : subroutine_ok (runProgPlaced H) target (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = target) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem) (hsp : s.spAligned = true) (hpanic : PanicK g s0 Qp)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜runPanicProp g s0 sf⌝ ∗ anyHeap) (hexit : ∀ code sf, spec.onExit x code s sf ⊢ ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ⊢ runOom s0 sf)
    (hk : ∀ sm : State, sm.pc = s.readReg64 .lr → sm.status = .Running → sm.sp = s.sp → CalleeSavedPreserved s sm → r1a_CodeOk sm.mem →
      s.trace <+: sm.trace → (sm.trace = s.trace → sm.fs.files = s.fs.files) → ProofLib.SepWPp (runProgPlaced H) lr sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    ProofLib.SepWPp (runProgPlaced H) lr s (spec.pre x s ∗ F) Q Qp (runOom s0) := by
  intro R hm hL; have hpre : s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]; rw [show (spec.pre x s ∗ ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F ∗ R) = ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ ((spec.pre x s ∗ F) ∗ R) by ac_rfl, satisfies_pure_sepConj]; exact ⟨hinv, hm⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hok x (F ∗ R) hpc hrun hpre hsp hL; obtain ⟨evs, htr_evs, hfiles_evs⟩ := hFs s sm hsteps
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · have hinv_m : r1a_CodeOk sm.mem := hinv.of_keepsFrozen hsteps.keepsFrozen
    have hm_post : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R := by simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hpost
    have hfiles_eq : sm.trace = s.trace → sm.fs.files = s.fs.files := fun heq => by
      have hevs : evs = [] := List.append_cancel_left (htr_evs.symm.trans (by simp [heq])); subst hevs; exact hfiles_evs NoFsEv.nil
    obtain ⟨sf, hsteps2, hout2⟩ := hk sm hpcm hrunm hspm hcsm hinv_m ⟨evs, htr_evs.symm⟩ hfiles_eq R hm_post (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic x s sm ∗ F) ∗ R := by simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hpost
    have hp_sat : sm.mem ⊨ (⌜runPanicProp g s0 sm⌝ ∗ anyHeap) ∗ (F ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hpan sm)) (by simpa only [sepConj_assoc] using hm_pan)
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp_sat
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, spec.onPanic x s sm ∗ F, hm_pan, hpanic sm (spec.onPanic x s sm ∗ F) hp_sat.1⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj (Satisfies.mono (sepConj_mono_left (hexit code sm))
      (by simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hpost)))
  · have hm_oom1 : sm.mem ⊨ (runOom s0 sm ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hoom sm))) (by simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hpost)
    dsimp only [runOom] at hm_oom1; rw [sepConj_assoc] at hm_oom1; exact False.elim (not_satisfies_false_sepConj hm_oom1)

private theorem r1a_call_run [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {g : RunCall} {target : BitVec 64} {spec : Spec α} {x : α} {retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} (hFs : TraceFsSound (runProgPlaced H))
    (hok : subroutine_ok (runProgPlaced H) target (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = target) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem) (hsp_eq : s.sp = runFsp s0) (hfp_eq : s.readReg64 .fp = s0.sp - 0x60#64)
    (hv_eq : calleeSavedVRegs s = calleeSavedVRegs s0) (hsp0_al : s0.spAligned = true) (hret : s.readReg64 .lr = runPcPlaced retOff) (hpanic : PanicK g s0 Qp)
    (hpre : P ⊢ spec.pre x s ∗ F) (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜runPanicProp g s0 sf⌝ ∗ anyHeap) (hexit : ∀ code sf, spec.onExit x code s sf ⊢ ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ⊢ runOom s0 sf)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm retOff → CalleeSavedPreserved s sm → s.trace <+: sm.trace → (sm.trace = s.trace → sm.fs.files = s.fs.files) →
      ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) :=
  sepWPp_weaken_pre hpre (r1a_call_lscro hFs hok hpc hrun hinv (r1a_spAligned_of_fsp hsp_eq hsp0_al) hpanic hpan hexit hoom fun sm hpcm hrunm hspm hcsm hinvm htr hf =>
    hk sm ⟨hpcm.trans hret, hrunm, hspm.trans hsp_eq, hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp_eq, hinvm, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hv_eq, hsp0_al⟩ hcsm htr hf)

private theorem r1a_call_dealloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {retOff : Nat} {s0 s : State} {sub : Nat}
    {cap ptr len : BitVec 64} {bs : Bytes} {P : SepProp} (F : SepProp) {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hpanic : PanicK g s0 Qp)
    (hstk : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64) (hne : cap ≠ 0) (hpc : s.pc = lsρ lsRustDeallocSymCli) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem)
    (hsp_eq : s.sp = runFsp s0) (hfp_eq : s.readReg64 .fp = s0.sp - 0x60#64) (hv_eq : calleeSavedVRegs s = calleeSavedVRegs s0) (hsp0_al : s0.spAligned = true)
    (hret : s.readReg64 .lr = runPcPlaced retOff) (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap) (hx2 : s.readReg64 .x2 = 1#64)
    (hpre : P = ownedBytes A cap ptr len bs ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ F)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm retOff → CalleeSavedPreserved s sm → sm.trace = s.trace → sm.fs.files = s.fs.files →
      ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm (stackAt (runFsp s0) sub ∗ A.pool ∗ F) Q Qp (runOom s0)) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  rw [hpre]; refine sepWPp_weaken_pre (sepConj_mono_left (r1a_ownedBytes_dealloc hne)) ?_; rw [sepConj_assoc, sepConj_assoc]; apply r1a_sepWPp_pure_pre; rintro ⟨hptr, hlok⟩
  let rem := memRegion (s.sp - BitVec.ofNat 64 sub) (sub - extHookStack)
  refine r1a_call_run (x := (ptr, cap.toNat, 1)) (F := rem ∗ F) (retOff := retOff) (hh.fs (runProgPlaced H) 579) (r1a_dealloc_ok hh) hpc hrun hinv hsp_eq hfp_eq hv_eq hsp0_al hret hpanic
    (by rw [← hsp_eq, r1a_stackAt_split s.sp hstk hsub64]; dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, rem]
        rw [show A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ (memRegion (s.sp - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ stackAt s.sp extHookStack) ∗ A.pool ∗ F =
          (A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack) ∗ (memRegion (s.sp - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F) by ac_rfl]
        exact sepConj_mono_left (Entails.pure_right ⟨hx0, by simp [hx1], by simp [hx2], hlok⟩ (Entails.refl _)))
    (fun _ => by dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]; exact r1a_false_entails) (fun _ _ => Entails.refl _)
    (fun _ => by dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]; exact r1a_false_entails) ?_
  intro sm hbm hcsm _ hfiles; dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]; rw [sepConj_assoc]; apply r1a_sepWPp_pure_pre; intro htrm
  refine sepWPp_weaken_pre ?_ (hk sm hbm hcsm htrm (hfiles htrm)); dsimp only [rem]; rw [hsp_eq, r1a_stackAt_split (runFsp s0) hstk hsub64]; exact Entails.of_eq (by ac_rfl)

private theorem r1a_call_dropSpe [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {retOff : Nat} {s0 s : State} {sub : Nat}
    {k : RunDrop.SpeOwned} {P : SepProp} (F : SepProp) {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hpanic : PanicK g s0 Qp) (hstk : 32 + extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64) (hpc : s.pc = (blkPl_553).base) (hrun : s.status = .Running)
    (hinv : r1a_CodeOk s.mem) (hsp_eq : s.sp = runFsp s0) (hfp_eq : s.readReg64 .fp = s0.sp - 0x60#64) (hv_eq : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hsp0_al : s0.spAligned = true) (hret : s.readReg64 .lr = runPcPlaced retOff) (hx0 : s.readReg64 .x0 = runFsp s0 + 0x4d0#64)
    (hpre : P = RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) k ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ F)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm retOff → CalleeSavedPreserved s sm → sm.trace = s.trace → sm.fs.files = s.fs.files →
      ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ F) Q Qp (runOom s0)) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  rw [hpre]; refine r1a_call_run (x := ⟨runFsp s0 + 0x4d0#64, k⟩) (F := F) (retOff := retOff) (hh.fs (runProgPlaced H) 579) (hdrop sub hstk hsub64)
    hpc hrun hinv hsp_eq hfp_eq hv_eq hsp0_al hret hpanic
    (by rw [← hsp_eq]; dsimp only [RunDrop.dropSpeOwnedSpec]
        rw [show RunDrop.speOwnedAt A (s.sp + 0x4d0#64) k ∗ stackAt s.sp sub ∗ A.pool ∗ F = (RunDrop.speOwnedAt A (s.sp + 0x4d0#64) k ∗ A.pool ∗ stackAt s.sp sub) ∗ F by ac_rfl]
        exact sepConj_mono_left (Entails.pure_right (hsp_eq ▸ hx0) (Entails.refl _)))
    (fun _ => by dsimp only [RunDrop.dropSpeOwnedSpec]; exact r1a_false_entails) (fun _ _ => Entails.refl _)
    (fun _ => by dsimp only [RunDrop.dropSpeOwnedSpec]; exact r1a_false_entails) ?_
  intro sm hbm hcsm _ hfiles; dsimp only [RunDrop.dropSpeOwnedSpec]; rw [sepConj_assoc]; apply r1a_sepWPp_pure_pre; intro htrm
  refine sepWPp_weaken_pre ?_ (hk sm hbm hcsm htrm (hfiles htrm)); rw [hsp_eq]; exact Entails.of_eq (by ac_rfl)

private theorem r1a_panic_step [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hpanic : PanicK g s0 Qp)
    (hpc : s.pc = runPcPlaced 0x2d68) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem)
    (haf : allocFailedIn s0 s) (_htr : s0.trace <+: s.trace) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  rw [runPcPlaced_eq] at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ r1a_herrSym) hinv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [r1a_herrSym, arm64_norm]) (by simp only [arm64_norm, hrun])
  intro _; apply r1a_bind_sepWPp_state; intro s1 R hm1 _hL
  have hext1 : (runProgPlaced H).externAt? s1.pc = some Rust.panicked :=
    (show s1.pc = lsρ r1a_herrSym by simp only [s1, r1a_herrSym, arm64_norm]) ▸ r1a_panic_handle_error hh
  exact ⟨Rust.panicked s1, Steps.step (Step.extern (by simp only [s1, arm64_norm, hrun]) hext1 (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr (Or.inl ⟨rfl, P, hm1, hpanic (Rust.panicked s1) P (Or.inr (by
      unfold allocFailedIn at haf ⊢; rwa [show (Rust.panicked s1).trace = s.trace by simp only [Rust.panicked, s1, arm64_norm]]))⟩)⟩


/-! ## Shared Post-Dispatch Sub-Hops -/

private theorem r1a_peel_pure_pre {P Q R F : SepProp} (h : Q ⊢ R ∗ F) : P ∗ Q ⊢ (P ∗ R) ∗ F := by
  rw [sepConj_assoc]; exact sepConj_mono_right h
private theorem r1a_group2c (a0 a1 c r : SepProp) : a0 ∗ a1 ∗ c ∗ r = ((a0 ∗ a1) ∗ c) ∗ r := by ac_rfl
private theorem r1a_group6c (a0 a1 a2 a3 a4 a5 c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ c ∗ r = ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ c) ∗ r := by ac_rfl
private theorem r1a_group6_4 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 m c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ b0 ∗ b1 ∗ b2 ∗ b3 ∗ m ∗ c ∗ r =
      ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ ((b0 ∗ b1 ∗ b2 ∗ b3) ∗ (m ∗ c))) ∗ r := by ac_rfl
private theorem r1a_group_ok710 (a0 a1 a2 a3 a4 a5 b0 b1 b2 m0 m1 m2 c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ b0 ∗ b1 ∗ b2 ∗ m0 ∗ m1 ∗ m2 ∗ c ∗ r =
      (((a0 ∗ (a1 ∗ a2 ∗ a3 ∗ a4) ∗ a5) ∗ (b0 ∗ b1 ∗ b2 ∗ (m0 ∗ m1 ∗ m2 ∗ c)))) ∗ r := by ac_rfl
private theorem r1a_group4_7 (a0 a1 a2 a3 c b0 b1 b2 b3 b4 b5 b6 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ c ∗ b0 ∗ b1 ∗ b2 ∗ b3 ∗ b4 ∗ b5 ∗ b6 ∗ r =
      ((a0 ∗ a1 ∗ a2 ∗ a3) ∗ c) ∗ ((b0 ∗ b1 ∗ b2 ∗ b3 ∗ b4 ∗ b5 ∗ b6) ∗ r) := by ac_rfl
private theorem r1a_group_mid2 (m0 m1 a c r : SepProp) : m0 ∗ m1 ∗ a ∗ c ∗ r = m0 ∗ m1 ∗ (a ∗ c) ∗ r := by ac_rfl
private theorem r1a_group_mid6 (m0 m1 a0 a1 a2 a3 a4 a5 c r : SepProp) :
    m0 ∗ m1 ∗ a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ c ∗ r = m0 ∗ m1 ∗ ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ c) ∗ r := by ac_rfl
private theorem r1a_group_8b0 (m0 m1 l s p w c o0 o1 o2 o3 o4 o5 o6 o7 o8 fh ah : SepProp) :
    m0 ∗ m1 ∗ l ∗ s ∗ p ∗ w ∗ c ∗ o0 ∗ o1 ∗ o2 ∗ o3 ∗ o4 ∗ o5 ∗ o6 ∗ o7 ∗ o8 ∗ fh ∗ ah =
      (m0 ∗ m1) ∗ l ∗ s ∗ p ∗ ((w ∗ c) ∗ o0 ∗ o1 ∗ o2 ∗ o3 ∗ o4 ∗ o5 ∗ o6 ∗ o7 ∗ o8 ∗ fh) ∗ ah := by ac_rfl
private theorem r1a_group_5c (a0 a1 a2 a3 a4 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ r = (a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4) ∗ r := by ac_rfl
private theorem r1a_group_11_2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0 b1 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ a7 ∗ a8 ∗ a9 ∗ a10 ∗ b0 ∗ b1 ∗ r =
      (a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ a7 ∗ a8 ∗ a9 ∗ a10) ∗ (b0 ∗ b1) ∗ r := by ac_rfl
private theorem r1a_group_6bc (a0 a1 a2 c p i r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ c ∗ p ∗ i ∗ r = (((a0 ∗ a1 ∗ a2) ∗ c) ∗ p ∗ i) ∗ r := by ac_rfl

private theorem r1a_tail_2c54 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV} {dir : Bytes} {w : CallW} {s0 s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x2c54) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx22 : s.readReg64 (.gpr 22#5) = w.w5) (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  have hafter_dir : ∀ s1 : State, InRunPlaced r1a_CodeOk s0 s1 0x2c68 → s1.readReg64 (.gpr 19#5) = g.stores → s0.trace <+: s1.trace → RunHistOk g.i s0 s1 ∧ g.a = some none → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1 (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
    intro s1 hb1 hx19_1 htr1 hhans1
    have hfinish : ∀ s2 : State, InRunPlaced r1a_CodeOk s0 s2 0x2c7c → s2.readReg64 (.gpr 19#5) = g.stores → s0.trace <+: s2.trace → RunHistOk g.i s0 s2 ∧ g.a = some none → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2 (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap)) Q Qp (runOom s0) := by
      intro s2 hb2 hx19_2 htr2 hhans2; refine sepWPp_weaken_pre ?_ (hrej s2 StoresGhost.opened .postDispatch ⟨hb2, hx19_2, (fun h => nomatch h), htr2, hhans2.1, hhans2.2⟩)
      have hrej0 : runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ⊢ runLocals (runFsp s0) [] := Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _)) (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _))
      dsimp only [rejectMem]; refine Entails.trans (Entails.of_eq (show _ = runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ F_heap ∗ ((runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hrej0 (sepConj_mono_left (entails_anyHeap F_heap))) ?_; exact Entails.of_eq (by ac_rfl)
    have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp; rw [runPcPlaced_eq] at hpc1
    by_cases hcap0 : w.w0 = 0#64
    · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c7c) hb1.inv; dsimp only [runProgPlaced, lsProg_579, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]; rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]; (iterate 2 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp1
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hcap0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2; (try simp only [arm64_norm]); (try rw [hsp1]); rw [r1a_group_5c]; (try rw [r1a_memRegion_zero (runFsp s0)])
      change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) _ _ _
      refine sepWPp_weaken_pre ?_ (hfinish _ ⟨by simp only [runPcPlaced_eq, arm64_norm, hcap0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun1], by simp only [arm64_norm, hsp1], by simp only [arm64_norm, hb1.fp], hinv2, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs], hb1.spAligned⟩ (by simp only [arm64_norm, hx19_1]) (by simpa only [arm64_norm] using htr1) (r1a_hist_ans_step hhans1 (by simp only [arm64_norm]) (by simp only [arm64_norm])))
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hcap0))) ?_; rw [emp_sepConj]; exact Entails.of_eq (by ac_rfl)
    · have hne0 : (w.w0 == 0#64) = false := beq_false_of_ne hcap0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv; dsimp only [runProgPlaced, lsProg_579, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]; rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]; (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp1
      apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hne0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv_c; (try simp only [arm64_norm]); (try rw [hsp1]); rw [r1a_group_5c]; (try rw [r1a_memRegion_zero (runFsp s0)])
      change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) _ _ _
      apply r1a_call_dealloc (cap := w.w0) (ptr := w.w1) (len := w.w2) (bs := peerV.name) (F := runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) (retOff := 0x2c7c) hh hpanic hext hsub64 hcap0 (by simp only [lsRustDeallocSymCli, arm64_norm, hne0, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun1]) hinv_c (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, hb1.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs]) hb1.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by ac_rfl)
      intro sm hbm hcsm htrm hfilesm; exact hfinish sm hbm (by simpa only [arm64_norm, hx19_1] using hcsm.1) (by simpa only [htrm, arm64_norm] using htr1) (r1a_hist_ans_step hhans1 (by simpa only [arm64_norm] using htrm) (by simpa only [arm64_norm] using hfilesm))
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; rw [runPcPlaced_eq] at hpc0
  by_cases hcap4 : w.w4 = 0#64
  · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c68) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx24, hcap4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; refine sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hcap4))) ?_; rw [emp_sepConj]
    exact hafter_dir _ ⟨by simp only [runPcPlaced_eq, arm64_norm, hx24, hcap4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun0], by simp only [arm64_norm, hsp0], by simp only [arm64_norm, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx19]) (by simpa only [arm64_norm] using htr) (r1a_hist_ans_step hhans (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  · have hne4 : (w.w4 == 0#64) = false := beq_false_of_ne hcap4
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hx24, hne4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
    intro hinv_c; apply r1a_call_dealloc (cap := w.w4) (ptr := w.w5) (len := w.w6) (bs := dir) (F := runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) (retOff := 0x2c68) hh hpanic hext hsub64 hcap4 (by simp only [lsRustDeallocSymCli, arm64_norm, hx24, hne4, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun0]) hinv_c (by simp only [arm64_norm, hsp0]) (by simp only [arm64_norm, hbase.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm]) (by ac_rfl)
    intro sm hbm hcsm htrm hfilesm; exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (hafter_dir sm hbm (by simpa only [arm64_norm, hx19] using hcsm.1) (by simpa only [htrm, arm64_norm] using htr) (r1a_hist_ans_step hhans (by simpa only [arm64_norm] using htrm) (by simpa only [arm64_norm] using hfilesm)))

private theorem r1a_tail_after_spe [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meG : AddrGhost} {w : CallW} {k : RunDrop.SpeOwned} {s0 s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp) (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x2c30) (hx0 : s.readReg64 .x0 = runFsp s0 + 0x4d0#64) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (runLocals (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) k)] ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  have hext : extHookStack ≤ resStack - runFrame := by omega
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; rw [runPcPlaced_eq] at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_553).base) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, hrun0]); intro hinv_c
  let cs5 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hfoc := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) k) []
  apply r1a_call_dropSpe (F := r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) (retOff := 0x2c34) hh hdrop hpanic hstk32 hsub64 (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, hrun0]) hinv_c (by simp only [arm64_norm, hsp0]) (by simp only [arm64_norm, hbase.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hx0]) (by dsimp only [cs5] at hfoc ⊢; simp only [List.cons_append, List.nil_append] at hfoc; rw [hfoc]; ac_rfl)
  intro s1 hb1 hcs1 htr1 hfiles1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simpa only [arm64_norm, hx19] using hcs1.1
  have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simpa only [arm64_norm, hx20] using hcs1.2.1
  have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [arm64_norm, hx21] using hcs1.2.2.1
  have htr_01 : s0.trace <+: s1.trace := by simpa only [htr1, arm64_norm] using htr
  have hhans1 := r1a_hist_ans_step hhans (by simpa only [arm64_norm] using htr1) (by simpa only [arm64_norm] using hfiles1)
  clear hpc0 hrun0 hsp0 hinv_c hcs1 htr1 hfiles1 hfoc
  have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []).symm
  have hres_split : memRegion g.res runResSize = (∃∗ r0 : BitVec 64, g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by rw [← ProofLib.memRegion_eight g.res]; exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hre : memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) = (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 []) ∗ memRegion g.res runResSize ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap := by ac_rfl
  rw [hre, hfoc', hres_split]; refine sepWPp_weaken_pre (sepConj_mono_left (r1a_locals_drop_mid (runFsp s0) cs5 0x4d0 48 _ [] (Entails.refl _))) ?_; dsimp only [cs5]; simp only [List.append_nil, sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro r0
  have hdrop3 : runLocals (runFsp s0) cs5 ⊢ runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] := Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _)) (Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _)) (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _)))
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp; rw [runPcPlaced_eq] at hpc1
  by_cases hme0 : meG.name.cap = 0#64
  · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c54) hb1.inv; dsimp only [runProgPlaced, lsProg_579, cs5, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]; rw [← hsp1, ← hx20_1]; symm at hsp1 hx20_1; wp_simp_pre only [sepConj_assoc]; (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp1 hx20_1
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21_1, hme0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2; apply r1a_bind_sepWPp_state; intro s2; (try simp only [arm64_norm, hx20_1]); (try rw [hsp1]); rw [r1a_group_11_2]; (try rw [r1a_memRegion_zero (runFsp s0)])
    change ProofLib.SepWPp _ _ s2 (runLocals (runFsp s0) cs5 ∗ ((g.res ↦₆₄ -1#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) _ _ _
    refine sepWPp_weaken_pre ?_ (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap) hh hpanic hrej hext hsub64 ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, hx21_1, hme0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hsp1], by simp only [s2, arm64_norm, hb1.fp], hinv2, by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs], hb1.spAligned⟩ (by simp only [s2, arm64_norm, hx19_1]) (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm]) (by simpa only [s2, arm64_norm] using htr_01) (r1a_hist_ans_step hhans1 (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm])))
    dsimp only [runResAt]; refine Entails.trans (sepConj_mono hdrop3 (sepConj_mono_right (sepConj_mono_left (r1a_addrNameHeap_zero hme0)))) ?_; rw [emp_sepConj]; exact Entails.of_eq (by ac_rfl)
  · have hne_me : (meG.name.cap == 0#64) = false := beq_false_of_ne hme0
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv; dsimp only [runProgPlaced, lsProg_579, cs5, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]; rw [← hsp1, ← hx20_1]; symm at hsp1 hx20_1; wp_simp_pre only [sepConj_assoc]; (iterate 8 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp1 hx20_1
    apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hx21_1, hne_me, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv_c; apply r1a_bind_sepWPp_state; intro sc; (try simp only [arm64_norm, hx20_1]); (try rw [hsp1]); rw [r1a_group_11_2]; (try rw [r1a_memRegion_zero (runFsp s0)])
    change ProofLib.SepWPp _ _ sc (runLocals (runFsp s0) cs5 ∗ ((g.res ↦₆₄ -1#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) _ _ _; rw [r1a_addrNameHeap_eq_owned meG]
    apply r1a_call_dealloc (cap := meG.name.cap) (ptr := meG.name.ptr) (len := BitVec.ofNat 64 meG.name.bytes.length) (bs := meG.name.bytes) (F := runLocals (runFsp s0) cs5 ∗ runResAt A cliWrOk g.res (some none) ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) (retOff := 0x2c54) hh hpanic hext hsub64 hme0 (by simp only [sc, lsRustDeallocSymCli, arm64_norm, hx21_1, hne_me, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [sc, arm64_norm, hrun1]) hinv_c (by simp only [sc, arm64_norm, hsp1]) (by simp only [sc, arm64_norm, hb1.fp]) (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs]) hbase.spAligned (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm, hx21_1]) (by simp only [sc, arm64_norm]) (by dsimp only [runResAt]; ac_rfl)
    intro sm hbm hcsm htrm hfilesm; refine sepWPp_weaken_pre ?_ (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap) hh hpanic hrej hext hsub64 hbm (by simpa only [sc, arm64_norm, hx19_1] using hcsm.1) (by simpa only [sc, arm64_norm] using hcsm.2.2.2.1) (by simpa only [sc, arm64_norm] using hcsm.2.2.2.2.2.1) (by simpa only [htrm, sc, arm64_norm] using htr_01) (r1a_hist_ans_step hhans1 (by simpa only [sc, arm64_norm] using htrm) (by simpa only [sc, arm64_norm] using hfilesm)))
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop3))) ?_; exact Entails.of_eq (by ac_rfl)

private theorem r1a_me_none [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV} {dir : Bytes} {w : CallW} {s0 s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x860) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx22 : s.readReg64 (.gpr 22#5) = w.w5) (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  have hres_split : memRegion g.res runResSize = (∃∗ r0 : BitVec 64, g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by rw [← ProofLib.memRegion_eight g.res]; exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro r0
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; change s.pc = (blkPl_579).base + 2144#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c54) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
  intro hinv1; exact sepWPp_weaken_pre (by dsimp only [runResAt]; exact Entails.of_eq (by ac_rfl)) (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap) hh hpanic hrej hext hsub64 ⟨by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun0], by simp only [arm64_norm, hbase.sp], by simp only [arm64_norm, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx24]) (by simpa only [arm64_norm] using htr) (r1a_hist_ans_step hhans (by simp only [arm64_norm]) (by simp only [arm64_norm])))

/-! ## Arm `R1a` Sub-Hops -/

private def r1a_ownedSlack (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
private theorem r1a_ownedBytes_expose (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) :
    ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs = (ptr ↦ₛ bs) ∗ r1a_ownedSlack A cap ptr bs := by
  unfold ownedBytes r1a_ownedSlack; simp only [true_and]; by_cases hz : cap = 0
  · simp only [hz, BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte, sepConj_emp]; apply sepProp_eq_of_entails
    · rw [← sepConj_emp ⌜_⌝]; apply Entails.pure_left; rintro ⟨hle, hp⟩; have hbs := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle); subst hbs; rw [pointsToBytes_nil, emp_sepConj]; exact Entails.pure_right ⟨Nat.zero_le _, hp⟩ (Entails.refl _)
    · rw [sepConj_comm]; apply Entails.pure_left; rintro ⟨hle, hp⟩; have hbs := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle); subst hbs; rw [pointsToBytes_nil, ← sepConj_emp (⌜_⌝ : SepProp)]; exact Entails.pure_right ⟨Nat.zero_le _, hp⟩ (Entails.refl _)
  · simp only [hz, ↓reduceIte]; ac_rfl
private theorem r1a_readFile_post_facts [LibsignalPlacement] {S : RunSem} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {s0 s_disp s sm : State} {r : Except Unit Bytes}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp) (hcall : g.c = .init peerV dir)
    (hs_tr : s0.trace <+: s.trace) (hs_fs : s.fs.files = runFiles g.i) (hs_out : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hfiles_eq : sm.trace = s.trace → sm.fs.files = s.fs.files) (hpost : r = cliIo.rd s.fs.files (dir ++ [0x2f#8] ++ utf8 "identity-key") ∧ sm.trace = s.trace) :
    s0.trace <+: sm.trace ∧ (r = .error () → RunHistOk g.i s0 sm ∧ g.a = some none) ∧
      (∀ ikB, r = .ok ikB → cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB ∧ sm.fs.files = runFiles g.i ∧ ProcessOutcome.traceStreamBytes .stdout sm.trace = []) := by
  rcases hpost with ⟨hr, htr_eq⟩; exact ⟨htr_eq ▸ hs_tr, fun he0 => ⟨⟨(hfiles_eq htr_eq).trans hs_fs, htr_eq ▸ hs_out⟩, r1a_reject_of_read_err he hd hcall (hs_fs ▸ hr.symm.trans he0)⟩, fun ikB hik => ⟨hs_fs ▸ hr.symm.trans hik, (hfiles_eq htr_eq).trans hs_fs, htr_eq ▸ hs_out⟩⟩
private theorem r1a_memRegion48_words (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split a 8 40 (by decide), ProofLib.memRegion_split (a + 8#64) 8 32 (by decide), ProofLib.memRegion_split (a + 8#64 + 8#64) 8 24 (by decide), ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide), ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))
private theorem r1a_words5_to_memRegion40 (a w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 8#64) 40 := by
  have hs : ∀ k, 8 + k ≤ 40 → ∀ p, memRegion p 8 ∗ memRegion (p + 8#64) k = memRegion p (8 + k) := fun k hk p => (ProofLib.memRegion_split p 8 k (by omega)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))) ?_
  have e32 : memRegion (a + 32#64) 8 ∗ memRegion (a + 40#64) 8 = memRegion (a + 32#64) 16 := by simpa [BitVec.add_assoc] using hs 8 (by decide) (a + 32#64)
  have e24 : memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 = memRegion (a + 24#64) 24 := by simpa [BitVec.add_assoc] using hs 16 (by decide) (a + 24#64)
  have e16 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 = memRegion (a + 16#64) 32 := by simpa [BitVec.add_assoc] using hs 24 (by decide) (a + 16#64)
  have e08 : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 = memRegion (a + 8#64) 40 := by simpa [BitVec.add_assoc] using hs 32 (by decide) (a + 8#64)
  rw [e32, e24, e16, e08]; exact Entails.refl _
private theorem r1a_words6_to_memRegion48 (a d0 d1 d2 d3 d4 d5 : BitVec 64) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗ ((a + 40#64) ↦₆₄ d5) ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split a 8 40 (by decide)]; exact sepConj_mono (pointsTo64_entails_memRegion _ _) (r1a_words5_to_memRegion40 a d1 d2 d3 d4 d5)
private theorem r1a_buf22_reassoc (buf d0 d1 : BitVec 64) : ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) ⊢ ∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) := by
  have h16 := (ProofLib.memRegion_split buf 8 8 (by decide)).symm; have h22 := (ProofLib.memRegion_split buf 16 6 (by decide)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion buf d0) (sepConj_mono_left (pointsTo64_entails_memRegion (buf + 8#64) d1))) ?_
  rw [← sepConj_assoc, h16, h22, ProofLib.memRegion_split buf 14 8 (by decide), ProofLib.memRegion_eight (buf + 14#64), sepExists_sepConj_right]; exact Entails.refl _
private theorem r1a_buf22_merge (buf d2 : BitVec 64) : (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ⊢ memRegion buf 22 := by
  rw [show (22 : Nat) = 14 + 8 from rfl, ProofLib.memRegion_split buf 14 8 (by decide)]; exact sepConj_mono_right (pointsTo64_entails_memRegion (buf + 14#64) d2)

private theorem r1a_free_path_6e0 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {s0 s : State} {sub : Nat} {pathCap pathPtr : BitVec 64} {pathBs : Bytes} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hpanic : PanicK g s0 Qp) (hstk : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64) (hne : pathCap ≠ 0) (hbase : InRunPlaced r1a_CodeOk s0 s 0x6e0) (hx1 : s.readReg64 .x1 = pathCap) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm 0x6f4 → sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) → sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) → sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) → sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) → sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) → sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) → sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) → sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) → sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) → sm.trace = s.trace → sm.fs.files = s.fs.files → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm (stackAt (runFsp s0) sub ∗ A.pool ∗ F) Q Qp (runOom s0)) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ F) Q Qp (runOom s0) := by
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; change s.pc = (blkPl_579).base + 1760#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0]); intro hinv_c
  apply r1a_call_dealloc (cap := pathCap) (ptr := pathPtr) (len := BitVec.ofNat 64 pathBs.length) (bs := pathBs) (F := F) (retOff := 0x6f0) hh hpanic hstk hsub64 hne (by simp only [lsRustDeallocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0]) hinv_c (by simp only [arm64_norm, hbase.sp]) (by simp only [arm64_norm, hbase.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm]) (by ac_rfl)
  intro s1 hb1 hcs1 htr1 hfiles1; have hx26_1 : s1.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 12#5) := by simpa only [arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; change s1.pc = (blkPl_579).base + 1776#64 at hpc1
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hb1.inv; dsimp only [runProgPlaced, lsProg_579]; (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2
  exact hk _ ⟨by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun1], by simp only [arm64_norm, hb1.sp], by simp only [arm64_norm, hb1.fp], hinv2, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs], hb1.spAligned⟩ (by simp only [arm64_norm, hx26_1]) (by simpa only [arm64_norm] using hcs1.1) (by simpa only [arm64_norm] using hcs1.2.1) (by simpa only [arm64_norm] using hcs1.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.2.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1) (by simpa only [arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1) (by simpa only [arm64_norm] using htr1) (by simpa only [arm64_norm] using hfiles1)

private theorem r1a_spe_pack_plain [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meG : AddrGhost} {w : CallW} {i : Nat} {s0 s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hi : RunDrop.PlainSpeTag i) (hbase : InRunPlaced r1a_CodeOk s0 s 0x2bf0)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗
        addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  let cs5 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hfoc := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
  (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ∗ _) _ _ _
  rw [hfoc]; refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro s0w; apply r1a_sepWPp_exists_pre; intro s1w; apply r1a_sepWPp_exists_pre; intro s2w; apply r1a_sepWPp_exists_pre; intro s3w; apply r1a_sepWPp_exists_pre; intro s4w; apply r1a_sepWPp_exists_pre; intro s5w
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; rw [runPcPlaced_eq] at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c30) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  (iterate 16 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  symm at hsp0; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm, hx12]); (try rw [hsp0]); rw [r1a_group6c]
  refine sepWPp_weaken_pre ?_ (r1a_tail_after_spe (peerV := peerV) (dir := dir) (meG := meG) (w := w) (k := .plain i hi) (F_heap := F_heap) hh hdrop hpanic hrej hstk32 hsub64 ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0], by simp only [arm64_norm, s1, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, s1, hsp0]) (by simp only [arm64_norm, s1, hx19]) (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1, hx21]) (by simpa only [arm64_norm, s1] using htr) (r1a_hist_ans_step hhans (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])))
  have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) (.plain i hi)) []).symm
  change _ ⊢ runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) (.plain i hi))]) ∗ _
  rw [← hfoc']; dsimp only [RunDrop.speOwnedAt]; have hw40 := r1a_words5_to_memRegion40 (runFsp s0 + 0x4d0#64); simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hw40 ⊢
  exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (hw40 _ _ _ _ _)))

private theorem r1a_decode_err [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV} {dir ikB : Bytes} {meG : AddrGhost} {w : CallW} {ikCap ikPtr : BitVec 64} {i : Nat} {s0 s : State} {resStack : Nat}
    {F_heap : SepProp} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hi : RunDrop.PlainSpeTag i) (hbase : InRunPlaced r1a_CodeOk s0 s 0x8f0)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx25 : s.readReg64 (.gpr 25#5) = ikCap) (hx27 : s.readReg64 (.gpr 27#5) = ikPtr)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗
        ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  have hext : extHookStack ≤ resStack - runFrame := by omega
  let cs5 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hf4d0 := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
  (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ∗ _) _ _ _
  rw [hf4d0]; refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro d0; apply r1a_sepWPp_exists_pre; intro d1; apply r1a_sepWPp_exists_pre; intro d2; apply r1a_sepWPp_exists_pre; intro d3; apply r1a_sepWPp_exists_pre; intro d4; apply r1a_sepWPp_exists_pre; intro d5
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 2288#64 at hpc0
  by_cases hik0 : ikCap = 0#64
  · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0xcdc) hbase.inv
    dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx25, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6c]
    have hb1 : InRunPlaced r1a_CodeOk s0 s1 0xcdc := ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hx25, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0], by simp only [arm64_norm, s1, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs], hbase.spAligned⟩
    have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; change s1.pc = (blkPl_579).base + 3292#64 at hpc1
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
    (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2
    refine sepWPp_weaken_pre ?_ (r1a_spe_pack_plain (peerV := peerV) (dir := dir) (meG := meG) (w := w) (F_heap := F_heap) hh hdrop hpanic hrej hstk32 hsub64 hi ⟨by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun1], by simp only [arm64_norm, hb1.sp], by simp only [arm64_norm, hb1.fp], hinv2, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs], hb1.spAligned⟩ (by simp only [arm64_norm, s1, hx12]) (by simp only [arm64_norm, s1, hx19]) (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1, hx21]) (by simpa only [arm64_norm, s1] using htr) (r1a_hist_ans_step hhans (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])))
    have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) ⊢ memRegion (runFsp s0 + 0x4d0#64) 48 := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) d0 d1 d2 d3 d4 d5
    refine Entails.trans (sepConj_mono (sepConj_mono_left hw48) (sepConj_mono_left (r1a_ownedBytes_zero hik0))) ?_; rw [← hf4d0, emp_sepConj]; exact Entails.refl _
  · have hne_ik : (ikCap == 0#64) = false := beq_false_of_ne hik0
    have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) ⊢ memRegion (runFsp s0 + 0x4d0#64) 48 := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) d0 d1 d2 d3 d4 d5
    have h32 : memRegion (runFsp s0 + 0x198#64) 32 = (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64, ((runFsp s0 + 0x198#64) ↦₆₄ t0) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1) ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ t2) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3)) := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x198#64)
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv
    have hctx_open : r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] = memRegion (runFsp s0 + 0x198#64) 32 ∗ memRegion (runFsp s0) 0x198 ∗ r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 [] := by
      dsimp only [cs5, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; have hs := ProofLib.memRegion_split (runFsp s0 + 0#64) 0x198 32 (by decide)
      simp only [BitVec.add_zero, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at hs ⊢; rw [hs]; ac_rfl
    rw [hctx_open, h32]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro t0; apply SepWP.exists_left; intro t1; apply SepWP.exists_left; intro t2; apply SepWP.exists_left; intro t3
    dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 24 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0; apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hx25, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun0]); intro hinv_c; apply r1a_bind_sepWPp_state; intro sc; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6_4]
    have hex4 : ∀ (a b c d : BitVec 64), ((runFsp s0 + 0x198#64) ↦₆₄ a) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ b) ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ c) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ d) ⊢ ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64, ((runFsp s0 + 0x198#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ q1) ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ q3) := fun a b c d => Entails.sepExists_right a (Entails.sepExists_right b (Entails.sepExists_right c (Entails.sepExists_right d (Entails.refl _))))
    refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (hex4 _ _ _ _)))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro t0'; apply r1a_sepWPp_exists_pre; intro t1'; apply r1a_sepWPp_exists_pre; intro t2'; apply r1a_sepWPp_exists_pre; intro t3'
    apply r1a_call_dealloc (cap := ikCap) (ptr := ikPtr) (len := BitVec.ofNat 64 ikB.length) (bs := ikB) (F := (((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ∗ (((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3')) ∗ memRegion (runFsp s0) 0x198 ∗ r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 [] ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap)
      (retOff := 0x950) hh hpanic hext hsub64 hik0 (by simp only [lsRustDeallocSymCli, arm64_norm, sc, hx25, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, sc, hrun0]) hinv_c (by simp only [arm64_norm, sc, hsp0]) (by simp only [arm64_norm, sc, hbase.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, sc, hbase.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, sc, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, sc, hx27]) (by simp only [arm64_norm, sc, hx25]) (by simp only [arm64_norm, sc]) (by ac_rfl)
    intro sm hbm hcsm htrm hfilesm
    have hx19_m : sm.readReg64 (.gpr 19#5) = g.res := by simpa only [arm64_norm, sc, hx20] using hcsm.1
    have hx20_m : sm.readReg64 (.gpr 20#5) = meG.name.cap := by simpa only [arm64_norm, sc, hx21] using hcsm.2.1
    have hx22_m : sm.readReg64 (.gpr 22#5) = g.stores := by simpa only [arm64_norm, sc, hx19] using hcsm.2.2.2.1
    have hx27_m : sm.readReg64 (.gpr 27#5) = speWord i := by simpa only [arm64_norm, sc, hx12] using hcsm.2.2.2.2.2.2.2.2.1
    have htr_0m : s0.trace <+: sm.trace := by simpa only [htrm, arm64_norm, sc] using htr
    have hhans_m := r1a_hist_ans_step hhans (by simpa only [arm64_norm, sc] using htrm) (by simpa only [arm64_norm, sc] using hfilesm)
    have hpcm := hbm.pc; have := hbm.spAligned_cur; have hrunm := hbm.run; have hspm := hbm.sp; change sm.pc = (blkPl_579).base + 2384#64 at hpcm
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hbm.inv; try dsimp only [runProgPlaced, lsProg_579]
    rw [← hspm]; symm at hspm; wp_simp_pre only [sepConj_assoc]; (iterate 13 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hspm; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrunm]); intro hinv2; (try simp only [arm64_norm]); (try rw [hspm])
    refine sepWPp_weaken_pre ?_ (r1a_spe_pack_plain (peerV := peerV) (dir := dir) (meG := meG) (w := w) (F_heap := F_heap) hh hdrop hpanic hrej hstk32 hsub64 hi ⟨by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrunm], by simp only [arm64_norm, hspm], by simp only [arm64_norm, hbm.fp], hinv2, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbm.vregs], hbm.spAligned⟩ (by simp only [arm64_norm, hx27_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simpa only [arm64_norm] using htr_0m) (r1a_hist_ans_step hhans_m (by simp only [arm64_norm]) (by simp only [arm64_norm])))
    have hm32 : ((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3') ⊢ memRegion (runFsp s0 + 0x198#64) 32 := by
      rw [h32]; exact Entails.sepExists_right t0' (Entails.sepExists_right t1' (Entails.sepExists_right t2' (Entails.sepExists_right t3' (Entails.refl _))))
    refine Entails.trans (Entails.of_eq (show _ = (((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ∗ ((((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3')) ∗ memRegion (runFsp s0) 0x198 ∗ r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 []) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hw48 (sepConj_mono_left (sepConj_mono_left hm32))) ?_; rw [← hctx_open, ← sepConj_assoc, ← hf4d0]; exact Entails.refl _


set_option maxHeartbeats 800000 in
private theorem r1a_read_err [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerV : AddrV}
    {dir pathBs : Bytes} {meG : AddrGhost} {w : CallW} {pathCap pathPtr : BitVec 64} {s0 s : State} {resStack : Nat} {F_heap : SepProp}
    {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x878) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx23 : s.readReg64 (.gpr 23#5) = -1#64) (hx24 : s.readReg64 (.gpr 24#5) = w.w4)
    (hx26 : s.readReg64 (.gpr 26#5) = pathPtr) (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
          (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
          (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48),
          (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)] ∗
        ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗
        ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  let sub := resStack - runFrame; have hext : extHookStack ≤ sub := by omega
  let rem := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack)
  let csErr := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
    (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
    (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48), (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
  let restMem := runLocals (runFsp s0) csErr ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ addrNameHeap A meG ∗
    ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 2168#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hbase.inv; dsimp only [runProgPlaced, lsProg_579]
  (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustNoAllocShimSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0]); intro hinv_s
  refine r1a_call_run (x := ()) (F := rem ∗ A.pool ∗ restMem) (retOff := 0x87c) (hh.fs (runProgPlaced H) 579) (r1a_shim_ok hh)
    (by simp only [lsRustNoAllocShimSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0]) hinv_s (by simp only [arm64_norm, hsp0])
    (by simp only [arm64_norm, hbase.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs]) hbase.spAligned
    (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) hpanic
    (by have hs : stackAt (runFsp s0) sub = rem ∗ stackAt (runFsp s0) extHookStack := r1a_stackAt_split (runFsp s0) hext hsub64
        dsimp only [withStack, sessionShimSpec, sub, restMem, csErr] at hs ⊢; rw [hs]; (try simp only [arm64_norm]); (try rw [hsp0]); exact Entails.of_eq (by ac_rfl))
    (fun _ => by dsimp only [withStack, sessionShimSpec]; exact r1a_false_entails) (fun _ _ => Entails.refl _)
    (fun _ => by dsimp only [withStack, sessionShimSpec]; exact r1a_false_entails) ?_
  intro s1 hb1 hcs1 _ hfiles1; dsimp only [withStack, sessionShimSpec]; rw [sepConj_assoc]; apply r1a_sepWPp_pure_pre; intro htr1; (try simp only [arm64_norm]); (try rw [hsp0])
  have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simpa only [arm64_norm, hx19] using hcs1.1
  have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simpa only [arm64_norm, hx20] using hcs1.2.1
  have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [arm64_norm, hx21] using hcs1.2.2.1
  have hx23_1 : s1.readReg64 (.gpr 23#5) = -1#64 := by simpa only [arm64_norm, hx23] using hcs1.2.2.2.2.1
  have hx24_1 : s1.readReg64 (.gpr 24#5) = w.w4 := by simpa only [arm64_norm, hx24] using hcs1.2.2.2.2.2.1
  have hx26_1 : s1.readReg64 (.gpr 26#5) = pathPtr := by simpa only [arm64_norm, hx26] using hcs1.2.2.2.2.2.2.2.1
  have htr_01 : s0.trace <+: s1.trace := by simpa only [htr1, arm64_norm] using htr
  have hhans1 := r1a_hist_ans_step hhans (by simpa only [arm64_norm] using htr1) (by simpa only [arm64_norm] using hfiles1 htr1)
  clear hpc0 hrun0 hsp0 hinv_s hcs1 htr1 hfiles1; have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp; change s1.pc = (blkPl_579).base + 2172#64 at hpc1
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustAllocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun1]); intro hinv_a
  refine r1a_call_run (x := (22, 1)) (F := rem ∗ restMem) (retOff := 0x888) (hh.fs (runProgPlaced H) 579) (r1a_alloc_ok hh) (by simp only [lsRustAllocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun1]) hinv_a (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, hb1.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) hpanic
    (by dsimp only [rustAllocSpecWithStack, rustAllocSpec]; (try simp only [arm64_norm]); (try rw [hsp1]); exact Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.pure_right ⟨by simp only [arm64_norm], ⟨0, rfl⟩, by decide⟩ (Entails.refl _)))
    (fun _ => by dsimp only [rustAllocSpecWithStack, rustAllocSpec]; exact r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => by dsimp only [rustAllocSpecWithStack, rustAllocSpec]; exact r1a_false_entails) ?_
  intro s2 hb2 hcs2 _ hfiles2; dsimp only [rustAllocSpecWithStack, rustAllocSpec]; (try simp only [arm64_norm]); (try rw [hb1.sp])
  have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by simpa only [arm64_norm, hx19_1] using hcs2.1
  have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by simpa only [arm64_norm, hx20_1] using hcs2.2.1
  have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [arm64_norm, hx21_1] using hcs2.2.2.1
  have hx23_2 : s2.readReg64 (.gpr 23#5) = -1#64 := by simpa only [arm64_norm, hx23_1] using hcs2.2.2.2.2.1
  have hx24_2 : s2.readReg64 (.gpr 24#5) = w.w4 := by simpa only [arm64_norm, hx24_1] using hcs2.2.2.2.2.2.1
  have hx26_2 : s2.readReg64 (.gpr 26#5) = pathPtr := by simpa only [arm64_norm, hx26_1] using hcs2.2.2.2.2.2.2.2.1
  clear hpc1 hrun1 hsp1 hinv_a hcs2; set buf := s2.readReg64 .x0
  by_cases hbuf0 : buf = 0#64
  · simp only [show (buf = 0) ↔ True from iff_of_true hbuf0 trivial, ↓reduceIte]
    have hp_oom (P1 P2 P3 P4 : SepProp) : P1 ∗ P2 ∗ P3 ∗ P4 = P3 ∗ (P1 ∗ P2 ∗ P4) := by ac_rfl
    rw [hp_oom]; apply r1a_sepWPp_pure_pre; intro htr_oom
    have haf0 : allocFailedIn s0 s2 := allocFailedIn_of_prefix htr_01 (r1a_allocFailedIn_of_append htr_oom)
    have htr_02 : s0.trace <+: s2.trace := htr_01.trans ⟨[allocFailedEvent], htr_oom.symm⟩
    have hpc2 := hb2.pc; have := hb2.spAligned_cur; have hrun2 := hb2.run; change s2.pc = (blkPl_579).base + 2184#64 at hpc2
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2d68) hb2.inv; try dsimp only [runProgPlaced, lsProg_579]
    (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, buf, hbuf0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun2]); intro hinv3
    exact r1a_panic_step hh hpanic (by simp only [runPcPlaced_eq, arm64_norm, buf, hbuf0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun2]) hinv3 (by unfold allocFailedIn at haf0 ⊢; simpa only [arm64_norm] using haf0) (by simpa only [arm64_norm] using htr_02)
  · have hbuf_be : (buf == 0#64) = false := beq_false_of_ne hbuf0; simp only [show ¬(buf = 0) from hbuf0, ↓reduceIte]
    have hp_ok (P1 P2 P3 P4 P5 P6 : SepProp) : P1 ∗ P2 ∗ (P3 ∗ P4 ∗ P5) ∗ P6 = P3 ∗ ((P4 ∗ (P5 ∗ P1 ∗ P2)) ∗ P6) := by ac_rfl
    rw [hp_ok]; apply r1a_sepWPp_pure_pre; rintro ⟨_, htr2⟩
    have htr_02 : s0.trace <+: s2.trace := by simpa only [htr2, arm64_norm] using htr_01
    have hhans2 := r1a_hist_ans_step hhans1 (by simpa only [arm64_norm] using htr2) (by simpa only [arm64_norm] using hfiles2 htr2)
    have hbuf22 : memRegion buf 22 = (∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, (buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) := by
      have h1 : memRegion buf 22 = memRegion buf 8 ∗ (memRegion (buf + 8#64) 8 ∗ memRegion (buf + 16#64) 6) := by
        rw [show (22 : Nat) = 8 + 14 from rfl, ProofLib.memRegion_split buf 8 14 (by decide), show (14 : Nat) = 8 + 6 from rfl, ProofLib.memRegion_split (buf + 8#64) 8 6 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [h1, ProofLib.memRegion_eight buf, sepExists_sepConj_left]; congr 1; funext b0
      rw [ProofLib.memRegion_eight (buf + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
    rw [hbuf22]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro b0; apply r1a_sepWPp_exists_pre; intro b1 R hm2 hL2
    have hm2_ro := r1a_rodata_unreadable_intro hb2.inv hm2; let ptrUnr := lsρ r1a_unreadSym
    refine (?_ : ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2 ((ptrUnr ↦ᵣ utf8 "file could not be read") ∗ ((A.live buf 22 1 ∗ (((buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) ∗ A.pool ∗ stackAt (runFsp s0) extHookStack)) ∗ (rem ∗ restMem))) Q Qp (runOom s0)) R (Satisfies.of_eq hm2_ro (by ac_rfl)) hL2
    clear R hm2 hm2_ro hL2
    have hpc2 := hb2.pc; have := hb2.spAligned_cur; have hrun2 := hb2.run; have hsp2 := hb2.sp; change s2.pc = (blkPl_579).base + 2184#64 at hpc2
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x8b0) hb2.inv; try dsimp only [runProgPlaced, lsProg_579]
    (wp_step; conv => arg 3; simp (config := { zeta := false }) only [show s2.readReg64 (Reg.gpr 0#5) = buf from rfl, hbuf_be, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (iterate 2 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    have hunr_len : (utf8 "file could not be read").length = 22 := by decide +kernel
    apply SepWP.step_ldrSimd128 (by simp only [arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]; rfl) (by simp only [arm64_norm, hrun2]) (by wp_norm_lhs) rfl (by show _ = (ptrUnr, none); simp only [ptrUnr, lsρ, lsmpl, r1a_unreadSym, evalAddrMode, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) rfl (SepLoad64.of_pointsToBytesRO rfl (off := 0) (by rw [hunr_len]; decide) (by simp)) (SepLoad64.of_pointsToBytesRO rfl (off := 8) (by rw [hunr_len]; decide) rfl) rfl
    simp (config := { zeta := false }) only [applyWriteback, State.pc_setPC, State.setPC_setPC, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.step_ldur64 (by simp only [arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]; rfl) (by simp only [arm64_norm, hrun2]) (by wp_norm_lhs) rfl (by show _ = (ptrUnr + 14#64, none); simp only [ptrUnr, lsρ, lsmpl, r1a_unreadSym, evalAddrMode, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (SepLoad64.of_pointsToBytesRO rfl (off := 14) (by rw [hunr_len]) rfl) rfl
    simp (config := { zeta := false }) only [applyWriteback, State.pc_setPC, State.setPC_setPC, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
    have hbuf_rw : s2.readReg64 (Reg.gpr 0#5) = buf := rfl; rw [← hbuf_rw]; symm at hbuf_rw; wp_simp_pre only [sepConj_assoc]
    (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hbuf_rw; rw [hbuf_rw]
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, buf, hbuf_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun2])
    intro hinv3; apply r1a_bind_sepWPp_state; intro s3
    have hb3 : InRunPlaced r1a_CodeOk s0 s3 0x8b0 := ⟨by simp only [runPcPlaced_eq, arm64_norm, s3, buf, hbuf_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s3, hrun2], by simp only [arm64_norm, s3, hsp2], by simp only [arm64_norm, s3, hb2.fp], hinv3, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s3, hb2.vregs], hbase.spAligned⟩
    have hx0_3 : s3.readReg64 .x0 = buf := by simp only [arm64_norm, s3, buf]
    have hx12_3 : s3.readReg64 (.gpr 12#5) = speWord 1 := by simp only [arm64_norm, s3]; decide
    have hx19_3 : s3.readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, s3, hx19_2]
    have hx20_3 : s3.readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, s3, hx20_2]
    have hx21_3 : s3.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, s3, hx21_2]
    have hx22_3 : s3.readReg64 (.gpr 22#5) = 22#64 := by simp only [arm64_norm, s3]
    have hx23_3 : s3.readReg64 (.gpr 23#5) = -1#64 := by simp only [arm64_norm, s3, hx23_2]
    have hx24_3 : s3.readReg64 (.gpr 24#5) = w.w4 := by simp only [arm64_norm, s3, hx24_2]
    have hx25_3 : s3.readReg64 (.gpr 25#5) = 22#64 := by simp only [arm64_norm, s3]
    have hx26_3 : s3.readReg64 (.gpr 26#5) = pathPtr := by simp only [arm64_norm, s3, hx26_2]
    have hx27_3 : s3.readReg64 (.gpr 27#5) = buf := by simp only [arm64_norm, s3, buf]
    have htr_03 : s0.trace <+: s3.trace := by simpa only [arm64_norm, s3] using htr_02
    have hhans3 := r1a_hist_ans_step (s2 := s3) hhans2 (by simp only [arm64_norm, s3]) (by simp only [arm64_norm, s3])
    have hstk_back : rem ∗ stackAt (runFsp s0) extHookStack = stackAt (runFsp s0) sub := (r1a_stackAt_split (runFsp s0) hext hsub64).symm
    refine sepWPp_weaken_pre (?_ : _ ⊢ (∃∗ b2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ b2)) ∗ A.live buf 22 1 ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ restMem ∗ anyHeap) ?_
    · refine Entails.trans (Entails.of_eq (show _ = ((buf ↦₆₄ _) ∗ ((buf + 8#64) ↦₆₄ _) ∗ memRegion (buf + 16#64) 6) ∗ A.live buf 22 1 ∗ (rem ∗ stackAt (runFsp s0) extHookStack) ∗ A.pool ∗ restMem ∗ (_ ↦ᵣ utf8 "file could not be read") by ac_rfl)) ?_
      rw [hstk_back]; exact sepConj_mono (r1a_buf22_reassoc buf _ _) (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))))
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro b2
    have hafter_free : ∀ s4 : State, InRunPlaced r1a_CodeOk s0 s4 0x6f4 → s4.readReg64 (.gpr 12#5) = speWord 1 → s4.readReg64 (.gpr 19#5) = g.stores → s4.readReg64 (.gpr 20#5) = g.res → s4.readReg64 (.gpr 21#5) = meG.name.cap → s4.readReg64 (.gpr 22#5) = 22#64 → s4.readReg64 (.gpr 23#5) = -1#64 → s4.readReg64 (.gpr 24#5) = w.w4 → s4.readReg64 (.gpr 25#5) = 22#64 → s4.readReg64 (.gpr 27#5) = buf → s0.trace <+: s4.trace → (RunHistOk g.i s0 s4 ∧ g.a = some none) → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s4 (memRegion buf 22 ∗ A.live buf 22 1 ∗ runLocals (runFsp s0) csErr ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ (F_heap ∗ anyHeap)) Q Qp (runOom s0) := by
      intro s4 hb4 hx12_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx27_4 htr_04 hhans4
      let csPre := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr)]
      let csMid := [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      have hdrop1750 : runLocals (runFsp s0) csErr ⊢ runLocals (runFsp s0) (csPre ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csMid) := r1a_locals_drop_mid (runFsp s0) (csPre ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csMid) 0x1750 8 _ [] (pointsTo64_entails_memRegion _ _)
      refine sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop1750))) ?_
      rw [r1a_locals_focus (runFsp s0) csPre 0x1c0 8 (memRegion (runFsp s0 + 0x1c0#64) 8) csMid, ProofLib.memRegion_eight (runFsp s0 + 0x1c0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro c1c0
      have hpc4 := hb4.pc; have := hb4.spAligned_cur; have hrun4 := hb4.run; have hsp4 := hb4.sp; change s4.pc = (blkPl_579).base + 1780#64 at hpc4
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x8c0) hb4.inv; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp4]; symm at hsp4; wp_simp_pre only [sepConj_assoc]
      (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp4; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx23_4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun4])
      intro hinv5; apply r1a_bind_sepWPp_state; intro s5; (try simp only [arm64_norm, hx24_4]); (try rw [hsp4])
      have hb5 : InRunPlaced r1a_CodeOk s0 s5 0x8c0 := ⟨by simp only [runPcPlaced_eq, arm64_norm, s5, hx23_4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s5, hrun4], by simp only [arm64_norm, s5, hsp4], by simp only [arm64_norm, s5, hb4.fp], hinv5, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s5, hb4.vregs], hbase.spAligned⟩
      let cs5 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
      have hfold1c0 : ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ r1a_localsCtx (runFsp s0) 0 csPre 0x1c0 8 csMid = memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] := by
        rw [← r1a_locals_focus (runFsp s0) csPre 0x1c0 8 ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) csMid]; exact r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
      rw [r1a_group_mid2, hfold1c0]; refine sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply r1a_sepWPp_exists_pre; intro e0; apply r1a_sepWPp_exists_pre; intro e1; apply r1a_sepWPp_exists_pre; intro e2; apply r1a_sepWPp_exists_pre; intro e3; apply r1a_sepWPp_exists_pre; intro e4; apply r1a_sepWPp_exists_pre; intro e5
      have hpc5 := hb5.pc; have := hb5.spAligned_cur; have hrun5 := hb5.run; change s5.pc = (blkPl_579).base + 2240#64 at hpc5
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hb5.inv; try dsimp only [runProgPlaced, lsProg_579]
      (iterate 11 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun5]); intro hinv6; apply r1a_bind_sepWPp_state; intro s6
      have hb6 : InRunPlaced r1a_CodeOk s0 s6 0x2bf0 := ⟨by simp only [runPcPlaced_eq, arm64_norm, s6, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s6, hrun5], by simp only [arm64_norm, s6, hb5.sp], by simp only [arm64_norm, s6, hb5.fp], hinv6, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s6, hb5.vregs], hbase.spAligned⟩
      have hpc6 := hb6.pc; have := hb6.spAligned_cur; have hrun6 := hb6.run; have hsp6 := hb6.sp; rw [runPcPlaced_eq] at hpc6
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c30) hb6.inv; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp6]; symm at hsp6; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      (iterate 16 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp6; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun6]); intro hinv7; apply r1a_bind_sepWPp_state; intro s7; (try simp only [arm64_norm]); (try rw [hsp6]); rw [r1a_group_mid6]
      refine sepWPp_weaken_pre ?_ (r1a_tail_after_spe (peerV := peerV) (dir := dir) (meG := meG) (w := w) (k := .withString 1 (by decide)) (F_heap := F_heap ∗ anyHeap) hh hdrop hpanic hrej hstk32 hsub64 ⟨by simp only [runPcPlaced_eq, arm64_norm, s7, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s7, hrun6], by simp only [arm64_norm, s7, hsp6], by simp only [arm64_norm, s7, hb6.fp], hinv7, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s7, hb6.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, s7, hsp6]) (by simp only [arm64_norm, s7, s6, s5, hx19_4]) (by simp only [arm64_norm, s7, s6, s5, hx20_4]) (by simp only [arm64_norm, s7, s6, s5, hx21_4]) (by simpa only [arm64_norm, s7, s6, s5] using htr_04) (r1a_hist_ans_step hhans4 (by simp only [arm64_norm, s7, s6, s5]) (by simp only [arm64_norm, s7, s6, s5])))
      have h4words : ∀ {v0 v1 v2 v3 w4 w5 : BitVec 64}, v0 = speWord 1 → v1 = 22#64 → v2 = buf → v3 = 22#64 → ((runFsp s0 + 0x4d0#64) ↦₆₄ v0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ v1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ v2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ v3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ w4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ w5) = ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ 22#64) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ buf) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ 22#64) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ w4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ w5) := by rintro _ _ _ _ _ _ rfl rfl rfl rfl; rfl
      rw [h4words (by simp only [arm64_norm, s7, s6, s5, hx12_4]) (by simp only [arm64_norm, s7, s6, s5, hx22_4, hx25_4]) (by simp only [arm64_norm, s7, s6, s5, hx27_4]; bv_bits) (by simp only [arm64_norm, s7, s6, s5, hx22_4, hx25_4])]
      have hspe_in := r1a_vec22_withString_intro A (runFsp s0 + 0x4d0#64) buf (s6.readReg64 (.gpr 11#5)) (s6.readReg64 (.gpr 13#5)) hbuf0; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspe_in
      have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) (.withString 1 (by decide))) []).symm
      change _ ⊢ runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) (.withString 1 (by decide)))]) ∗ _
      rw [← hfoc']; refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hspe_in)); exact Entails.of_eq (by ac_rfl)
    have hf1750 := r1a_locals_focus (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] 0x1750 8 ((runFsp s0 + 0x1750#64) ↦₆₄ pathCap) []; simp only [List.cons_append, List.nil_append] at hf1750
    have hpc3 := hb3.pc; have := hb3.spAligned_cur; have hrun3 := hb3.run; have hsp3 := hb3.sp; change s3.pc = (blkPl_579).base + 2224#64 at hpc3
    by_cases hp0 : pathCap = 0#64
    · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hb3.inv; dsimp only [restMem, csErr]; rw [hf1750]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp3, ← hx0_3]; symm at hsp3 hx0_3; wp_simp_pre only [sepConj_assoc]
      (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp3 hx0_3; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun3])
      intro hinv4; (try simp only [arm64_norm, hx0_3]); (try rw [hsp3]); rw [r1a_group_8b0]
      refine sepWPp_weaken_pre ?_ (hafter_free _ ⟨by simp only [runPcPlaced_eq, arm64_norm, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun3], by simp only [arm64_norm, hsp3], by simp only [arm64_norm, hb3.fp], hinv4, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb3.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx12_3]) (by simp only [arm64_norm, hx19_3]) (by simp only [arm64_norm, hx20_3]) (by simp only [arm64_norm, hx21_3]) (by simp only [arm64_norm, hx22_3]) (by simp only [arm64_norm, hx23_3]) (by simp only [arm64_norm, hx24_3]) (by simp only [arm64_norm, hx25_3]) (by simp only [arm64_norm, hx27_3]) (by simpa only [arm64_norm] using htr_03) (r1a_hist_ans_step hhans3 (by simp only [arm64_norm]) (by simp only [arm64_norm])))
      rw [← hf1750]; refine Entails.trans (sepConj_mono (r1a_buf22_merge buf _) (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hp0)))))))) ?_; rw [emp_sepConj]; exact Entails.of_eq (by ac_rfl)
    · have hp_be : (pathCap == 0#64) = false := beq_false_of_ne hp0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x6e0) hb3.inv; dsimp only [restMem, csErr]; rw [hf1750]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp3, ← hx0_3]; symm at hsp3 hx0_3; wp_simp_pre only [sepConj_assoc]
      (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp3 hx0_3; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun3])
      intro hinv4; (try simp only [arm64_norm, hx0_3]); (try rw [hsp3]); rw [r1a_group_8b0, ← hf1750]; refine sepWPp_weaken_pre (sepConj_mono_left (r1a_buf22_merge buf _)) ?_
      refine sepWPp_weaken_pre (Entails.of_eq (show memRegion buf 22 ∗ (A.live buf 22 1 ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ (runLocals (runFsp s0) csErr ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) ∗ anyHeap) = ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ stackAt (runFsp s0) sub ∗ A.pool ∗ (memRegion buf 22 ∗ A.live buf 22 1 ∗ runLocals (runFsp s0) csErr ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ (F_heap ∗ anyHeap)) by ac_rfl)) ?_
      apply r1a_free_path_6e0 hh hpanic hext hsub64 hp0 ⟨by simp only [runPcPlaced_eq, arm64_norm, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun3], by simp only [arm64_norm, hsp3], by simp only [arm64_norm, hb3.fp], hinv4, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb3.vregs], hbase.spAligned⟩ (by simp only [arm64_norm]) (by simp only [arm64_norm, hx26_3])
      intro sm4 hb4 r12 r19 r20 r21 r22 r23 r24 r25 r27 _ htrm4 hfilesm4
      refine sepWPp_weaken_pre ?_ (hafter_free sm4 hb4 (by simpa only [arm64_norm, hx12_3] using r12) (by simpa only [arm64_norm, hx19_3] using r19) (by simpa only [arm64_norm, hx20_3] using r20) (by simpa only [arm64_norm, hx21_3] using r21) (by simpa only [arm64_norm, hx22_3] using r22) (by simpa only [arm64_norm, hx23_3] using r23) (by simpa only [arm64_norm, hx24_3] using r24) (by simpa only [arm64_norm, hx25_3] using r25) (by simpa only [arm64_norm, hx27_3] using r27) (by simpa only [htrm4, arm64_norm] using htr_03) (r1a_hist_ans_step hhans3 (by simpa only [arm64_norm] using htrm4) (by simpa only [arm64_norm] using hfilesm4)))
      exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
private theorem r1a_after_decode [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir ikB : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW} {ikCap ikPtr : BitVec 64} {s0 s_disp s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp) (hcall : g.c = .init peerV dir)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hnext : ∀ (s1 : State) (d1 : Init1Data), AtInit1Placed r1a_CodeOk g d1 s0 s1 → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1 (init1MemPlaced A g d1 s0 resStack) Q Qp (runOom s0))
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hbase : InRunPlaced r1a_CodeOk s0 s 0x710)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx25 : s.readReg64 (.gpr 25#5) = ikCap) (hx27 : s.readReg64 (.gpr 27#5) = ikPtr) (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hik : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB) (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A (r1a_peerGhostOf peerV w) (runFsp s0 + 0x2a0#64)), (0x4d0, 48, identityKeyResultAt A (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB))] ∗
        ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) Q Qp (runOom s0) := by
  have hext : extHookStack ≤ resStack - runFrame := by omega
  let peerG := r1a_peerGhostOf peerV w
  let cs6 := [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64))]
  rcases hdec : decodeIdentityKey ikB with err | idKey
  · have hnotOk : ∀ ik, decodeIdentityKey ikB ≠ .ok ik := by rw [hdec]; intro _ h; nomatch h
    obtain ⟨i, hi, hcmn_ne, hent_spe⟩ := r1a_decode_err_unified A (runFsp s0 + 0x4d0#64) ikB hnotOk
    have hhans : RunHistOk g.i s0 s ∧ g.a = some none := ⟨⟨hfs, hout⟩, r1a_reject_of_decode_err he hd hcall hik (by rw [hdec]; rfl)⟩
    rw [← hdec]; have hf4d0 := r1a_locals_focus (runFsp s0) cs6 0x4d0 48 (identityKeyResultAt A (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB)) []
    (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, identityKeyResultAt A (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB))]) ∗ _) _ _ _; rw [hf4d0]
    have h40_words : memRegion (runFsp s0 + 0x4d0#64 + 8#64) 40 ⊢ ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) := by
      rw [ProofLib.memRegion_split _ 8 32 (by decide), ProofLib.memRegion_split _ 8 24 (by decide), ProofLib.memRegion_split _ 8 16 (by decide), ProofLib.memRegion_split _ 8 8 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun d5 => Entails.sepExists_elim fun d4 => Entails.sepExists_elim fun d3 => Entails.sepExists_elim fun d2 => Entails.sepExists_elim fun d1 => ?_
      exact Entails.sepExists_right d1 (Entails.sepExists_right d2 (Entails.sepExists_right d3 (Entails.sepExists_right d4 (Entails.sepExists_right d5 (Entails.refl _)))))
    refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (Entails.trans hent_spe (sepConj_mono_right h40_words)))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro d1; apply r1a_sepWPp_exists_pre; intro d2; apply r1a_sepWPp_exists_pre; intro d3; apply r1a_sepWPp_exists_pre; intro d4; apply r1a_sepWPp_exists_pre; intro d5
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 1808#64 at hpc0
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x8f0) hbase.inv; dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hcmn_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6c]
    refine sepWPp_weaken_pre ?_ (r1a_decode_err (peerV := peerV) (dir := dir) (ikB := ikB) (meG := meG) (w := w) (ikCap := ikCap) (ikPtr := ikPtr) (F_heap := coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) hh hdrop hpanic hrej hstk32 hsub64 hi ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hcmn_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0], by simp only [arm64_norm, s1, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1, hx19]) (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1, hx21]) (by simp only [arm64_norm, s1, hx25]) (by simp only [arm64_norm, s1, hx27]) (by simpa only [arm64_norm, s1] using htr) (r1a_hist_ans_step hhans (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])))
    have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord i) ∗ (((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ⊢ memRegion (runFsp s0 + 0x4d0#64) 48 := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) (speWord i) d1 d2 d3 d4 d5
    have hcs_ent : runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ⊢ runLocals (runFsp s0) [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name := by
      let csPre3 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5)]
      let csSuf2 := [(0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      dsimp only [cs6, csPre3, csSuf2] at *; refine Entails.trans (r1a_locals_drop_head (runFsp s0) 0x1b0 4 _ (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf2) (r1a_pointsTo32_entails_memRegion _ _)) ?_
      refine Entails.trans (r1a_locals_drop_mid (runFsp s0) csPre3 0x260 16 _ csSuf2 (addrUpperAt_entails_memRegion _ _)) ?_
      rw [r1a_locals_focus (runFsp s0) csPre3 0x2a0 32 (protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)) [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)], protocolAddressAt_eq_parts A peerG (runFsp s0 + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]; dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
      have hup16 : addrUpperAt (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w) ⊢ memRegion (runFsp s0 + 0x2b0#64) 16 := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using addrUpperAt_entails_memRegion (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w)
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup16)))) ?_; dsimp only [csPre3, r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]
      have hm2b0 : memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 528 = memRegion (runFsp s0 + 0x2b0#64) 544 := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 16 528 (by decide)).symm
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]; refine Entails.of_eq ?_
      trans ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ ((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗ (memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 528) ∗ memRegion (runFsp s0) 440 ∗ ((runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ ((runFsp s0 + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (runFsp s0 + 0x1d0#64) 208 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 9456
      · ac_rfl
      · rw [hm2b0]; ac_rfl
    refine Entails.trans (sepConj_mono_left (Entails.trans (sepConj_mono_left hw48) (Entails.trans (Entails.of_eq (r1a_locals_focus (runFsp s0) cs6 0x4d0 48 _ []).symm) hcs_ent))) ?_; exact Entails.of_eq (by ac_rfl)
  · obtain ⟨ikW0, ikW1, ikW2, ikW3, hikWords⟩ := r1a_exists_words32 idKey.publicKey.bytes.toList (by simp)
    have hf4d0 := r1a_locals_focus (runFsp s0) cs6 0x4d0 48 (identityKeyResultAt A (runFsp s0 + 0x4d0#64) (.ok idKey)) []
    (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, identityKeyResultAt A (runFsp s0 + 0x4d0#64) (.ok idKey))]) ∗ _) _ _ _; rw [hf4d0]; dsimp only [identityKeyResultAt]; rw [← hikWords (runFsp s0 + 0x4d0#64 + 8#64)]
    have hhead_split : r1a_localsCtx (runFsp s0) 0 cs6 0x4d0 48 [] = memRegion (runFsp s0 + 0x180#64) 8 ∗ memRegion (runFsp s0 + 0x190#64) 8 ∗ memRegion (runFsp s0 + 0x1a8#64) 8 ∗ (memRegion (runFsp s0) 0x180 ∗ memRegion (runFsp s0 + 0x188#64) 8 ∗ memRegion (runFsp s0 + 0x198#64) 16 ∗ r1a_localsCtx (runFsp s0) 0x1b0 cs6 0x4d0 48 []) := by
      dsimp only [cs6, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; have s1 := ProofLib.memRegion_split (runFsp s0 + 0#64) 0x180 48 (by decide); have s2 := ProofLib.memRegion_split (runFsp s0 + 0x180#64) 8 40 (by decide); have s3 := ProofLib.memRegion_split (runFsp s0 + 0x188#64) 8 32 (by decide); have s4 := ProofLib.memRegion_split (runFsp s0 + 0x190#64) 8 24 (by decide); have s5 := ProofLib.memRegion_split (runFsp s0 + 0x198#64) 16 8 (by decide); simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at s1 s2 s3 s4 s5 ⊢; rw [s1, s2, s3, s4, s5]; ac_rfl
    rw [hhead_split, ProofLib.memRegion_eight (runFsp s0 + 0x180#64), ProofLib.memRegion_eight (runFsp s0 + 0x190#64), ProofLib.memRegion_eight (runFsp s0 + 0x1a8#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply r1a_sepWPp_exists_pre; intro z0; apply r1a_sepWPp_exists_pre; intro z1; apply r1a_sepWPp_exists_pre; intro z2
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 1808#64 at hpc0
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x738) hbase.inv; dsimp only [runProgPlaced, lsProg_579, okTagVec]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
    (iterate 10 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_ok710]
    have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x738 := ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0], by simp only [arm64_norm, s1, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs], hbase.spAligned⟩
    have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, s1, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, s1, hx20]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, s1, hx21]
    have hx22_1 : s1.readReg64 (.gpr 22#5) = ikW2 := by simp only [arm64_norm, s1]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = ikCap := by simp only [arm64_norm, s1, hx25]
    have hx27_1 : s1.readReg64 (.gpr 27#5) = ikPtr := by simp only [arm64_norm, s1, hx27]
    have hx28_1 : s1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length := by simp only [arm64_norm, s1, hx28]
    have htr_01 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using htr
    have hfs_1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hfs
    have hout_1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [] := by simpa only [arm64_norm, s1] using hout
    let d1 : Init1Data := { peerV := peerV, peerG := peerG, meV := meV, meG := meG, dir := dir, dirCap := w.w4, dirPtr := w.w5, idKey := idKey, ikW0 := ikW0, ikW1 := ikW1, ikW2 := ikW2, ikW3 := ikW3 }
    have hpack_init1 : ((((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ (((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3)) ∗ memRegion (runFsp s0 + 0x4f8#64) 8) ∗ (((runFsp s0 + 0x180#64) ↦₆₄ ikW0) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ ikW3) ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ ikW1) ∗ (memRegion (runFsp s0) 0x180 ∗ memRegion (runFsp s0 + 0x188#64) 8 ∗ memRegion (runFsp s0 + 0x198#64) 16 ∗ r1a_localsCtx (runFsp s0) 0x1b0 cs6 0x4d0 48 []))) ⊢ runLocals (runFsp s0) (init1Cells A (runFsp s0) d1) := by
      have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ (((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3)) ∗ memRegion (runFsp s0 + 0x4f8#64) 8 ⊢ memRegion (runFsp s0 + 0x4d0#64) 48 := by
        have s1 := (ProofLib.memRegion_split (runFsp s0 + 0x4d0#64) 8 40 (by decide)).symm; have s2 := (ProofLib.memRegion_split (runFsp s0 + 0x4d8#64) 8 32 (by decide)).symm; have s3 := (ProofLib.memRegion_split (runFsp s0 + 0x4e0#64) 8 24 (by decide)).symm; have s4 := (ProofLib.memRegion_split (runFsp s0 + 0x4e8#64) 8 16 (by decide)).symm; have s5 := (ProofLib.memRegion_split (runFsp s0 + 0x4f0#64) 8 8 (by decide)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5; rw [← s1, ← s2, ← s3, ← s4, ← s5]
        refine Entails.trans (Entails.of_eq (show _ = ((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3) ∗ memRegion (runFsp s0 + 0x4f8#64) 8 by ac_rfl)) ?_
        exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))
      refine Entails.trans (sepConj_mono_left hw48) ?_; have hdrop4d0 : runLocals (runFsp s0) (init1Cells A (runFsp s0) d1 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ⊢ runLocals (runFsp s0) (init1Cells A (runFsp s0) d1) := r1a_locals_drop_mid (runFsp s0) (init1Cells A (runFsp s0) d1) 0x4d0 48 _ [] (Entails.refl _)
      refine Entails.trans (Entails.of_eq ?_) hdrop4d0; rw [r1a_locals_focus (runFsp s0) (init1Cells A (runFsp s0) d1) 0x4d0 48 _ []]; dsimp only [init1Cells, d1, cs6, r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]; simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]; ac_rfl
    refine sepWPp_weaken_pre (sepConj_mono_left hpack_init1) ?_
    have hmeVal : d1.meG.val = addrValOf d1.meV := by rcases hd.meRegs with ⟨_, _, hnb, _, hdev⟩; dsimp only [d1, AddrGhost.val, addrValOf]; rw [hnb, hdev]
    have hfinish : ∀ s2 : State, InRunPlaced r1a_CodeOk s0 s2 0x74c → s2.readReg64 (.gpr 19#5) = g.stores → s2.readReg64 (.gpr 20#5) = g.res → s2.readReg64 (.gpr 21#5) = meG.name.cap → s2.readReg64 (.gpr 22#5) = ikW2 → s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length → s0.trace <+: s2.trace → s2.fs.files = runFiles g.i → ProcessOutcome.traceStreamBytes .stdout s2.trace = [] → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2 (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (runLocals (runFsp s0) (init1Cells A (runFsp s0) d1) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0)) Q Qp (runOom s0) := by
      intro s2 hb2 r19 r20 r21 r22 r28 tr2 fs2 out2; refine sepWPp_weaken_pre (by dsimp only [init1MemPlaced, d1]; rw [hw6]; exact Entails.of_eq (by ac_rfl)) (hnext s2 d1 ⟨hb2, hcall, r19, r20, r21, r22, r28, rfl, hmeVal, hd.ownSem, ⟨ikB, r1a_ikOk_sem hik hdec⟩, hikWords, tr2, fs2, out2⟩)
    have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp; change s1.pc = (blkPl_579).base + 1848#64 at hpc1
    by_cases hik0 : ikCap = 0#64
    · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x74c) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
      (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx25_1, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2
      refine sepWPp_weaken_pre ?_ (hfinish _ ⟨by simp only [runPcPlaced_eq, arm64_norm, hx25_1, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun1], by simp only [arm64_norm, hsp1], by simp only [arm64_norm, hb1.fp], hinv2, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx19_1]) (by simp only [arm64_norm, hx20_1]) (by simp only [arm64_norm, hx21_1]) (by simp only [arm64_norm, hx22_1]) (by simp only [arm64_norm, hx28_1]) (by simpa only [arm64_norm] using htr_01) (by simpa only [arm64_norm] using hfs_1) (by simpa only [arm64_norm] using hout_1))
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hik0))) ?_; rw [emp_sepConj]; exact Entails.of_eq (by ac_rfl)
    · have hne_ik : (ikCap == 0#64) = false := beq_false_of_ne hik0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
      (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hx25_1, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun1]); intro hinv_c
      apply r1a_call_dealloc (cap := ikCap) (ptr := ikPtr) (len := BitVec.ofNat 64 ikB.length) (bs := ikB) (F := runLocals (runFsp s0) (init1Cells A (runFsp s0) d1) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) (retOff := 0x74c) hh hpanic hext hsub64 hik0 (by simp only [lsRustDeallocSymCli, arm64_norm, hx25_1, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun1]) hinv_c (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, hb1.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hx27_1]) (by simp only [arm64_norm, hx25_1]) (by simp only [arm64_norm]) (by ac_rfl)
      intro sm hbm hcsm htrm hfilesm; exact hfinish sm hbm (by simpa only [arm64_norm, hx19_1] using hcsm.1) (by simpa only [arm64_norm, hx20_1] using hcsm.2.1) (by simpa only [arm64_norm, hx21_1] using hcsm.2.2.1) (by simpa only [arm64_norm, hx22_1] using hcsm.2.2.2.1) (by simpa only [arm64_norm, hx28_1] using hcsm.2.2.2.2.2.2.2.2.2.1) (by simpa only [htrm, arm64_norm] using htr_01) (by simpa only [hfilesm, arm64_norm] using hfs_1) (by simpa only [htrm, arm64_norm] using hout_1)

/-! ## Entry Dispatch and `run_hop_init1_placed_ok` -/
private theorem r1a_none_sem [LibsignalPlacement] {S : RunSem} {g : RunCall} {s0 s : State} (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g .none s0 s) : g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hnone⟩; rw [he.rel.2.2.2.2.2]; unfold runAns; simp [he.parse, hget, hnone]

private theorem r1a_init_none_branch [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {peerV : AddrV} {dir : Bytes} {w : CallW} {s0 s_disp s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g .none s0 s_disp) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hbase : InRunPlaced r1a_CodeOk s0 s 0x654)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = noneCap) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [] ∗ ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F_heap) Q Qp (runOom s0) := by
  have hcarve := r1a_locals_carve_region (runFsp s0) [] 0x2a0 32 []; have hf2a0 := r1a_locals_focus (runFsp s0) [] 0x2a0 32 (memRegion (runFsp s0 + 0x2a0#64) 32) []
  have h32 : memRegion (runFsp s0 + 0x2a0#64) 32 = (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64, ((runFsp s0 + 0x2a0#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ q1) ∗ ((runFsp s0 + 0x2b0#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ q3)) := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x2a0#64)
  simp only [List.nil_append] at hcarve hf2a0 ⊢; rw [hcarve, hf2a0, h32]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro q0; apply r1a_sepWPp_exists_pre; intro q1; apply r1a_sepWPp_exists_pre; intro q2; apply r1a_sepWPp_exists_pre; intro q3
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 1620#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x860) hbase.inv; dsimp only [runProgPlaced, lsProg_579, noneCap] at hpc0 hx21 ⊢
  rw [← hsp0, ← hx25]; symm at hsp0 hx25; wp_simp_pre only [sepConj_assoc]
  (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  symm at hsp0 hx25; apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx25]); (try rw [hsp0]); rw [r1a_group4_7]
  refine sepWPp_weaken_pre ?_ (r1a_me_none (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap) hh hpanic hrej hext hsub64 ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hx21, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0], by simp only [arm64_norm, s1, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, s1, hx19]) (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1]) (by simpa only [arm64_norm, s1] using htr) ⟨⟨by simpa only [arm64_norm, s1] using hfs, by simpa only [arm64_norm, s1] using hout⟩, r1a_none_sem he hd⟩)
  have hpack2a0 : (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗ ((runFsp s0 + 0x2b0#64) ↦₆₄ w.w2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ w.w3)) ∗ r1a_localsCtx (runFsp s0) 0 [] 0x2a0 32 [] ⊢ runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] := by
    have ht16 : ((runFsp s0 + 0x2b0#64) ↦₆₄ w.w2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ w.w3) ⊢ memRegion (runFsp s0 + 0x2b0#64) 16 := by
      have hs := (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 8 8 (by decide)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; rw [← hs]; exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ht16))) ?_; dsimp only [r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]; have hm := (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 16 10032 (by decide)).symm
    simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at hm ⊢; refine Entails.of_eq ?_
    trans (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗ (memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 10032) ∗ memRegion (runFsp s0) 672)
    · ac_rfl
    · rw [hm]; ac_rfl
  refine Entails.trans (sepConj_mono hpack2a0 (sepConj_mono_left (r1a_call7_to_memRegion56 g.call w))) ?_; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
private theorem r1a_after_read [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {S : RunSem} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW} {pathCap pathPtr : BitVec 64} {r : Except Unit Bytes} {s0 s_disp s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp) (hcall : g.c = .init peerV dir)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp)
    (hnext : ∀ (s1 : State) (d1 : Init1Data), AtInit1Placed r1a_CodeOk g d1 s0 s1 → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1 (init1MemPlaced A g d1 s0 resStack) Q Qp (runOom s0))
    (hikStk : 0x60 ≤ resStack - runFrame) (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hbase : InRunPlaced r1a_CodeOk s0 s 0x6bc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (_hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr) (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length) (htr : s0.trace <+: s.trace)
    (herr_f : r = .error () → RunHistOk g.i s0 s ∧ g.a = some none)
    (hok_f : ∀ ikB, r = .ok ikB → cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB ∧ s.fs.files = runFiles g.i ∧ ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A (r1a_peerGhostOf peerV w) (runFsp s0 + 0x2a0#64)), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48), (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap), (0x23b0, 24, ioVecAt A (runFsp s0 + 0x23b0#64) r)] ∗
        ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) Q Qp (runOom s0) := by
  intro pathBs; have hext : extHookStack ≤ resStack - runFrame := by omega
  let peerG := r1a_peerGhostOf peerV w
  let cs8 := [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48), (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
  have hf23b0 := r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (ioVecAt A (runFsp s0 + 0x23b0#64) r) []; (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (cs8 ++ [(0x23b0, 24, ioVecAt A (runFsp s0 + 0x23b0#64) r)]) ∗ _) _ _ _; rw [hf23b0]
  rcases r with ⟨⟨⟩⟩ | ikB
  · dsimp only [ioVecAt]; have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 1724#64 at hpc0
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x878) hbase.inv; try dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
    (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp0
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group2c]
    refine sepWPp_weaken_pre ?_ (r1a_read_err (peerV := peerV) (dir := dir) (pathBs := pathBs) (meG := meG) (w := w) (pathCap := pathCap) (pathPtr := pathPtr) (F_heap := coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) hh hdrop hpanic hrej hstk32 hsub64 ⟨by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun0], by simp only [arm64_norm, hsp0], by simp only [arm64_norm, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm]; decide) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx26]) (by simpa only [arm64_norm] using htr) (r1a_hist_ans_step (herr_f rfl) (by simp only [arm64_norm]) (by simp only [arm64_norm])))
    have hm24 : ∀ v, ((runFsp s0 + 0x23b0#64) ↦₆₄ v) ∗ memRegion (runFsp s0 + 0x23b8#64) 16 ⊢ memRegion (runFsp s0 + 0x23b0#64) 24 := fun v => by
      have hs24 := ProofLib.memRegion_split (runFsp s0 + 0x23b0#64) 8 16 (by decide); simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hs24; rw [hs24]; exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left (hm24 _))) ?_; rw [← r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (memRegion (runFsp s0 + 0x23b0#64) 24) []]; have hdrop23b0 : runLocals (runFsp s0) (cs8 ++ [(0x23b0, 24, memRegion (runFsp s0 + 0x23b0#64) 24)]) ⊢ runLocals (runFsp s0) cs8 := r1a_locals_drop_mid (runFsp s0) cs8 0x23b0 24 _ [] (Entails.refl _)
    let csPre3 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5)]
    let csSuf2 := [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48), (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
    let csSuf3 := (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)) :: csSuf2
    have hdrop1b0 : runLocals (runFsp s0) cs8 ⊢ runLocals (runFsp s0) (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3) := r1a_locals_drop_head (runFsp s0) 0x1b0 4 _ (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3) (r1a_pointsTo32_entails_memRegion _ _)
    have hdrop260 : runLocals (runFsp s0) (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3) ⊢ runLocals (runFsp s0) (csPre3 ++ csSuf3) := r1a_locals_drop_mid (runFsp s0) csPre3 0x260 16 _ csSuf3 (addrUpperAt_entails_memRegion _ _)
    refine Entails.trans (sepConj_mono_left (Entails.trans hdrop23b0 (Entails.trans hdrop1b0 hdrop260))) ?_; change (runLocals (runFsp s0) (csPre3 ++ (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)) :: csSuf2) ∗ _) ⊢ _
    rw [r1a_locals_focus (runFsp s0) csPre3 0x2a0 32 (protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)) csSuf2, protocolAddressAt_eq_parts A peerG (runFsp s0 + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]; dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
    have hsplit_peer : (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a0#64 + 8#64) ↦₆₄ w.w1) ∗ addrUpperAt (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name) ∗ r1a_localsCtx (runFsp s0) 0 csPre3 0x2a0 32 csSuf2 ⊢ runLocals (runFsp s0) (csPre3 ++ (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) :: (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) :: csSuf2) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (addrUpperAt_entails_memRegion _ _))))) ?_; have hc1 := r1a_locals_drop_mid (runFsp s0) (csPre3 ++ [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]) 0x2b0 16 (memRegion (runFsp s0 + 0x2b0#64) 16) csSuf2 (Entails.refl _); refine Entails.trans ?_ (sepConj_mono_left hc1); simp only [csPre3, csSuf2, List.append_assoc, List.cons_append, List.nil_append, BitVec.add_assoc, BitVec.reduceAdd]; dsimp only [r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]; simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
    refine Entails.trans (sepConj_mono_left hsplit_peer) ?_; dsimp only [csPre3, csSuf2]; simp only [List.cons_append, List.nil_append]; exact Entails.of_eq (by ac_rfl)
  · obtain ⟨hik, hfs_ok, hout_ok⟩ := hok_f ikB rfl; dsimp only [ioVecAt]; refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (M3Helpers.vecU8_to_ownedBytes A _ ikB))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]; apply r1a_sepWPp_exists_pre; intro ikCap; apply r1a_sepWPp_exists_pre; intro ikPtr; rw [M3Helpers.ownedBytes_pure A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB]
    have hp_ik {P0 : Prop} (W0 W1 W2 Y0 C0 P1 R0 : SepProp) : ((W0 ∗ W1 ∗ W2 ∗ ⌜P0⌝ ∗ Y0) ∗ C0) ∗ P1 ∗ R0 = ⌜P0⌝ ∗ ((((W0 ∗ W1 ∗ W2) ∗ C0) ∗ P1 ∗ Y0) ∗ R0) := by ac_rfl
    rw [hp_ik]; apply r1a_sepWPp_pure_pre; rintro ⟨_, hik_le, hik_lt, _⟩; have hik_ne : (ikCap + 1#64 == 0#64) = false := M3Helpers.beq_add_one_zero_false_of_lt hik_lt
    let cs7 := [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
    have hafter_path : ∀ s2 : State, InRunPlaced r1a_CodeOk s0 s2 0x6f4 → s2.readReg64 (.gpr 19#5) = g.stores → s2.readReg64 (.gpr 20#5) = g.res → s2.readReg64 (.gpr 21#5) = meG.name.cap → s2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 ikB.length → s2.readReg64 (.gpr 23#5) = ikCap → s2.readReg64 (.gpr 24#5) = w.w4 → s2.readReg64 (.gpr 25#5) = ikCap → s2.readReg64 (.gpr 27#5) = ikPtr → s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length → s0.trace <+: s2.trace → s2.fs.files = runFiles g.i → ProcessOutcome.traceStreamBytes .stdout s2.trace = [] → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2 (runLocals (runFsp s0) cs7 ∗ ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) Q Qp (runOom s0) := by
      intro s2 hb2 r19 r20 r21 r22 r23 r24 r25 r27 r28 tr2 fs2 out2
      let csPre2 := [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr)]
      let csSuf4 := [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64)), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      (try rw [r1a_memRegion_zero (runFsp s0)]); change ProofLib.SepWPp _ _ _ (runLocals (runFsp s0) (csPre2 ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csSuf4) ∗ _) _ _ _; rw [r1a_locals_focus (runFsp s0) csPre2 0x1c0 8 (memRegion (runFsp s0 + 0x1c0#64) 8) csSuf4, ProofLib.memRegion_eight (runFsp s0 + 0x1c0#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro c1c0
      have hpc2 := hb2.pc; have := hb2.spAligned_cur; have hrun2 := hb2.run; have hsp2 := hb2.sp; change s2.pc = (blkPl_579).base + 1780#64 at hpc2
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (RecordCodecs.Placed.blkPl_18).base) hb2.inv; (try dsimp only [runProgPlaced, lsProg_579]); rw [← hsp2]; symm at hsp2; wp_simp_pre only [sepConj_assoc]
      (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp2
      apply SepWP.done (by simp only [arm64_norm, r23, hik_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte]; rfl) (by simp only [arm64_norm, hrun2]); intro hinv_d; apply r1a_bind_sepWPp_state; intro sd; (try simp only [arm64_norm, r24]); (try rw [hsp2])
      let csPre6 := csPre2 ++ (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) :: [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (runFsp s0 + 0x2a0#64))]
      have hfold4d0 : ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ r1a_localsCtx (runFsp s0) 0 csPre2 0x1c0 8 csSuf4 = memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 [] := by rw [← r1a_locals_focus (runFsp s0) csPre2 0x1c0 8 ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) csSuf4]; exact r1a_locals_focus (runFsp s0) csPre6 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
      let sub := resStack - runFrame; let rem60 := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - 0x60)
      have hstk60 : stackAt (runFsp s0) sub = rem60 ∗ stackAt (runFsp s0) 0x60 := r1a_stackAt_split (runFsp s0) hikStk hsub64
      refine r1a_call_run (x := ⟨ikPtr, ikB, runFsp s0 + 0x4d0#64⟩) (F := r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 [] ∗ r1a_ownedSlack A ikCap ikPtr ikB ∗ rem60 ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ runSaved s0 ∗ A.pool) (retOff := 0x710) (hh.fs (runProgPlaced H) 579) (identityKeyDecode_placed_ok (callerProg := runProgPlaced H) (i := 579) (A := A)) (by simp only [arm64_norm, sd, r23, hik_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte]; rfl) (by simp only [arm64_norm, sd, hrun2]) hinv_d (by simp only [arm64_norm, sd, hsp2]) (by simp only [arm64_norm, sd, hb2.fp]) (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, sd, hb2.vregs]) hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, sd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) hpanic
        (by dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec]; rw [← sepConj_assoc, hfold4d0, r1a_ownedBytes_expose A ikCap ikPtr ikB, hstk60]
            have hlen_ik : (BitVec.ofNat 64 ikB.length).toNat = ikB.length := Nat.mod_eq_of_lt (by omega)
            refine Entails.trans (Entails.of_eq (by (try simp only [arm64_norm, sd]); (try rw [hsp2]); dsimp only [lsLogOff, lsLogFilterAddr, FromRecordCallees.lsLogOff, lsρ]; ac_rfl)) (sepConj_mono_left (Entails.pure_right ⟨by simp only [arm64_norm, sd, r27], by simp only [arm64_norm, sd, r22, hlen_ik], by simp only [arm64_norm, sd, hsp2]⟩ (Entails.refl _))))
        (fun _ => by dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails)
        (fun _ _ => by dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec]; exact Entails.refl _)
        (fun _ => by dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails) ?_
      intro s3 hb3 hcs3 _ hfiles3; dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec]; rw [sepConj_assoc]; apply r1a_sepWPp_pure_pre; intro htr3
      refine sepWPp_weaken_pre ?_ (r1a_after_decode hh hdrop he hd hcall hpanic hrej hnext hstk32 hsub64 hb3 (by simpa only [arm64_norm, sd, r19] using hcs3.1) (by simpa only [arm64_norm, sd, r20] using hcs3.2.1) (by simpa only [arm64_norm, sd, r21] using hcs3.2.2.1) (by simpa only [arm64_norm, sd, r25] using hcs3.2.2.2.2.2.2.1) (by simpa only [arm64_norm, sd, r27] using hcs3.2.2.2.2.2.2.2.2.1) (by simpa only [arm64_norm, sd, r28] using hcs3.2.2.2.2.2.2.2.2.2.1) hik hw6 hw2 (by simpa only [htr3, arm64_norm, sd] using tr2) ((hfiles3 htr3).trans (by simpa only [arm64_norm, sd] using fs2)) (by simpa only [htr3, arm64_norm, sd] using out2))
      have hsd_sp : sd.sp = runFsp s0 := by simp only [sd, arm64_norm, hsp2]
      rw [hsd_sp]; have hback4d0 := (r1a_locals_focus (runFsp s0) csPre6 0x4d0 48 (identityKeyResultAt A (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB)) []).symm; dsimp only [csPre6, csPre2, peerG] at hback4d0; simp only [List.cons_append, List.append_assoc, List.nil_append] at hback4d0; refine Entails.of_eq ?_
      trans (identityKeyResultAt A (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB) ∗ r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 []) ∗ ((ikPtr ↦ₛ ikB) ∗ r1a_ownedSlack A ikCap ikPtr ikB) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) sub ∗ A.pool
      · rw [hstk60]; dsimp only [lsLogOff, lsLogFilterAddr, FromRecordCallees.lsLogOff, lsρ]; ac_rfl
      · rw [← r1a_ownedBytes_expose A ikCap ikPtr ikB]; dsimp only [csPre6, csPre2, peerG]; simp only [List.cons_append, List.append_assoc, List.nil_append]; rw [← hback4d0]
    have hcollapse_slots : (((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗ ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗ r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 [] ⊢ runLocals (runFsp s0) cs7 := by
      have hw24 : ((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗ ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length) ⊢ memRegion (runFsp s0 + 0x23b0#64) 24 := by
        have s1 := (ProofLib.memRegion_split (runFsp s0 + 0x23b0#64) 8 16 (by decide)).symm; have s2 := (ProofLib.memRegion_split (runFsp s0 + 0x23b8#64) 8 8 (by decide)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2; rw [← s1, ← s2]; exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))
      refine Entails.trans (sepConj_mono_left hw24) ?_; rw [← r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (memRegion (runFsp s0 + 0x23b0#64) 24) []]; refine Entails.trans (r1a_locals_drop_mid (runFsp s0) cs8 0x23b0 24 _ [] (Entails.refl _)) ?_; exact r1a_locals_drop_mid (runFsp s0) cs7 0x1750 8 _ [] (pointsTo64_entails_memRegion _ _)
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp; change s.pc = (blkPl_579).base + 1724#64 at hpc0
    by_cases hp0 : pathCap = 0#64
    · apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hbase.inv; dsimp only [cs8, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]; (iterate 9 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp0
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_6bc]
      refine sepWPp_weaken_pre (Entails.of_eq (show _ = (((((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗ ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗ r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 []) ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool by simp only [cs8, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]; ac_rfl)) ?_
      refine sepWPp_weaken_pre ?_ (hafter_path _ ⟨by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun0], by simp only [arm64_norm, hsp0], by simp only [arm64_norm, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hx28]) (by simpa only [arm64_norm] using htr) (by simpa only [arm64_norm] using hfs_ok) (by simpa only [arm64_norm] using hout_ok))
      refine Entails.trans (sepConj_mono_left (sepConj_mono hcollapse_slots (sepConj_mono_left (r1a_ownedBytes_zero hp0)))) ?_; rw [emp_sepConj]; exact Entails.of_eq (by ac_rfl)
    · have hp_be : (pathCap == 0#64) = false := beq_false_of_ne hp0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x6e0) hbase.inv; dsimp only [cs8, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]; (iterate 9 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp0
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_6bc]
      refine sepWPp_weaken_pre (Entails.of_eq (show _ = (((((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗ ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗ r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 []) ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool by simp only [cs8, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]; ac_rfl)) ?_
      refine sepWPp_weaken_pre (Entails.trans (sepConj_mono_left (sepConj_mono_left hcollapse_slots)) (Entails.of_eq (show (runLocals (runFsp s0) cs7 ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool = ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (runLocals (runFsp s0) cs7 ∗ ownedBytes A ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) by ac_rfl))) ?_
      apply r1a_free_path_6e0 hh hpanic hext hsub64 hp0 ⟨by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd], by simp only [arm64_norm, hrun0], by simp only [arm64_norm, hsp0], by simp only [arm64_norm, hbase.fp], hinv1, by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs], hbase.spAligned⟩ (by simp only [arm64_norm]) (by simp only [arm64_norm, hx26])
      intro sm4 hb4 _ r19 r20 r21 r22 r23 r24 r25 r27 r28 htrm4 hfilesm4
      exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (hafter_path sm4 hb4 (by simpa only [arm64_norm, hx19] using r19) (by simpa only [arm64_norm, hx20] using r20) (by simpa only [arm64_norm, hx21] using r21) (by simpa only [arm64_norm] using r22) (by simpa only [arm64_norm] using r23) (by simpa only [arm64_norm, hx24] using r24) (by simpa only [arm64_norm] using r25) (by simpa only [arm64_norm] using r27) (by simpa only [arm64_norm, hx28] using r28) (by simpa only [htrm4, arm64_norm] using htr) (by simpa only [hfilesm4, arm64_norm] using hfs_ok) (by simpa only [htrm4, arm64_norm] using hout_ok))

private theorem r1a_inRun [LibsignalPlacement] {s0 s : State} {off : Nat} (hpc : s.pc = runPcPlaced off) (hrun : s.status = .Running) (hsp : s.sp = runFsp s0) (hfp : s.readReg64 .fp = s0.sp - 0x60#64) (hinv : r1a_CodeOk s.mem) (hv : calleeSavedVRegs s = calleeSavedVRegs s0) (hal : s0.spAligned = true) : InRunPlaced r1a_CodeOk s0 s off := ⟨hpc, hrun, hsp, hfp, hinv, hv, hal⟩
private theorem r1a_memRegion4_word32 (a : BitVec 64) : memRegion a 4 ⊢ ∃∗ u : BitVec 32, a ↦₃₂ u := by rw [ProofLib.memRegion_four]; exact Entails.refl _
private theorem r1a_sepWPp_rodata_idkey [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp} (hinv : r1a_CodeOk s.mem) (h : ProofLib.SepWPp prog ret s ((lsρ r1a_idKeySym ↦ᵣ utf8 "identity-key") ∗ P) Q Qp O) : ProofLib.SepWPp prog ret s P Q Qp O :=
  fun R hm hL => h R (by simpa only [sepConj_assoc] using r1a_rodata_idkey_intro hinv hm) hL
private theorem r1a_sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State} {D P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp} (h : ProofLib.SepWPp prog ret s P Q Qp O) : ProofLib.SepWPp prog ret s (D ∗ P) Q Qp O :=
  fun R hm hL => h R (Satisfies.drop_mid (by simpa only [sepConj_comm D P, sepConj_assoc] using hm)) hL

set_option maxHeartbeats 800000 in
private theorem r1a_some_after_668 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {slots : RunSlots} {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW} {s0 s_disp s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hc : RunCalleesPlaced A H B slots) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp) (hcall : g.c = .init peerV dir)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1a_CodeOk H A g s0 resStack Q Qp) (hnext : ∀ (s1 : State) (d1 : Init1Data), AtInit1Placed r1a_CodeOk g d1 s0 s1 → ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1 (init1MemPlaced A g d1 s0 resStack) Q Qp (runOom s0))
    (hpathStk : pathNeed ≤ resStack - runFrame) (hreadStk : B.readFile ≤ resStack - runFrame) (hikStk : 0x60 ≤ resStack - runFrame) (hstk32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x668) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx25 : s.readReg64 (.gpr 25#5) = g.call) (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length) (hw3 : w.w3.setWidth 8 = peerV.device) (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    let fsp := runFsp s0
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗ ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3)) ∗ r1a_localsCtx fsp 0 [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] 0x2a0 32 [] ∗ ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool) Q Qp (runOom s0) := by
  intro fsp; obtain ⟨hpOk, hdLen, hnLen, hpLen⟩ := r1a_idKey_path_bounds he hcall; let peerG := r1a_peerGhostOf peerV w
  have hclose_peer : ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3) ⊢ addrUpperAt (fsp + 0x2b0#64) peerG := by have h2 : w.w2 = BitVec.ofNat 64 peerG.name.bytes.length := hw2; rw [h2]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_addrUpperAt_close (fsp + 0x2b0#64) peerG w.w3 hw3
  refine sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right hclose_peer))) ?_; refine sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_left (by dsimp only [r1a_localsCtx]; exact sepConj_mono_right (sepConj_mono_left (r1a_addrUpperAt_open (fsp + 0x1d0#64) meG))))) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro meW1
  have hp_me (X Y P Z W V : SepProp) : X ∗ (Y ∗ (P ∗ Z) ∗ W) ∗ V = P ∗ (X ∗ (Y ∗ Z ∗ W) ∗ V) := by ac_rfl
  rw [hp_me]; apply r1a_sepWPp_pure_left; intro hmeW1
  have hctx_open : memRegion (fsp + 0#64) (0x1d0 - 0) ∗ (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d0#64 + 8#64) ↦₆₄ meW1)) ∗ (memRegion (fsp + BitVec.ofNat 64 (0x1d0 + 16)) (0x2a0 - (0x1d0 + 16)) ∗ runLocalsFrom fsp (0x2a0 + 32) []) = memRegion (fsp + 0x1b0#64) 4 ∗ memRegion (fsp + 0x1b8#64) 8 ∗ memRegion (fsp + 0x1c0#64) 8 ∗ memRegion (fsp + 0x1c8#64) 8 ∗ memRegion (fsp + 0x260#64) 8 ∗ memRegion (fsp + 0x268#64) 8 ∗ (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) := by
    have a1 := ProofLib.memRegion_split fsp 0x1b0 32 (by decide); have a2 := ProofLib.memRegion_split (fsp + 0x1b0#64) 4 28 (by decide); have a3 := ProofLib.memRegion_split (fsp + 0x1b4#64) 4 24 (by decide); have a4 := ProofLib.memRegion_split (fsp + 0x1b8#64) 8 16 (by decide); have a5 := ProofLib.memRegion_split (fsp + 0x1c0#64) 8 8 (by decide); have b1 := ProofLib.memRegion_split (fsp + 0x1e0#64) 0x80 64 (by decide); have b2 := ProofLib.memRegion_split (fsp + 0x260#64) 8 56 (by decide); have b3 := ProofLib.memRegion_split (fsp + 0x268#64) 8 48 (by decide); dsimp only [r1a_localsCtx, runLocalsFrom]; simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at a1 a2 a3 a4 a5 b1 b2 b3 ⊢; rw [a1, a2, a3, a4, a5, b1, b2, b3]; ac_rfl
  rw [hctx_open, ProofLib.memRegion_four (fsp + 0x1b0#64), ProofLib.memRegion_eight (fsp + 0x1b8#64), ProofLib.memRegion_eight (fsp + 0x1c0#64), ProofLib.memRegion_eight (fsp + 0x1c8#64), ProofLib.memRegion_eight (fsp + 0x260#64), ProofLib.memRegion_eight (fsp + 0x268#64)]; dsimp only [addrUpperAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply r1a_sepWPp_exists_pre; intro u0; apply r1a_sepWPp_exists_pre; intro u1; apply r1a_sepWPp_exists_pre; intro u2; apply r1a_sepWPp_exists_pre; intro u3; apply r1a_sepWPp_exists_pre; intro u4; apply r1a_sepWPp_exists_pre; intro u5
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 : s.sp = fsp := hbase.sp; change s.pc = (blkPl_579).base + 1640#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_596).base) hbase.inv; (try dsimp only [runProgPlaced, lsProg_579])
  rw [← hsp0, ← hx25]; symm at hsp0 hx25; wp_simp_pre only [sepConj_assoc]; (iterate 14 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp0 hx25
  apply SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, hrun0]); intro hinva; apply r1a_bind_sepWPp_state; intro sa; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx22, hx25, hx28]); (try rw [hsp0])
  let cs7 := [(0x1b0, 4, (fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32), (0x1b8, 8, (fsp + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (fsp + 0x1c0#64) 8), (0x1c8, 8, (fsp + 0x1c8#64) ↦₆₄ w.w5), (0x260, 16, addrUpperAt (fsp + 0x260#64) meG), (0x2a0, 32, protocolAddressAt A peerG (fsp + 0x2a0#64)), (0x4d0, 48, memRegion (fsp + 0x4d0#64) 48)]
  have hpack_locals : (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗ (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗ ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗ (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ ((fsp + 0x1c0#64) ↦₆₄ u3) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗ (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ⊢ memRegion (fsp + 0x1750#64) 24 ∗ r1a_localsCtx fsp 0 cs7 0x1750 24 [] := by
    have hme260 := r1a_addrUpperAt_close (fsp + 0x260#64) meG meW1 hmeW1
    have hd1d0 : ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ⊢ memRegion (fsp + 0x1d0#64) 16 := by have s := (ProofLib.memRegion_split (fsp + 0x1d0#64) 8 8 (by decide)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]; exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    have hpeer2a0 : ((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗ addrUpperAt (fsp + 0x2b0#64) peerG ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ⊢ protocolAddressAt A peerG (fsp + 0x2a0#64) := by rw [protocolAddressAt_eq_parts A peerG (fsp + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]; dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)
    dsimp only [addrUpperAt] at hpeer2a0; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer2a0 hme260 ⊢
    refine Entails.trans (Entails.of_eq (show _ = (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗ (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗ ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name) ∗ (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗ (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1)) ∗ ((fsp + 0x1c0#64) ↦₆₄ u3) ∗ (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hpeer2a0 (sepConj_mono hme260 (sepConj_mono hd1d0 (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))) ?_
    have m1 := (ProofLib.memRegion_split (fsp + 0x1d0#64) 16 0x80 (by decide)).symm; dsimp only [cs7, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]; simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at m1 ⊢
    rw [show protocolAddressAt A peerG (fsp + 0x2a0#64) ∗ addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1c0#64) 8 ∗ (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 432 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 128 ∗ memRegion (fsp + 0x270#64) 48 ∗ memRegion (fsp + 0x2c0#64) 10032) = memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ (memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1e0#64) 128) ∗ addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗ protocolAddressAt A peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 10032 by ac_rfl, m1]
    have splitTail : memRegion (fsp + 0x2c0#64) 10032 = memRegion (fsp + 0x2c0#64) 528 ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1750#64) 24 ∗ memRegion (fsp + 0x1768#64) 4744 := by
      have t1 := ProofLib.memRegion_split (fsp + 0x2c0#64) 528 9504 (by decide); have t2 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 9456 (by decide); have t3 := ProofLib.memRegion_split (fsp + 0x500#64) 4688 4768 (by decide); have t4 := ProofLib.memRegion_split (fsp + 0x1750#64) 24 4744 (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at t1 t2 t3 t4; rw [t1, t2, t3, t4]
    rw [splitTail]; exact Entails.of_eq (by ac_rfl)
  let ptrIdk := lsρ r1a_idKeySym; let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
  have hdir_exp : ownedBytes A w.w4 w.w5 w.w6 dir = (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A w.w4 w.w5 dir := by rw [hw6]; exact r1a_ownedBytes_expose A w.w4 w.w5 dir
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by rw [hdir_exp]; exact show _ = ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗ (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗ ((fsp + 0x2b8#64) ↦₈ peerG.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗ (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ ((fsp + 0x1c0#64) ↦₆₄ _) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗ (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name) ∗ ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗ ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1a_ownedSlack A w.w4 w.w5 dir ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) by ac_rfl)) (sepConj_mono hpack_locals (sepConj_mono_left (r1a_call7_to_memRegion56 g.call w)))) ?_
  apply r1a_sepWPp_rodata_idkey hinva; have hsa_sp : sa.sp = fsp := by simp only [sa, arm64_norm, hsp0]
  have hsa_tr : s0.trace <+: sa.trace := by simpa only [sa, arm64_norm] using htr
  have hpath_ok := path_placed_ok (callerProg := runProgPlaced H) (i := 579) hh hpathStk; unfold pathSpecPlaced at hpath_ok
  apply r1a_call_run (hh.fs (runProgPlaced H) 579) hpath_ok (x := ({ dirA := w.w5, dir := dir, dirRo := false, nameA := ptrIdk, name := utf8 "identity-key", nameRo := true, ret := fsp + 0x1750#64 } : PathGhost)) (F := r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗ r1a_ownedSlack A w.w4 w.w5 dir ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) (retOff := 0x6a4) (by simp only [sa, arm64_norm]; rfl) (by simp only [sa, arm64_norm, hrun0]) hinva hsa_sp (by simp only [sa, arm64_norm, hbase.fp]) (by simp only [sa, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs]) hbase.spAligned (by simp only [sa, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) hpanic
    (by dsimp only [SpqrV1.ChainProofs.bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hsa_sp]
        have hpure : sa.readReg64 .x0 = fsp + 0x1750#64 ∧ sa.readReg64 .x1 = w.w5 ∧ (sa.readReg64 .x2).toNat = dir.length ∧ sa.readReg64 .x3 = ptrIdk ∧ (sa.readReg64 .x4).toNat = (utf8 "identity-key").length ∧ dir.length < 2 ^ 32 ∧ (utf8 "identity-key").length < 2 ^ 32 := ⟨by simp only [sa, arm64_norm]; rw [hsp0], by simp only [sa, arm64_norm, hx22], by simp only [sa, arm64_norm, hw6]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by omega), by simp only [sa, ptrIdk, lsρ, lsmpl, r1a_idKeySym, arm64_norm], by simp only [sa, arm64_norm]; decide +kernel, hdLen, hnLen⟩
        refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left (M3Helpers.entails_pure_intro_left hpure (Entails.refl _))))
    (fun sf => by apply Entails.pure_left; rintro ⟨haf, _⟩; obtain ⟨t, ht⟩ := hsa_tr; have haf0 : allocFailedIn s0 sf := by { unfold allocFailedIn at haf ⊢; rw [← ht, List.length_append, ← List.drop_drop] at haf; exact List.mem_of_mem_drop haf }; exact M3Helpers.entails_pure_intro_left (Or.inr haf0) (Entails.refl _))
    (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
  intro sb hbb hcsb _ hfilesb; dsimp only [SpqrV1.ChainProofs.bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]; apply r1a_sepWPp_pure_left; intro htr_ba
  refine sepWPp_weaken_pre (Entails.of_eq (show _ = (ptrIdk ↦ᵣ utf8 "identity-key") ∗ vecU8 A (fsp + 0x1750#64) pathBs ∗ ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ (r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗ r1a_ownedSlack A w.w4 w.w5 dir ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0)) by dsimp only [pathBs]; rw [hsa_sp]; ac_rfl)) ?_
  apply r1a_sepWPp_drop_left; refine sepWPp_weaken_pre (sepConj_mono_left (M3Helpers.vecU8_to_ownedBytes A (fsp + 0x1750#64) pathBs)) ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]; apply r1a_sepWPp_exists_pre; intro pathCap; apply r1a_sepWPp_exists_pre; intro pathPtr
  have hsb_fs : sb.fs.files = runFiles g.i := (hfilesb htr_ba).trans (by simpa only [sa, arm64_norm] using hfs)
  have hsb_out : ProcessOutcome.traceStreamBytes .stdout sb.trace = [] := by rw [htr_ba]; simpa only [sa, arm64_norm] using hout
  have hsb_tr : s0.trace <+: sb.trace := by rw [htr_ba]; exact hsa_tr
  have hx27_b : sb.readReg64 (.gpr 27#5) = fsp + 0x1750#64 := (by simpa only [sa, arm64_norm] using hcsb.2.2.2.2.2.2.2.2.1 : sb.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
  have hpcb := hbb.pc; have := hbb.spAligned_cur; have hrunb := hbb.run; have hspb : sb.sp = fsp := hbb.sp; change sb.pc = (blkPl_579).base + 1700#64 at hpcb
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsReadFileSym) hbb.inv; (try dsimp only [runProgPlaced, lsProg_579]); rw [← hspb]; symm at hspb; wp_simp_pre only [sepConj_assoc]; (iterate 6 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hspb
  apply SepWP.done (by simp only [lsReadFileSym, arm64_norm]) (by simp only [arm64_norm, hrunb]); intro hinvc; apply r1a_bind_sepWPp_state; intro sc; (try simp only [arm64_norm]); (try rw [hspb])
  let cs8 := cs7 ++ [(0x1750, 8, (fsp + 0x1750#64) ↦₆₄ pathCap)]
  have hctx_read : (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗ r1a_localsCtx fsp 0 cs7 0x1750 24 [] ⊢ memRegion (fsp + 0x23b0#64) 24 ∗ r1a_localsCtx fsp 0 cs8 0x23b0 24 [] := by
    have h16 : ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length) ⊢ memRegion (fsp + 0x1758#64) 16 := by have s := (ProofLib.memRegion_split (fsp + 0x1758#64) 8 8 (by decide)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]; exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right h16)) ?_; have s1 := (ProofLib.memRegion_split (fsp + 0x1758#64) 16 4744 (by decide)).symm; have s2 := ProofLib.memRegion_split (fsp + 0x1758#64) 3160 1600 (by decide); have s3 := ProofLib.memRegion_split (fsp + 0x23b0#64) 24 1576 (by decide); simp only [cs8, cs7, List.append_assoc, List.cons_append, List.nil_append]; dsimp only [r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]; simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 ⊢
    rw [show (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ memRegion (fsp + 0x1758#64) 16) ∗ (memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗ addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗ protocolAddressAt A peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1768#64) 4744) = (memRegion (fsp + 0x1758#64) 16 ∗ memRegion (fsp + 0x1768#64) 4744) ∗ memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗ addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗ protocolAddressAt A peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗ memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗ ((fsp + 0x1750#64) ↦₆₄ pathCap) by ac_rfl, s1, s2, s3]
    exact Entails.of_eq (by ac_rfl)
  have hstk_sp := r1a_stackAt_split fsp hreadStk hsub64; have hpath_exp := r1a_ownedBytes_expose A pathCap pathPtr pathBs; have hdir_back : (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A w.w4 w.w5 dir = ownedBytes A w.w4 w.w5 w.w6 dir := hdir_exp.symm; have hsc_sp : sc.sp = fsp := by simp only [sc, arm64_norm, hspb]
  have hsc_tr : s0.trace <+: sc.trace := by simpa only [sc, arm64_norm] using hsb_tr
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq (show _ = ((((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗ r1a_localsCtx fsp 0 cs7 0x1750 24 []) ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ ((w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A w.w4 w.w5 dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ (memRegion g.call 56 ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) by ac_rfl)) (by rw [hpath_exp, hdir_back, hstk_sp]; exact sepConj_mono_left hctx_read)) ?_
  apply r1a_call_run (hh.fs (runProgPlaced H) 579) (r1a_readFile_lscro_ok hc) (x := ({ pathA := pathPtr, path := pathBs, ret := fsp + 0x23b0#64 } : ReadFileGhost)) (F := r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A pathCap pathPtr pathBs ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗ memRegion g.call 56 ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) (retOff := 0x6bc) (by simp only [sc, lsReadFileSym, arm64_norm]) (by simp only [sc, arm64_norm, hrunb]) hinvc hsc_sp (by simp only [sc, arm64_norm, hbb.fp]) (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbb.vregs]) hbase.spAligned (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) hpanic
    (by (try dsimp only [readFileSpecPlaced]); rw [hsc_sp]
        have hpure : sc.readReg64 .x0 = pathPtr ∧ (sc.readReg64 .x1).toNat = pathBs.length ∧ sc.readReg64 .x8 = fsp + 0x23b0#64 ∧ pathBs.length < 2 ^ 32 ∧ cliWrOk pathBs := ⟨by simp only [sc, arm64_norm], by simp only [sc, arm64_norm]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by dsimp only [pathBs]; omega), by simp only [sc, arm64_norm]; rw [hspb], hpLen, hpOk⟩
        refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left (M3Helpers.entails_pure_intro_left hpure (Entails.refl _))))
    (fun sf => by (try dsimp only [readFileSpecPlaced]); apply Entails.pure_left; rintro ⟨haf, _⟩; obtain ⟨t, ht⟩ := hsc_tr; have haf0 : allocFailedIn s0 sf := by { unfold allocFailedIn at haf ⊢; rw [← ht, List.length_append, ← List.drop_drop] at haf; exact List.mem_of_mem_drop haf }; exact M3Helpers.entails_pure_intro_left (Or.inr haf0) (Entails.refl _))
    (fun _ _ => by (try dsimp only [readFileSpecPlaced]); exact Entails.refl _) (fun _ => by (try dsimp only [readFileSpecPlaced]); exact r1a_false_entails)
  intro sd hbd hcsd _ hfilesd; (try dsimp only [readFileSpecPlaced]); simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply r1a_sepWPp_exists_pre; intro r; apply r1a_sepWPp_pure_left; intro hpost_r
  obtain ⟨htr_d, herr_f, hok_f⟩ := r1a_readFile_post_facts he hd hcall hsc_tr (by simpa only [sc, arm64_norm] using hsb_fs) (by simpa only [sc, arm64_norm] using hsb_out) hfilesd (by simpa only [sc, pathBs] using hpost_r)
  have hremerge : ioVecAt A (fsp + 0x23b0#64) r ∗ (pathPtr ↦ₛ pathBs) ∗ stackAt sc.sp B.readFile ∗ A.pool ∗ (r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A pathCap pathPtr pathBs ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗ memRegion g.call 56 ∗ addrNameHeap A meG ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0) = runLocals fsp (cs8 ++ [(0x23b0, 24, ioVecAt A (fsp + 0x23b0#64) r)]) ∗ ownedBytes A pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool := by rw [hsc_sp, r1a_locals_focus fsp cs8 0x23b0 24 (ioVecAt A (fsp + 0x23b0#64) r) [], hpath_exp, hstk_sp]; ac_rfl
  rw [hremerge]; exact r1a_after_read hh hdrop he hd hcall hpanic hrej hnext hikStk hstk32 hsub64 hbd (by simpa only [sc, sa, arm64_norm, hx19] using hcsd.1.trans hcsb.1) (by simpa only [sc, sa, arm64_norm, hx20] using hcsd.2.1.trans hcsb.2.1) (by simpa only [sc, sa, arm64_norm, hx21] using hcsd.2.2.1.trans hcsb.2.2.1) (by simpa only [sc, sa, arm64_norm, hx22] using hcsd.2.2.2.1.trans hcsb.2.2.2.1) (by simpa only [sc, sa, arm64_norm, hx24] using hcsd.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.1) (by simpa only [sc, arm64_norm] using hcsd.2.2.2.2.2.2.2.1) (by simpa only [sc, sa, arm64_norm, hw6] using hcsd.2.2.2.2.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.2.2.2.2.1) hw6 hw2 htr_d herr_f hok_f

theorem run_hop_init1_of_slots [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs)) :
    RunHopInit1PlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S slots resStack := by
  intro g s0 s me peerV dir Q Qp hh hc hdrop hres hres64 he hd hcall hpanic hrej hnext
  rw [hneed_eq] at hres
  obtain ⟨_, _, hsub64, _, _, hreadStk, hpathStk, _, _, _, _, hikStk, _, _, hstk32, _, hext, _⟩ := runNeed_bounds_placed hres hres64
  have htag : s.readReg64 (.gpr 8#5) = 1#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hpc0 := hd.base.pc; have := hd.base.spAligned_cur; have hrun0 := hd.base.run; change s.pc = (blkPl_579).base + 532#64 at hpc0
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x654) hd.base.inv; try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]); intro hinv1; apply r1a_bind_sepWPp_state; intro s1
  have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x654 := r1a_inRun (by simp only [runPcPlaced_eq, arm64_norm, s1, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, s1, hrun0]) (by simp only [arm64_norm, s1, hd.base.sp]) (by simp only [arm64_norm, s1, hd.base.fp]) hinv1 (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hd.base.vregs]) hd.base.spAligned
  have htr1 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using hd.trace
  have hfs1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hd.fs
  have hout1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [] := by simpa only [arm64_norm, s1] using hd.stdout
  have hcall_eq : callAt A g.call g.c = callAt A g.call (.init peerV dir) := congrArg (callAt A g.call) hcall
  unfold dispatchMemPlaced; rw [hcall_eq]; dsimp only [callAt, callHeap, addrWords]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply r1a_sepWPp_exists_pre; intro w
  have hp_w (A0 W0 W1 W2 W3 W4 W5 W6 N0 P' R' : SepProp) : A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ P' ∗ R' = P' ∗ A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ R' := by ac_rfl
  rw [hp_w]; apply r1a_sepWPp_pure_left; intro hw3
  rcases me with _ | ⟨meV, meG⟩
  · dsimp only [dispatchMeHeap, dispatchCells]
    exact sepWPp_weaken_pre (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; ac_rfl)) (r1a_init_none_branch (peerV := peerV) (dir := dir) (w := w) (F_heap := coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) hh he hd hpanic hrej hext hsub64 hb1 (by simp only [s1, arm64_norm, hd.x19]) (by simp only [s1, arm64_norm, hd.x20]) (by simp only [s1, arm64_norm, hd.meRegs]) (by simp only [s1, arm64_norm, hd.x25]) htr1 hfs1 hout1)
  · dsimp only [dispatchMeHeap, dispatchCells]; rcases hd.meRegs with ⟨hx21_0, hx28_0, _, _, _⟩
    have hmep := M3Helpers.ownedBytes_pure A meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes; have hpeerp := M3Helpers.ownedBytes_pure A w.w0 w.w1 w.w2 peerV.name; have hdirp := M3Helpers.ownedBytes_pure A w.w4 w.w5 w.w6 dir
    refine sepWPp_weaken_pre (Entails.of_eq (show _ = addrNameHeap A meG ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ (memRegion g.res runResSize ∗ ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool) by ac_rfl)) ?_
    rw [r1a_addrNameHeap_eq_owned meG, hmep, hpeerp, hdirp, ← r1a_addrNameHeap_eq_owned meG]
    have hp3 {P1 P2 P3 : Prop} (A1 A2 A3 R0 : SepProp) : (⌜P1⌝ ∗ A1) ∗ (⌜P2⌝ ∗ A2) ∗ (⌜P3⌝ ∗ A3) ∗ R0 = ⌜P1⌝ ∗ ⌜P2⌝ ∗ ⌜P3⌝ ∗ (A1 ∗ A2 ∗ A3 ∗ R0) := by ac_rfl
    rw [hp3]; apply r1a_sepWPp_pure_left; rintro ⟨_, _, hme_lt, _⟩; apply r1a_sepWPp_pure_left; rintro ⟨hw2, _, _, _⟩; apply r1a_sepWPp_pure_left; rintro ⟨hw6, _, _, _⟩
    refine sepWPp_weaken_pre (Entails.of_eq (show _ = runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗ ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗ addrNameHeap A meG ∗ ownedBytes A w.w4 w.w5 w.w6 dir ∗ ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool by ac_rfl)) ?_
    have hcmn : (meG.name.cap + 1#64 == 0#64) = false := M3Helpers.beq_add_one_zero_false_of_lt hme_lt
    have hcarve := r1a_locals_carve_region (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 []
    have hf2a0 := r1a_locals_focus (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 (memRegion (runFsp s0 + 0x2a0#64) 32) []
    have h32 : memRegion (runFsp s0 + 0x2a0#64) 32 = (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64, ((runFsp s0 + 0x2a0#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ q1) ∗ ((runFsp s0 + 0x2b0#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ q3)) := by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x2a0#64)
    simp only [List.nil_append, List.append_nil] at hcarve hf2a0; rw [hcarve, hf2a0, h32]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro q0; apply r1a_sepWPp_exists_pre; intro q1; apply r1a_sepWPp_exists_pre; intro q2; apply r1a_sepWPp_exists_pre; intro q3
    have hpc1 := hb1.pc; have hal0 : (s0.sp &&& 15#64 == 0#64) = true := hd.base.spAligned; have hal1 : (s1.sp &&& 15#64 == 0#64) = true := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp; change s1.pc = (blkPl_579).base + 1620#64 at hpc1
    have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [s1, arm64_norm, hx21_0]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = g.call := by simp only [s1, arm64_norm, hd.x25]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x668) hb1.inv; (try dsimp only [runProgPlaced, lsProg_579]); rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]
    (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]))); symm at hsp1
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]); intro hinv2; apply r1a_bind_sepWPp_state; intro s2; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx25_1]); (try rw [hsp1])
    exact sepWPp_weaken_pre (Entails.of_eq (by rw [hw2]; ac_rfl)) (r1a_some_after_668 (peerV := peerV) (dir := dir) (w := w) hh hc hdrop he hd hcall hpanic hrej hnext hpathStk hreadStk hikStk hstk32 hsub64 (r1a_inRun (by simp only [runPcPlaced_eq, arm64_norm, s2, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, s2, hrun1]) (by simp only [arm64_norm, s2, hsp1]) (by simp only [arm64_norm, s2, hb1.fp]) hinv2 (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s2, hb1.vregs]) hd.base.spAligned) (by simp only [arm64_norm, s2, s1, hd.x19]) (by simp only [arm64_norm, s2, s1, hd.x20]) (by simp only [arm64_norm, s2, hx21_1]) (by simp only [arm64_norm, s2]) (by simp only [arm64_norm, s2]) (by simp only [arm64_norm, s2, hx25_1]) (by simp only [arm64_norm, s2, s1, hd.x27]) (by simp only [arm64_norm, s2, s1, hx28_0]) hw6 hw2 hw3 (by simpa only [arm64_norm, s2] using htr1) (by simpa only [arm64_norm, s2] using hfs1) (by simpa only [arm64_norm, s2] using hout1))

theorem run_hop_init1_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopInit1Placed (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S needs resStack :=
  run_hop_init1_of_slots (needs := needs) rfl

end CryptoVerification.SignalSession.Cli.RunCompose
