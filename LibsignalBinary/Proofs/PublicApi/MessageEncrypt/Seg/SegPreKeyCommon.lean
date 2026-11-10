/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Stack
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.Common.StringCloneFlat

/-!
# Shared Helpers and Hook Bridges for `segPreKey`

Pure `SystemTime` comparison lemmas, callee/hook `subroutine_ok` projections at `encEntry img`,
`.rodata` `"message_encrypt"` literal lemmas, `SegExit` combinators, and error-answer witnesses for
`segPreKey`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure Model and `SystemTime` Lemmas -/

theorem checkedAddSecs_tvNsec {t ts : SystemTime} {s : Nat}
    (h : t.checkedAddSecs s = some ts) : ts.tvNsec = t.tvNsec := by
  unfold SystemTime.checkedAddSecs at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · simp at h

theorem unixEpoch_checkedAddSecs_tvNsec {s : Nat} {ts : SystemTime}
    (h : SystemTime.unixEpoch.checkedAddSecs s = some ts) :
    ts.tvNsec = 0#32 ∧ ts.tvNsec.toNat < 10 ^ 9 := by
  have h1 := checkedAddSecs_tvNsec h
  have h2 : SystemTime.unixEpoch.tvNsec = 0#32 := rfl
  rw [h2] at h1
  exact ⟨h1, by rw [h1]; decide⟩

theorem checkedAddSecs_tvNsec_lt_of_unixEpoch {s1 s2 : Nat} {ts expiry : SystemTime}
    (h1 : SystemTime.unixEpoch.checkedAddSecs s1 = some ts)
    (h2 : ts.checkedAddSecs s2 = some expiry) :
    expiry.tvNsec = 0#32 ∧ expiry.tvNsec.toNat < 10 ^ 9 := by
  have ⟨hts0, _⟩ := unixEpoch_checkedAddSecs_tvNsec h1
  have hexp := checkedAddSecs_tvNsec h2
  rw [hts0] at hexp
  exact ⟨hexp, by rw [hexp]; decide⟩

/-! ## `SystemTime.lt` Instruction Bridge (`+0x704..+0x71c`) -/

theorem systemTime_lt_cond_eq (a b : SystemTime) :
    (if a.tvSec == b.tvSec then a.tvNsec.ult b.tvNsec else a.tvSec.slt b.tvSec) = a.lt b := by
  unfold SystemTime.lt
  by_cases h : a.tvSec = b.tvSec
  · have hslt : b.tvSec.slt b.tvSec = false := by simp [BitVec.slt]
    simp [h, hslt, BitVec.ult, BitVec.lt_def]
  · have hbeq : (a.tvSec == b.tvSec) = false := beq_false_of_ne h
    simp [hbeq]

/-! ## Callee and Hook Address Projections -/

theorem encEntry_eq_fnAddr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt env.loads encryptWithStoresName

theorem encEntry_eq_base_add {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    encEntry img = img.base + 0x3cbd8#64 := by
  rw [encEntry_eq_fnAddr env, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x3cbd8]

theorem unack_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + 18446744073709377668#64) (unackItemsSpec A img) := by
  have h := env.callees.unack
  unfold UnackItemsOk at h
  have haddr : img.base + 0x1245c#64 = encEntry img + 18446744073709377668#64 := by
    rw [encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem kyber_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + 18446744073709516640#64) (kyberMapSpec A) := by
  have h := env.callees.kyber
  unfold KyberMapOk at h
  have haddr : img.base + 0x34338#64 = encEntry img + 18446744073709516640#64 := by
    rw [encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem otrEnc_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + 18446744073709515544#64) (otrEncryptSpecQ Q C A ctl uuidTryParse S img) := by
  have h := env.callees.otrEnc
  unfold OtrEncryptOkQ at h
  have haddr : (tripleRatchetProgAt img.base C ctl abs).fnAddr otrEncryptName =
      encEntry img + 18446744073709515544#64 := by
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x33ef0, encEntry_eq_base_add env]
    bv_omega
  rwa [← haddr]

theorem preKeyMsgNew_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + 18446744073709389144#64) (preKeyMsgNewSpec A) := by
  have h := env.callees.psmNew
  unfold PreKeyMsgNewOk at h
  have haddr : img.base + 0x15130#64 = encEntry img + 18446744073709389144#64 := by
    rw [encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem timeAdd_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + bv% (ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - 0x3cbd8)) timeAddSpec := by
  rw [encEntry_eq_fnAddr env]
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h4 : Rust.withPanics (tripleRatchetExterns C ctl abs) timeAddHookName =
      abs timeAddHookName := Option.some.inj (congrArg (·[4]?) habs)
  refine hook_ok_at_raw (hname := timeAddHookName) (stub := num% (ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"))
    libsignalSessionCode_fnOff_0x3cbd8 (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add") ?_
  simpa [HookSat, h4] using env.hooks.timeAdd

theorem durationSince_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + bv% (ls_off% "<std::time::SystemTime>::duration_since" - 0x3cbd8)) durationSinceSpec := by
  rw [encEntry_eq_fnAddr env]
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h5 : Rust.withPanics (tripleRatchetExterns C ctl abs) durationSinceHookName =
      abs durationSinceHookName := Option.some.inj (congrArg (·[5]?) habs)
  refine hook_ok_at_raw (hname := durationSinceHookName) (stub := num% (ls_off% "<std::time::SystemTime>::duration_since"))
    libsignalSessionCode_fnOff_0x3cbd8 (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime>::duration_since") ?_
  simpa [HookSat, h5] using env.hooks.durationSince

theorem stringClone_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (encEntry img + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8)) (stringCloneSpec A) := by
  rw [encEntry_eq_fnAddr env]
  exact sub_ok_at_of_fnAddr
    (LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok img.base C A ctl abs env.hooks.alloc)
    encryptWithStoresName (num% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8))
    (by simp only [libsignalSessionCode_fnOff_0x3cbd8,
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff, arm64_norm])

/-! ## `.rodata` `"message_encrypt"` Literal -/

open ProofLib.ProgramReflection in
theorem rodata_0x4a6a0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% 0x3cdb0 0x3cdb4) - num% (ls_xref% 0x2440 0x2444))).take 15 = utf8 "message_encrypt" := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_message_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% 0x3cdb0 0x3cdb4)) (secLen := 15) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) rodata_0x4a6a0_eq hro hP

theorem rodata_message_encrypt_sepWPp {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWPp prog ret s (((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_message_encrypt_intro himg hro hm

theorem adrp_0x4a6a0_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + 248792#64 = entry) :
    ((entry + 1968#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x3cdb0 0x3cdb4 - 0x3d000)) = base + bv% (ls_xref% 0x3cdb0 0x3cdb4) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem adrp_0x4b000_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + 248792#64 = entry) :
    ((entry + 1816#64 &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x3d000)) = base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem SepWPp.of_sepWP_ret {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hpost⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.of_sepWP {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hcont R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.call_frame {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hf : P = T ∗ F)
    (hexit : ∀ code sf R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R')) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R' hm hL
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
    rw [hf, sepConj_assoc] at hm
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex_st, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpan sm hpan_st⟩)⟩
  · exact (hexit code sm R' hex_st hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R' hoom_st hpost⟩)⟩

/-! ## `SegExit` Combinators -/

theorem segExit_trans {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem segExit_of_false {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {next : State → Prop}
    (h : SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False)) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact hfalse.elim
  · exact ⟨sf, hst, Or.inr hout⟩

theorem onPanic_absorb_extra {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 sf : State} {R0 : SepProp}
    (h : sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
      (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) :
    sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  dsimp only [withStoresEncSpecV, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h.2

theorem segExit_of_sepWPp {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {next : State → Prop}
    (hm : s.mem ⊨ P ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) → next sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) →
        (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
          (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)))) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, onPanic_absorb_extra (hqp hmf)⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segExit_of_sepWP {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {next : State → Prop}
    (hinv : CallInv img s)
    (hm : s.mem ⊨ P ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => CallInv img sf → (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) → next sf)) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hinv.of_steps hsteps) hmf)⟩

/-! ## Store-Answer Witnesses for Early Exits -/

def preKeyErrAnswers (r : SessionRecord (List (BitVec 8))) :
    StoreAnswers (List (BitVec 8)) Unit :=
  okAnswers r .newOrUnchanged

theorem allocFailedIn_of_prefix {s0 s sf : State} (hpref : s0.trace <+: s.trace)
    (ha : allocFailedIn s sf) : allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := hpref
  unfold allocFailedIn at ha ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem onPanic_of_alloc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F R : SepProp}
    (hpref0 : s0.trace <+: s.trace)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨ha, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  refine ⟨⟨hpref0.trans hpref, Or.inl (allocFailedIn_of_prefix hpref0 ha)⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem model_of_unack_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = none) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts]

theorem onPanic_of_unack {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hm : sf.mem ⊨ (⌜(∃ items', ({ sess with state := taken } : Session (List (BitVec 8))).pendingPreKey = some items' ∧
        SystemTime.unixEpoch.checkedAddSecs items'.timestamp.toNat = none) ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨⟨items', hpk', hts⟩, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  simp only [hpk, Option.some.injEq] at hpk'
  subst hpk'
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, Or.inr ⟨preKeyErrAnswers r, hsc.2, ?_, ?_⟩⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_unack_panic hcur hfrom hrem hpk hts)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem model_of_timeAdd_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = none) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts, hexp]

theorem onPanic_of_timeAdd {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts : SystemTime} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hm : sf.mem ⊨ (⌜ts.checkedAddSecs maxUnacknowledgedSessionAge = none ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hexp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, Or.inr ⟨preKeyErrAnswers r, hsc.2, ?_, ?_⟩⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_timeAdd_panic hcur hfrom hrem hpk hts hexp)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem model_of_stale {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = true) :
    x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) ∧
    x.draws S (preKeyErrAnswers r) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte]
  · unfold EncryptGhost.draws EncryptGhost.sendState loadedSession preKeyErrAnswers okAnswers
    simp only [hcur, hfrom, hrem, Option.isNone, hpk, hts, hexp, hlt, Option.bind, ↓reduceIte,
      Bool.false_eq_true]

theorem sendState_of_not_stale {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false) :
    x.sendState (preKeyErrAnswers r) = some otr.pqrState := by
  unfold EncryptGhost.sendState loadedSession preKeyErrAnswers okAnswers
  simp only [hcur, hfrom, hrem, Option.isNone, hpk, hts, hexp, hlt, Option.bind, ↓reduceIte,
    Bool.false_eq_true]

theorem draws_of_not_stale {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false) :
    x.draws S (preKeyErrAnswers r) = S.draws otr.pqrState x.rest := by
  unfold EncryptGhost.draws
  rw [sendState_of_not_stale hcur hfrom hrem hpk hts hexp hlt]

def preKeyOtrGhost (x : WithStoresEncGhost) (sp pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) : OtrEncryptGhost where
  ret := sp + 0x580#64
  o := sp + 0x288#64
  pqCap := pqCap
  pqPtr := pqPtr
  ot := otr
  ptA := x.ptA
  ptext := x.ptext
  locA := x.locA
  loc := some x.loc
  remA := x.remA
  rem := x.rem
  cur := x.cur
  rest := x.rest

theorem execOk_of_preKeyOtrGhost_error {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {sp pqCap pqPtr : BitVec 64}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {e : SignalProtocolError}
    (h : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error e) :
    execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
      (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr = .error e := by
  unfold execOk
  change (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).1 = .error e at h
  rcases hm : Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr with ⟨_ | _, _⟩ <;>
    simp_all

theorem execOk_of_preKeyOtrGhost_ok {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {sp pqCap pqPtr : BitVec 64}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (h : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm) :
    execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
      (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr =
      .ok (sm, ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2) := by
  unfold execOk
  change (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).1 = .ok sm at h
  change _ = Except.ok (sm, (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).2)
  rcases hm : Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr with ⟨_ | _, _⟩ <;>
    simp_all

theorem model_of_otr_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hotr : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  have hexec := execOk_of_preKeyOtrGhost_error hotr
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
    hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec, ApiError.ofProtocol]

theorem onPanic_of_otrEnc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hm : sf.mem ⊨ (⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
        S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s sf) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  have htr' : s0.trace ++ kit.loadEvs encRecord x.rem.val (preKeyErrAnswers r).loadSession <+: sf.trace := by
    rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  refine ⟨⟨hpref0, ?_⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  rcases hp with hotr | hsp | halloc
  · exact Or.inr ⟨preKeyErrAnswers r, hsc.2, htr',
      Or.inl (model_of_otr_panic hcur hfrom hrem hpk hts hexp hlt hotr)⟩
  · refine Or.inr ⟨preKeyErrAnswers r, hsc.2, htr', Or.inr ?_⟩
    unfold EncryptGhost.sendPanics
    rw [sendState_of_not_stale hcur hfrom hrem hpk hts hexp hlt]
    exact ⟨otr.pqrState, rfl, hsp⟩
  · refine Or.inl (allocFailedIn_of_prefix ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), ?_⟩ halloc)
    exact htr.symm

theorem tailModel_of_otr_err {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {e : SignalProtocolError}
    {s0 s : State}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (herr : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error e) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (ApiError.ofProtocol e)) s0 s := by
  have hexec := execOk_of_preKeyOtrGhost_error herr
  have hm : x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
  refine ⟨⟨congrArg Prod.fst hm, by rw [congrArg Prod.snd hm]; exact ⟨hsc.2, trivial⟩,
    by rw [congrArg Prod.snd hm]; exact trivial⟩, ?_⟩
  rw [congrArg Prod.snd hm, htr, ikit.traceOfWith_load]
  rfl

theorem stepsThroughEncrypt_of_preKey_ok {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {sm : SignalMessage}
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hok : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm) :
    let otr' := ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2
    let psm := PreKeySignalMessage.new otr'.sessionVersion sess.localRegistrationId
      items.preKeyId items.signedPreKeyId
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
      items.baseKey otr'.localIdentityKey sm
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k
      (.preKeySignalMessage psm) otr' := by
  intro otr' psm
  refine ⟨hcur, hscope, hfrom, hrem, ?_⟩
  unfold EncEncryptStep
  rw [hpk]
  exact ⟨ts, expiry, sm, hts, hexp, hlt, execOk_of_preKeyOtrGhost_ok hok, rfl⟩

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
