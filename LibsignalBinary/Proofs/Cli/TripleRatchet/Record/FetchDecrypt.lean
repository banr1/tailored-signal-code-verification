/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction Decode Fetches and Model Bridges for CLI `SegDecrypt` and `SegMismatch`

Provides `segDecrypt_rec_fetches_cli`, instruction decode lemmas, and `RecordDecryptGhost` model/tape
bridges for the decrypt and version-mismatch segments of CLI `signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet




/-- Adds `libsignalSessionCode_fetch_fnAddr` hypotheses for `signal_session_ratchet::decrypt_signal`
from relative offset `k0` over `len` bytes. -/
macro "segDecrypt_rec_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode segDecryptBinCli $b $H
    $hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) $k0 $len)

/-! ## Decode Lemmas -/

gen_decodes libsignalSessionCode_tree segDecryptBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1692) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1712), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1716), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1720) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1752), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1984) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2004), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2008), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2012) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2056), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2060), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2064) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2080), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2084), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2088) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2124), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5948) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6020), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6024), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6028) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6044), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6048), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6052) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6096), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6100), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7812), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7816)]

macro "segDecrypt_mismatch_fetches_cli" : term =>
  `([(ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2020)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2024)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2028)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2032)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2036)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2040)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2044)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2048)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2052)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2056)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2060)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2064)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2068)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2072)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2076)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2080)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2084)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2088)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2092)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2096)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2100)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2104)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2108)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2112)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2116)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2120)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2124))])

macro "segDecrypt_decrypt_fetches_cli" : term =>
  `([(ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1692)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1696)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1700)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1704)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1708)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1712)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1716)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1720)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1724)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1728)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1732)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1736)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1740)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1744)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1748)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1752)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1984)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1988)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1992)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1996)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2000)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2004)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2008)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2012)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2016)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5948)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5952)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5956)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5960)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5964)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5968)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5972)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5976)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5980)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5984)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5988)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5992)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 5996)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6000)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6004)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6008)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6012)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6016)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6020)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6024)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6028)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6032)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6036)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6040)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6044)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6048)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6052)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6056)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6060)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6064)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6068)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6072)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6076)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6080)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6084)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6088)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6092)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6096)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6100)),
     (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7812)), (ls_decode% segDecryptBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7816))])

namespace SegDecryptFacts

/-! ## Model and Coins-Tape Bridges -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_zero (ctl : BitVec 64) (cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  simp [CryptoVerification.SignalSession.Coins.coinsAfter, CryptoVerification.SignalSession.Coins.tapeAfter2, CryptoVerification.SignalSession.Coins.coinsAt, CryptoVerification.SignalSession.Coins.tapeAt2]
  exact Entails.pure_left fun _ => Entails.refl _

end SegDecryptFacts

end CryptoVerification.LibsignalTripleRatchet.Record
