#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Hygiene check for `Symbolic/Specifications/` and the symbolic theorems (`Symbolic/Theorems/`):
# - Scans `files` for `sorry` (checked against `intended_files`), `axiom`, `admit`,
#   `native_decide`, `unsafe`, and `implemented_by`.
# - Prints axioms of the headline theorems and rejects `sorryAx` outside `intended_names`.
# - Verifies via `scripts/TrustedClosure.lean --symbolic` that `trusted=()` matches the
#   theorem-statement closure and excludes proof and forbidden `CryptoGames` modules.
# - Checks that trusted specs contain only `kept_theorems` and no raw symbol string literals
#   outside `ImageSymbols.lean` (except `str_allow_*`).
# Pass `--self-test` to run only the scratch-copy negative controls (no `lake` needed).
set -euo pipefail
# Run from the repository root.
cd "$(dirname "$0")/../.."
# Repo-local, gitignored scratch output.
out=.lake/refinement_hygiene
mkdir -p "$out"

# `CryptoGames` primitive definitions (types, records, and reference functions, with no games,
# advantages, or bounds) allowed in the statement closure of `compExternsSatisfiableCli` only.
# The two `CliElfLib` headlines (`signal_session_secure_placed`, `comp_refines_cli_placed`) are
# checked separately in CI after `lake build CliElfLib`; this script passes the 12 default-build
# headlines in `default_symbolic_headlines` below.
cli_cryptogames=(
  # AES-CBC decryption (`cbcDecRaw`, `cbcDecryptBlocks`, `chunks16`, `pkcs7Unpad`, `blockToBytesLE`).
  LibsignalBinary/Specifications/CryptoGames/AEAD/CBCDecDefs.lean
  # AES-CBC PKCS#7 encryption (`cbcPkcs7EncryptOnly`, `cbcScheme`, `cbcEncrypt`, `pkcs7Bytes`,
  # `pkcs7Blocks`, `padLen`, `nBlocks`) and block types (`Block`, `AesKey`, `Plain`, `bytesToBlock`).
  LibsignalBinary/Specifications/CryptoGames/AEAD/CBCDefs.lean
  # `CipherScheme` record (type of `cbcScheme`).
  LibsignalBinary/Specifications/CryptoGames/AEAD/EtMDefs.lean
  # `bytesToKey32` conversion read by `HooksMatchInterpretation`.
  LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean
  # `ShaState` (state type of `ShaCompress`).
  LibsignalBinary/Specifications/CryptoGames/AEAD/HMACDefs.lean
  # `X25519Fn` (field type in `Crypto`).
  LibsignalBinary/Specifications/CryptoGames/Ratchet/CreateChainDefs.lean
  # `Crypto` record, `ShaCompress`, `PubKeyFn`, `aesCbcEncrypt`, and `aesCbcDecrypt`.
  LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSession.lean
)
# Statement files whose source imports reach `LibsignalBinary/Specifications/` modules outside
# the constant-level statement closure (via `ElfBinding.lean` and `CliBinaryPq.lean`). The
# import-closure check below permits extra `LibsignalBinary/Specifications/` imports only from
# `cli_wit`.
cli_wit=(
  Symbolic/Specifications/Refinement/ElfBinding.lean
  # `SignalSessionSecureFor` (used by `CompRefinementPreservationCli`) lives next to the
  # ELF-level headline, so `Binary.lean` and `RefinementPreservation.lean` import `ElfBinding.lean`.
  Symbolic/Specifications/Security/Binary.lean
  Symbolic/Specifications/Refinement/RefinementPreservation.lean
  LibsignalBinary/Specifications/SignalSession/CliRun.lean
  LibsignalBinary/Specifications/LibsignalE2E/PqxdhInputs.lean
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean
  "${cli_cryptogames[@]}"
)
cli_trusted=(
  Symbolic/Specifications/Refinement/Statement.lean
  Symbolic/Specifications/Refinement/CliSetup.lean
  Symbolic/Specifications/Security/AsmSecure.lean
  LibsignalBinary/Specifications/SignalSession/Run.lean
  LibsignalBinary/Specifications/RecordCodecs/Proto.lean
  "${cli_wit[@]}"
)

# `.lean` files scanned for `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, and `implemented_by`.
shopt -s globstar nullglob
files=(
  Symbolic/Specifications/Concrete/*.lean
  Symbolic/Specifications/Refinement/WireFormat.lean
  Symbolic/Specifications/Refinement/Concretization.lean
  Symbolic/Specifications/Refinement/ModelTraces.lean
  Symbolic/Specifications/Refinement/TraceExplanation.lean
  LibsignalBinary/Specifications/AsmConstants.lean
  Symbolic/Specifications/Model/EquationalTheory/*.lean
  Symbolic/Specifications/Model/*.lean
  Symbolic/Specifications/Security/Model.lean
  Symbolic/Tests/**/*.lean
  # Shared wire-format definitions (trusted) and Rust allocator contracts (scanned here; omitted
  # from `trusted=()` because no theorem statement references them).
  LibsignalBinary/Specifications/LibsignalSignalMessage.lean
  LibsignalBinary/Specifications/RustHeap/Alloc.lean
  # Top-level composed helper and theorem modules, plus `CliElfLib` sources scanned as text
  # without a `CliElfLib` build (`Security/Binary.lean` is included via `cli_trusted`).
  Symbolic/Proofs/TopLevelHelpers/Composed/*.lean
  Symbolic/Proofs/TopLevelHelpers/Composed/Cli/*.lean
  Symbolic/Theorems/*.lean
  "${cli_trusted[@]}"
)
echo "scanning ${#files[@]} files"

# Trusted specification files: must equal the repository theorem-statement closure reported by
# `scripts/TrustedClosure.lean --symbolic` (`check_closure_trusted`).
trusted=(
  Symbolic/Specifications/Concrete/*.lean
  Symbolic/Specifications/Refinement/WireFormat.lean
  Symbolic/Specifications/Refinement/Concretization.lean
  Symbolic/Specifications/Refinement/ModelTraces.lean
  Symbolic/Specifications/Refinement/TraceExplanation.lean
  Symbolic/Specifications/Model/EquationalTheory/*.lean
  Symbolic/Specifications/Model/*.lean
  Symbolic/Specifications/Security/Model.lean
  LibsignalBinary/Specifications/LibsignalSignalMessage.lean
  "${cli_trusted[@]}"
)

# Exemption 1 (`kept_theorems`): exact `file:name` allowlist of theorems in `trusted=()`
# (`check_spec_theorems` rejects both unlisted theorems and stale entries). All 14 live in
# `LibsignalBinary/Specifications/` modules reached via `cli_wit` and are `sorry`-free:
# - `MlKem.fromSeed_pk1`, `fromSeed_pk2` (used by `LibsignalSpqrV1/Hooks.lean`) and their `rfl`
#   siblings `fromSeed_dk`, `fromSeed_hdr`, `fromSeed_ek`.
# - `indcpaAdvantage_eq_boolDist`, `prfAdvantage_eq_boolDist` (used by `AEAD/CBC.lean` and
#   `AEAD/EtM.lean`).
# - `etm_correct`, the four HKDF effective-salt lemmas (DEV-LS25), and `tryDecryptFromRecord_error`
#   / `messageEncrypt_error` in `LibsignalSession.lean`, kept alongside their definitions.
kept_theorems=(
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean:MlKem.fromSeed_dk
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean:MlKem.fromSeed_hdr
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean:MlKem.fromSeed_ek
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean:MlKem.fromSeed_pk1
  LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean:MlKem.fromSeed_pk2
  LibsignalBinary/Specifications/CryptoGames/AEAD/EtMDefs.lean:indcpaAdvantage_eq_boolDist
  LibsignalBinary/Specifications/CryptoGames/AEAD/EtMDefs.lean:prfAdvantage_eq_boolDist
  LibsignalBinary/Specifications/CryptoGames/AEAD/EtMDefs.lean:etm_correct
  LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean:hmacWith_append_zeros
  LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean:hkdfExtractRaw_eq_saltKey
  LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean:hkdfExtract_effSalt
  LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean:msgKeys_effSalt
  LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSession.lean:tryDecryptFromRecord_error
  LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSession.lean:messageEncrypt_error
)

# Exemption 2 (`str_allow_*`): bundle file-name literals and `"/"` in `WireFormat.parseBundleFiles`
# (from `read_bundle` in `third_party/libsignal/libsignal-session/cli/src/public.rs`).
# Scoped from `def parseBundleFiles` up to the next blank line, column-0 line, or declaration
# keyword at any indentation (exclusive); `scan_spec_strings` rejects any unlisted literal or
# missing listed literal.
str_allow_file=Symbolic/Specifications/Refinement/WireFormat.lean
str_allow_def=parseBundleFiles
str_allow_lits=('"/"' '"identity-key"' '"registration-id"' '"signed-pre-key"' '"kyber-pre-key"'
  '"one-time-pre-key"')

# List `theorem`, `lemma`, and `example` declarations in the given files as `file:name`.
list_spec_theorems() {
  (( $# )) || return 0
  awk '
    /^[[:space:]]*\/-/ { inc = 1 }
    inc { if ($0 ~ /-\//) inc = 0; next }
    { sub(/--.*/, "") }
    /^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((public|private|protected|noncomputable)[[:space:]]+)*(theorem|lemma|example)([[:space:]]|$)/ {
      name = $0; sub(/^.*(theorem|lemma|example)[[:space:]]*/, "", name); sub(/[[:space:]].*$/, "", name)
      print FILENAME ":" name
    }
  ' "$@"
}

# Verify that the sorted theorem list in `$1` matches `kept_theorems` exactly.
check_spec_theorems() {
  local found unkept stale rc=0
  found=$(LC_ALL=C sort -u "$1")
  unkept=$(LC_ALL=C comm -23 <(printf '%s\n' "$found" | sed '/^$/d') \
    <(printf '%s\n' "${kept_theorems[@]}" | LC_ALL=C sort -u))
  stale=$(LC_ALL=C comm -13 <(printf '%s\n' "$found" | sed '/^$/d') \
    <(printf '%s\n' "${kept_theorems[@]}" | LC_ALL=C sort -u))
  if [[ -n "$unkept" ]]; then
    echo "FAIL: theorems in the trusted specification files:"
    echo "$unkept" | sed 's/^/  /'; rc=1
  fi
  if [[ -n "$stale" ]]; then
    echo "FAIL: kept_theorems entries with no such theorem (delete them):"
    echo "$stale" | sed 's/^/  /'; rc=1
  fi
  return "$rc"
}

# Report raw string literals outside `ImageSymbols.lean` (modulo `str_allow_*`).
scan_spec_strings() {
  local f seen=0
  for f in "$@"; do
    [[ "$f" == "Symbolic/Specifications/Concrete/ImageSymbols.lean" ]] && continue
    [[ "$f" == "$str_allow_file" ]] && seen=1
    awk -v F="$f" -v AF="$str_allow_file" -v AD="$str_allow_def" -v AL="${str_allow_lits[*]}" '
      function strip(lit,   i, n) {
        n = 0
        while ((i = index(line, lit)) > 0) { line = substr(line, 1, i - 1) substr(line, i + length(lit)); n++ }
        return n
      }
      BEGIN {
        na = split(AL, al, " ")
        DECL = "^[[:space:]]*(@\\[[^]]*\\][[:space:]]*)?((public|private|protected|noncomputable|partial|unsafe)[[:space:]]+)*(def|theorem|lemma|example|abbrev|instance|structure|inductive|class|opaque|axiom|namespace|section|end)([[:space:]]|$)"
      }
      /^[[:space:]]*\/-/ { inc = 1 }
      inc { if ($0 ~ /-\//) inc = 0; next }
      { sub(/--.*/, "") }
      { gsub(/"WhisperRatchet"|"WhisperMessageKeys"|"WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"|"spec::x25519_add_eight_torsion"/, "") }
      F == "Symbolic/Specifications/Refinement/CliSetup.lean" {
        gsub(/"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"|"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"/, "") }
      F == AF && inallow && ($0 ~ /^[^[:space:]]/ || $0 ~ /^[[:space:]]*$/ || $0 ~ DECL) { inallow = 0 }
      F == AF && $0 ~ ("^[[:space:]]*((public|private|protected|noncomputable)[[:space:]]+)*def[[:space:]]+" AD "([[:space:]]|$)") { inallow = 1 }
      F == AF && inallow { line = $0; for (k = 1; k <= na; k++) used[k] += strip(al[k]); $0 = line }
      /"/ { print F ":" FNR ": raw string literal outside ImageSymbols.lean: " $0 }
      END {
        if (F == AF) for (k = 1; k <= na; k++) if (!used[k])
          print F ": str_allow_lits entry " al[k] " is not in " AD " (stale exemption: delete it)"
      }
    ' "$f"
  done
  (( seen )) || echo "$str_allow_file: not scanned (stale str_allow_file / str_allow_def: update them)"
}

# Verify that sorted file lists `$1` (closure) and `$2` (`trusted=()`) are identical.
check_closure_trusted() {
  local missing extra rc=0
  missing=$(comm -23 "$1" "$2")
  if [[ -n "$missing" ]]; then
    echo "FAIL: specification files in theorem-statement closure missing from trusted=():"
    echo "$missing" | sed 's/^/  /'; rc=1
  fi
  extra=$(comm -13 "$1" "$2")
  if [[ -n "$extra" ]]; then
    echo "FAIL: files in trusted=() not in theorem-statement closure:"
    echo "$extra" | sed 's/^/  /'; rc=1
  fi
  return "$rc"
}

# Scratch-copy negative controls for `check_spec_theorems`, `scan_spec_strings`, and
# `check_closure_trusted` (the working tree is untouched).
self_test() {
  local root=$PWD scratch="$PWD/$out/self_test" bad=0 n=0 f t g
  rm -rf "$scratch"; mkdir -p "$scratch"
  for f in "${trusted[@]}" Symbolic/Specifications/**/*.lean; do
    mkdir -p "$scratch/$(dirname "$f")"; cp "$f" "$scratch/$f"
  done
  st_restore() { cp "$root/$1" "$scratch/$1"; }
  st_edit() { # <file> <awk program>: rewrite the scratch copy of <file>
    awk "$2" "$scratch/$1" > "$scratch/$1.tmp" && mv "$scratch/$1.tmp" "$scratch/$1"
  }
  st_theorems() {
    (cd "$scratch" && list_spec_theorems "${trusted[@]}" > "$scratch/st_thm.txt" &&
      check_spec_theorems "$scratch/st_thm.txt" > "$scratch/st_out.txt")
  }
  st_strings() {
    (cd "$scratch" && scan_spec_strings Symbolic/Specifications/**/*.lean > "$scratch/st_out.txt" &&
      [[ ! -s "$scratch/st_out.txt" ]])
  }
  st_closure() { # <closure list file>
    check_closure_trusted "$1" "$scratch/st_trusted.txt" > "$scratch/st_out.txt"
  }
  st_expect() { # <label> <pass|fail> <command...>
    local label=$1 want=$2 got; shift 2; n=$((n + 1))
    if "$@"; then got=pass; else got=fail; fi
    if [[ "$got" != "$want" ]]; then
      echo "FAIL: self-test control '$label': expected $want, got $got"
      sed 's/^/    /' "$scratch/st_out.txt" 2>/dev/null || true
      bad=1
    fi
  }
  printf '%s\n' "${trusted[@]}" | sort -u > "$scratch/st_trusted.txt"
  # Exemption 1: baseline passes; an extra theorem or missing kept theorem fails.
  st_expect "theorems: unmodified copy" pass st_theorems
  t=${kept_theorems[0]%%:*}
  st_edit "$t" '{ print } END { print ""; print "theorem selfTestPlanted : True := trivial" }'
  st_expect "theorems: planted 15th theorem" fail st_theorems
  st_restore "$t"
  g=${kept_theorems[-1]##*.}; g=${g##*:}; t=${kept_theorems[-1]%%:*}
  st_edit "$t" "/^theorem.*[ .]$g[ (]/ { sub(/^theorem/, \"def\") } { print }"
  cmp -s "$root/$t" "$scratch/$t" || st_expect "theorems: kept theorem gone" fail st_theorems
  cmp -s "$root/$t" "$scratch/$t" && { echo "FAIL: self-test could not demote $g"; bad=1; }
  st_restore "$t"
  # Exemption 2: baseline passes; an extra literal, out-of-scope allowed literal, or missing
  # allowed literal fails.
  st_expect "strings: unmodified copy" pass st_strings
  st_edit "$str_allow_file" "{ print } \$0 ~ /def $str_allow_def / { print \"  let _x := \\\"seventh\\\"\" }"
  st_expect "strings: 7th literal in $str_allow_def" fail st_strings
  st_restore "$str_allow_file"
  st_edit "$str_allow_file" '{ print } END { print ""; print "def selfTestName : String := \"identity-key\"" }'
  st_expect "strings: allowed literal outside $str_allow_def" fail st_strings
  st_restore "$str_allow_file"
  st_edit "$str_allow_file" '{ gsub(/"kyber-pre-key"/, "kyberName") } { print }'
  st_expect "strings: listed literal gone" fail st_strings
  st_restore "$str_allow_file"
  # Without the blank line after `parseBundleFiles`, the allowed region must still end at the
  # next column-0 or indented declaration.
  for t in "def" "  def"; do
    st_edit "$str_allow_file" "inb && /^[[:space:]]*\$/ && !done { print \"$t selfTestNext : String := \\\"identity-key\\\"\"; done = 1; next } /def $str_allow_def / { inb = 1 } { print }"
    if grep -q selfTestNext "$scratch/$str_allow_file"; then
      st_expect "strings: blank line deleted, literal in next '$t'" fail st_strings
    else
      echo "FAIL: self-test could not plant the deleted-blank-line control ('$t')"; bad=1
    fi
    st_restore "$str_allow_file"
  done
  # After the blank line, an indented non-declaration must also fall outside the allowed region.
  st_edit "$str_allow_file" "inb && /^[[:space:]]*\$/ && !done { print; print \"  local notation \\\"identity-key\\\" => selfTestG1\"; done = 1; next } /def $str_allow_def / { inb = 1 } { print }"
  if grep -q selfTestG1 "$scratch/$str_allow_file"; then
    st_expect "strings: blank line kept, literal in indented non-declaration" fail st_strings
  else
    echo "FAIL: self-test could not plant the blank-line-kept control"; bad=1
  fi
  st_restore "$str_allow_file"
  # Closure vs `trusted=()`: equal lists pass; an untrusted file (`RustHeap/Alloc.lean`) in the
  # closure or a missing trusted file fails.
  st_expect "closure: equal to trusted=()" pass st_closure "$scratch/st_trusted.txt"
  g=LibsignalBinary/Specifications/RustHeap/Alloc.lean
  if grep -qxF "$g" "$scratch/st_trusted.txt"; then
    echo "FAIL: self-test: $g is in trusted=() again (update the closure control)"; bad=1
  fi
  { cat "$scratch/st_trusted.txt"; echo "$g"; } | sort -u > "$scratch/st_closure_in.txt"
  st_expect "closure: untrusted $g enters it" fail st_closure "$scratch/st_closure_in.txt"
  awk 'NR > 1' "$scratch/st_trusted.txt" > "$scratch/st_closure_out.txt"
  st_expect "closure: a trusted file leaves it" fail st_closure "$scratch/st_closure_out.txt"
  if (( bad )); then echo "FAIL: exemption self-test ($n controls)"; return 1; fi
  echo "exemption self-test OK: $n controls (3 baselines pass, $((n - 3)) planted violations fail)"
}
if [[ "${1:-}" == "--self-test" ]]; then if self_test; then exit 0; else exit 1; fi; fi

# Expected `sorry` counts (`file:count`) and `sorryAx` allowlist regex (empty: zero `sorry`s).
intended_files=""
intended_names='$^'

fail=0
self_test || fail=1
for f in "${files[@]}"; do
  # Scan code lines only (strip comments).
  awk -v F="$f" '
    /^[[:space:]]*\/-/ { inc = 1 }
    inc { if ($0 ~ /-\//) inc = 0; next }
    { sub(/--.*/, "") }
    /(^|[^A-Za-z_.])sorry([^A-Za-z_]|$)/ { print F ":" FNR ": sorry" }
    /(^|[^A-Za-z_.])axiom[[:space:]]/ { print F ":" FNR ": axiom" }
    /native_decide/ { print F ":" FNR ": native_decide" }
    /(^|[^A-Za-z_.])admit([^A-Za-z_]|$)/ { print F ":" FNR ": admit" }
    /implemented_by|(^|[^A-Za-z_.])unsafe[[:space:]]/ { print F ":" FNR ": unsafe" }
  ' "$f"
done > "$out/hygiene.txt"

cat "$out/hygiene.txt"
n_other=$(awk '!/: sorry$/' "$out/hygiene.txt" | wc -l)
# Reject `sorry`s outside `intended_files` or mismatched per-file counts.
stray=$(awk -v L="$intended_files" 'BEGIN { n = split(L, a, " "); for (i = 1; i <= n; i++) { split(a[i], p, ":"); ok[p[1]] = 1 } }
  /: sorry$/ { split($0, q, ":"); if (!(q[1] in ok)) print q[1] ":" q[2] }' "$out/hygiene.txt")
if [[ -n "$stray" ]]; then echo "FAIL: unintended sorry at: $stray"; fail=1; fi
for fc in $intended_files; do
  f=${fc%%:*}; c=${fc##*:}
  n=$(awk -v F="$f" 'index($0, F ":") == 1 && /: sorry$/' "$out/hygiene.txt" | wc -l)
  if [[ "$n" -ne "$c" ]]; then echo "FAIL: expected $c sorry in $f, found $n"; fail=1; fi
done
if [[ "$n_other" -ne 0 ]]; then echo "FAIL: axiom, admit, native_decide, unsafe or implemented_by found"; fail=1; fi

cat > "$out/axioms.lean" <<'EOF'
import Symbolic.Theorems.ModelSecurity
import Symbolic.Theorems.RefinementPreservation
import Symbolic.Tests.ExternWitness
open DY.Libsignal.Refinement
#print axioms Proven.ForwardSecrecy.forward_secrecy
#print axioms Proven.PostCompromiseSecurity.post_compromise_security
#print axioms Proven.Handshake.alice_initiator_secrecy
#print axioms Proven.Handshake.bob_responder_secrecy
#print axioms Proven.Handshake.authentication
#print axioms Proven.Handshake.peer_authentication
#print axioms Proven.Handshake.handshake_forward_secrecy
#print axioms Proven.Handshake.kci_resistance
#print axioms Proven.Handshake.session_independence
#print axioms Proven.Handshake.hndl_resistance
#print axioms Proven.RefinementPreservation.comp_refinement_preservation_cli
#print axioms Proven.ExternWitness.comp_externsSatisfiable_cli
EOF
# `arm64-semantics` builds `Arm64.Trusted` and `Arm64.Testing` under separate `.lake` directories;
# symlink `Testing` into `Arm64/.lake` so standalone `lake env lean` resolves both under `Arm64`.
if [[ -d arm64-semantics/Arm64/Testing/.lake/build/lib/lean/Arm64/Testing &&
      -d arm64-semantics/Arm64/.lake/build/lib/lean/Arm64 &&
      ! -e arm64-semantics/Arm64/.lake/build/lib/lean/Arm64/Testing ]]; then
  ln -sfn ../../../../../Testing/.lake/build/lib/lean/Arm64/Testing \
    arm64-semantics/Arm64/.lake/build/lib/lean/Arm64/Testing
fi
LAKE_TRUST_CACHED_RUST_EXPORTS="${LAKE_TRUST_CACHED_RUST_EXPORTS:-true}" \
  lake env lean "$out/axioms.lean" > "$out/axioms.out" 2>&1 || true
# Print one summary line per theorem (`uses sorryAx` vs `no sorryAx`).
awk '/depends on axioms/ { name = $1; s = ($0 ~ /sorryAx/) ? "uses sorryAx" : "no sorryAx" }
     /depends on axioms/ && /\]/ { print name ": " s; name = "" ; next }
     name != "" && /sorryAx/ { s = "uses sorryAx" }
     name != "" && /\]/ { print name ": " s; name = "" }' "$out/axioms.out"

# Fail if any result outside `intended_names` uses `sorryAx`, or if a result is missing.
n_expected=$(awk '/^#print axioms/' "$out/axioms.lean" | wc -l)
n_printed=$(awk '/depends on axioms|does not depend on any axioms/' "$out/axioms.out" | wc -l)
if [[ "$n_printed" -ne "$n_expected" ]]; then
  echo "FAIL: $n_printed of $n_expected axiom reports (see $out/axioms.out)"; fail=1
fi
bad=$(awk -v OK="$intended_names" '/depends on axioms/ { name = $1; gsub(/'"'"'/, "", name); s = ($0 ~ /sorryAx/) }
     /depends on axioms/ && /\]/ { if (s && name !~ OK) print name; name = ""; next }
     name != "" && /sorryAx/ { s = 1 }
     name != "" && /\]/ { if (s && name !~ OK) print name; name = "" }' "$out/axioms.out")
if [[ -n "$bad" ]]; then echo "FAIL: sorryAx in: $bad"; fail=1; fi

# Check via `scripts/TrustedClosure.lean --symbolic` that `trusted=()` matches the repository
# theorem-statement closure, excludes proof and non-allowlisted `CryptoGames` modules, has a
# clean import closure, and is a subset of `files=()`.
statement_args=()
for f in "${trusted[@]}"; do
  statement_args+=(--statement-file "$f")
done
default_symbolic_headlines=(
  --headline compFs:Proven.ForwardSecrecy.forward_secrecy:Symbolic.Theorems.ModelSecurity
  --headline compPcs:Proven.PostCompromiseSecurity.post_compromise_security:Symbolic.Theorems.ModelSecurity
  --headline compAliceInitiatorSecrecy:Proven.Handshake.alice_initiator_secrecy:Symbolic.Theorems.ModelSecurity
  --headline compBobResponderSecrecy:Proven.Handshake.bob_responder_secrecy:Symbolic.Theorems.ModelSecurity
  --headline compAuthentication:Proven.Handshake.authentication:Symbolic.Theorems.ModelSecurity
  --headline compPeerAuthentication:Proven.Handshake.peer_authentication:Symbolic.Theorems.ModelSecurity
  --headline compHandshakeFs:Proven.Handshake.handshake_forward_secrecy:Symbolic.Theorems.ModelSecurity
  --headline compKci:Proven.Handshake.kci_resistance:Symbolic.Theorems.ModelSecurity
  --headline compSessionIndependence:Proven.Handshake.session_independence:Symbolic.Theorems.ModelSecurity
  --headline compHndl:Proven.Handshake.hndl_resistance:Symbolic.Theorems.ModelSecurity
  --headline compRefinementPreservationCli:Proven.RefinementPreservation.comp_refinement_preservation_cli:Symbolic.Theorems.RefinementPreservation
  --headline compExternsSatisfiableCli:Proven.ExternWitness.comp_externsSatisfiable_cli:Symbolic.Tests.ExternWitness
)
if ! LAKE_TRUST_CACHED_RUST_EXPORTS="${LAKE_TRUST_CACHED_RUST_EXPORTS:-true}" \
     lake env lean --run scripts/TrustedClosure.lean --symbolic \
     "${default_symbolic_headlines[@]}" \
     "${statement_args[@]}" \
     --out-dir "$out/trusted_closure" > "$out/trusted_closure.out" 2>&1; then
  cat "$out/trusted_closure.out"
  echo "FAIL: scripts/TrustedClosure.lean --symbolic failed"; fail=1
else
  awk -F, 'NR > 1 && $2 == "crypto-verification" && $1 != "generated" { print $3 }' \
    "$out/trusted_closure/trusted_closure_files.csv" | sort -u > "$out/closure_files.txt"
  printf '%s\n' "${trusted[@]}" | sort -u > "$out/trusted_files.txt"
  printf '%s\n' "${files[@]}" | sort -u > "$out/scanned_files.txt"
  if [[ ! -s "$out/closure_files.txt" ]]; then
    echo "FAIL: scripts/TrustedClosure.lean produced no repository entries in trusted_closure_files.csv"; fail=1
  fi
  repo_tier=$(awk -F, 'NR > 1 && $2 == "crypto-verification" && $1 != "T" && $1 != "generated" { print $3 " (" $1 ", headline " $13 ")" }' \
    "$out/trusted_closure/trusted_closure_files.csv" | sort -u)
  if [[ -n "$repo_tier" ]]; then
    echo "FAIL: repository files outside trusted=() in theorem-statement closure:"
    echo "$repo_tier" | sed 's/^/  /'; fail=1
  fi
  # Allow `cli_cryptogames` only on `compExternsSatisfiableCli` rows (reached via `ElfBinding.lean`,
  # which `check_symbolic_deps.py` checks under `HEADLINE_ROOTS` rather than `STATEMENT_ROOTS`; see
  # `docs/Symbolic/PAPER_DIFFERENCES.md` §5.3 and `Computational/docs/DEVIATIONS.md`).
  forbidden_closure=$(awk -F, -v ALLOW="${cli_cryptogames[*]}" '
    BEGIN { n = split(ALLOW, a, " "); for (i = 1; i <= n; i++) ok[a[i]] = 1 }
    NR > 1 && ($3 ~ /^(Computational\/(Proofs|Specifications\/CryptoGames|Tests)|LibsignalBinary\/Proofs|Symbolic\/Proofs|LibsignalBinary\/Specifications\/CryptoGames)\//) &&
      !(($3 in ok) && $13 == "compExternsSatisfiableCli") { print $3 " (" $13 ")" }' \
    "$out/trusted_closure/trusted_closure_files.csv" | sort -u)
  if [[ -n "$forbidden_closure" ]]; then
    echo "FAIL: forbidden proof/CryptoGames files in theorem-statement closure:"
    echo "$forbidden_closure" | sed 's/^/  /'; fail=1
  fi
  # Statement files outside `cli_wit` may transitively import only `trusted=()` repo modules;
  # `cli_wit` may also reach `LibsignalBinary/Specifications/`. Cross-check the extra module count
  # against the `repo` row in `trusted_closure.md`.
  import_closure_repo() { # <file>... -> the repository files they import, transitively
    local -A seen=() ; local queue=("$@") f m g
    while ((${#queue[@]})); do
      f=${queue[-1]}; unset 'queue[-1]'
      [[ -n ${seen[$f]:-} ]] && continue; seen[$f]=1
      for m in $(awk '/^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]/ {
               for (i = 1; i <= NF; i++) if ($i != "public" && $i != "meta" && $i != "import" && $i != "all") { print $i; break } }' "$f"); do
        g=${m//.//}.lean
        [[ -f $g && -z ${seen[$g]:-} ]] && queue+=("$g")
      done
    done
    printf '%s\n' "${!seen[@]}" | sort -u
  }
  import_closure_repo "${trusted[@]}" | comm -23 - "$out/trusted_files.txt" > "$out/stmt_import_extra.txt"
  strict=($(printf '%s\n' "${trusted[@]}" | sort -u | comm -23 - <(printf '%s\n' "${cli_wit[@]}" | sort -u)))
  strict_extra=$(import_closure_repo "${strict[@]}" | comm -23 - "$out/trusted_files.txt")
  if [[ -n "$strict_extra" ]]; then
    echo "FAIL: statement files outside cli_wit transitively import non-statement repo modules:"
    echo "$strict_extra" | sed 's/^/  /'; fail=1
  fi
  wit_extra=$(grep -v '^LibsignalBinary/Specifications/' "$out/stmt_import_extra.txt" || true)
  if [[ -n "$wit_extra" ]]; then
    echo "FAIL: cli_wit statement files transitively import repo modules outside LibsignalBinary/Specifications/:"
    echo "$wit_extra" | sed 's/^/  /'; fail=1
  fi
  n_walk=$(wc -l < "$out/stmt_import_extra.txt")
  if ! grep -qE "^\| \`repo\` \| ${n_walk} \| [0-9,]+ \|\$" "$out/trusted_closure/trusted_closure.md"; then
    echo "FAIL: the import walk found $n_walk non-statement repo modules, the report's module-level repo row does not (see $out/trusted_closure/trusted_closure.md)"
    fail=1
  fi
  check_closure_trusted "$out/closure_files.txt" "$out/trusted_files.txt" || fail=1
  missing_scanned=$(comm -23 "$out/trusted_files.txt" "$out/scanned_files.txt")
  if [[ -n "$missing_scanned" ]]; then
    echo "FAIL: files in trusted=() missing from files=() hygiene scan:"
    echo "$missing_scanned" | sed 's/^/  /'; fail=1
  fi
  echo "trusted closure verified: $(wc -l < "$out/closure_files.txt") statement files (T), 0 other repo files (report: $out/trusted_closure/trusted_closure.md)"
fi
# Check that `trusted=()` contains no theorems outside `kept_theorems`.
echo "theorems / lemmas / examples left in the ${#trusted[@]} trusted specification files:"
list_spec_theorems "${trusted[@]}" > "$out/spec_theorems.txt"
if [[ -s "$out/spec_theorems.txt" ]]; then sed 's/^/  /' "$out/spec_theorems.txt"; else echo "  (none)"; fi
check_spec_theorems "$out/spec_theorems.txt" || fail=1
# Informational list of proof-carrying instances and `decreasing_by` blocks required to
# elaborate definitions in `trusted=()` (e.g. `ParseConsumes`, `ALaCarte.Representable`, and
# termination obligations in `WireFormat.lean`).
echo "proof-carrying instances and termination proofs kept in the trusted files:"
grep -nE '^[[:space:]]*(public[[:space:]]+)?instance\b.*:= by|decreasing_by' "${trusted[@]}" | sed 's/^/  /' || true

# Symbol-literal hygiene: binary symbol string literals in `Symbolic/Specifications/` must live
# in `Concrete/ImageSymbols.lean`. `scan_spec_strings` exempts only protocol HKDF info strings,
# `"spec::x25519_add_eight_torsion"` (`Concrete/ExternInterpretation.lean`), the party UUIDs in
# `Refinement/CliSetup.lean`, and `str_allow_*` in `WireFormat.parseBundleFiles`.
spec_files=(Symbolic/Specifications/**/*.lean)
scan_spec_strings "${spec_files[@]}" > "$out/spec_strings.txt"
if [[ -s "$out/spec_strings.txt" ]]; then
  echo "FAIL: raw string literals in Symbolic/Specifications/ outside ImageSymbols.lean:"
  cat "$out/spec_strings.txt"
  fail=1
fi

[[ "$fail" -eq 0 ]] && echo "hygiene OK"
exit "$fail"
