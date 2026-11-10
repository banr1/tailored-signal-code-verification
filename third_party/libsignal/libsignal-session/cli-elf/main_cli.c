// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

/* Weak placeholder: snapshot-link's musl-discovery probe links main.o alone and needs `main`.
 * With `--native-objects` / `--musl-string`, musl's verified `memcpy`/`memset`/`memmove`/
 * `memcmp`/`bcmp` `.o` files are placed directly after `main.o` and before archives, so `ld.lld`
 * resolves musl's `__init_tls` to musl's own `memcpy` without pulling `libcompiler_rt.a`'s
 * monolithic `mem*` archive member. In the real link the image's strong global `main` (the
 * CLI's `#[no_mangle] extern "C" fn main`) overrides this weak stub. */
__attribute__((weak)) int main(void) {
    return 0;
}
