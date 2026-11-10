// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// Static AArch64 C program compiled with `zig cc` (-O0 and -O2) and `aarch64-linux-gnu-gcc`
// (when available) for differential testing of the Lean ELF64 loader against `qemu-aarch64`.

#include <stddef.h>
#include <stdint.h>

const uint64_t ro_table[8] = {
    0x1020304050607080ULL, 0x90a0b0c0d0e0f001ULL,
    0x0123456789abcdefULL, 0xfedcba9876543210ULL,
    0x0011223344556677ULL, 0x8899aabbccddeeffULL,
    0xdeadbeefcafebabeULL, 0x1337c0de42424242ULL,
};

uint64_t rw_data[4] = {
    0xaaaaaaaaaaaaaaaaULL,
    0x5555555555555555ULL,
    0x123456789abcdef0ULL,
    0x0fedcba987654321ULL,
};

uint8_t large_bss[8192];

int main(int argc, char **argv, char **envp) {
    uint64_t acc = ro_table[argc & 7] ^ rw_data[0];
    large_bss[0] = (uint8_t)argc;
    large_bss[4095] = (uint8_t)(acc & 0xff);
    large_bss[8191] = (argv && argv[0]) ? (uint8_t)argv[0][0] : 0;
    if (envp && envp[0]) {
        rw_data[1] ^= (uint64_t)(uint8_t)envp[0][0];
    }
    return (int)((acc ^ large_bss[0] ^ large_bss[8191]) & 0);
}
