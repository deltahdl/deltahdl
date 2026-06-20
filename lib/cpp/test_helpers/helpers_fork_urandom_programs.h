#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_seeded_run.h"

using namespace delta;

// Run a fork program whose parent calls process::self().srandom(parent_seed)
// before forking two children that each draw one $urandom value. Returns the
// two children's draws as {a, b}. The §18.14 random-stability tests reuse this
// exact program to show that reseeding the parent shifts the seed material the
// children inherit.
inline std::vector<uint64_t> RunParentSeededTwoForkUrandom(
    uint32_t parent_seed) {
  std::string src =
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    p.srandom(" +
      std::to_string(parent_seed) +
      ");\n"
      "    fork\n"
      "      a = $urandom;\n"
      "      b = $urandom;\n"
      "    join\n"
      "  end\n"
      "endmodule\n";
  return RunSeededAndRead(src, {"a", "b"});
}

// Run a fork that spawns four sibling children, each drawing one $urandom
// value. Returns the four draws as {a, b, c, d}. The §18.14 tests reuse this
// program to assert that many forked siblings receive pairwise-distinct
// streams.
inline std::vector<uint64_t> RunFourForkedSiblingUrandom() {
  return RunSeededAndRead(
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  int unsigned c;\n"
      "  int unsigned d;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = $urandom;\n"
      "      b = $urandom;\n"
      "      c = $urandom;\n"
      "      d = $urandom;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      {"a", "b", "c", "d"});
}
