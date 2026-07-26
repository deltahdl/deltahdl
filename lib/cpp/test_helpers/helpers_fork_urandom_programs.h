#pragma once

#include <gtest/gtest.h>

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

// Run a fork whose two children each draw one $urandom_range value, twice over
// from the same starting state, and check the two runs agree draw for draw.
//
// A value a thread draws is fixed by the stream that thread was seeded with
// rather than by the order the scheduler happened to run the siblings in, so
// replaying the same program from the same state reproduces both draws. A
// scheduler-order dependence would let the two runs disagree.
inline void ExpectForkedUrandomRangeDrawsReplay() {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      a = $urandom_range(1000000);\n"
        "      b = $urandom_range(1000000);\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}
