#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_seeded_run.h"

using namespace delta;

inline std::vector<uint64_t> RunParentSeededTwoForkUrandom(
    uint32_t parent_seed) {
  std::string src =
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
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
