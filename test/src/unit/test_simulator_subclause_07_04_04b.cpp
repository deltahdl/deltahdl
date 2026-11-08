#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(MultidimensionalArraySimulation, PackageArrayOfStagedTypedefIsTwoDim) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [1:5] bsix;\n"
      "  typedef bsix mem_type [0:3];\n"
      "  mem_type ba [0:7];\n"
      "  bsix plain [0:1];\n"
      "  function automatic int f();\n"
      "    ba[0][0] = 5'd7;\n"
      "    ba[0][3] = 5'd1;\n"
      "    return ba[0][0] + ba[0][3];\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = p::f();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 8u);
}

TEST(MultidimensionalArraySimulation, PortArrayOfStagedTypedefIsTwoDim) {
  auto v = RunAndGet(
      "typedef bit [1:5] bsix;\n"
      "typedef bsix mem_type [0:3];\n"
      "typedef bit [7:0] byte_t;\n"
      "module t(output mem_type ba [0:1], output byte_t o [0:1]);\n"
      "  int result;\n"
      "  initial begin\n"
      "    ba[1][2] = 5'd4;\n"
      "    result = ba[1][2] + ba[1][0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

}  // namespace
