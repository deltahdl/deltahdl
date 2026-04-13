

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void RunAndExpectArray(
    SimFixture& f, RtlirDesign* design, const std::string& name,
    std::initializer_list<std::pair<int, uint64_t>> expected) {
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (const auto& [idx, val] : expected) {
    auto key = name + "[" + std::to_string(idx) + "]";
    auto* var = f.ctx.FindVariable(key);
    ASSERT_NE(var, nullptr) << key;
    EXPECT_EQ(var->value.ToUint64(), val) << key;
  }
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInPositionalPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{A3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInReplicatedPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{3{A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ReplicationTargetingUnpackedArrayError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatScalarElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{0, 1}, {1, 2}, {2, 3}});
}

TEST(ArrayItemExpansionElaborates, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatDescending, UnpackedArrayConcatDescending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [2:0];\n"
      "  initial begin\n"
      "    arr = {10, 20, 30};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{2, 10}, {1, 20}, {0, 30}});
}

}  // namespace
