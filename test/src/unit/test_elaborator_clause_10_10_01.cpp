

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

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

TEST(UnpackedArrayConcatSim, ConcatAndPatternEquivalent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [1:3];\n"
      "  int B [1:3];\n"
      "  initial begin\n"
      "    A = {1, 2, 3};\n"
      "    B = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 1; i <= 3; ++i) {
    auto a_name = "A[" + std::to_string(i) + "]";
    auto b_name = "B[" + std::to_string(i) + "]";
    auto* a = f.ctx.FindVariable(a_name);
    auto* b = f.ctx.FindVariable(b_name);
    ASSERT_NE(a, nullptr) << a_name;
    ASSERT_NE(b, nullptr) << b_name;
    EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64()) << "index " << i;
  }
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

TEST(UnpackedArrayConcatMixed, UnpackedArrayConcatMixed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{1, 2};\n"
      "  int B [0:2];\n"
      "  initial begin\n"
      "    B = {A, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b0 = f.ctx.FindVariable("B[0]");
  auto* b1 = f.ctx.FindVariable("B[1]");
  auto* b2 = f.ctx.FindVariable("B[2]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b0->value.ToUint64(), 1u);
  EXPECT_EQ(b1->value.ToUint64(), 2u);
  EXPECT_EQ(b2->value.ToUint64(), 3u);
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

TEST(MixedScalarArrayConcatenation, MixedScalarArrayElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[3];\n"
      "  initial B = {A, 5};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
