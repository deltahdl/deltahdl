

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ElabCh10j, EmptyUnpackedArrayConcatElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaborates, UnpackedArrayConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatArrayExpansion, UnpackedArrayConcatArrayExpansion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{10, 20};\n"
      "  int B [0:1] = '{30, 40};\n"
      "  int C [0:3];\n"
      "  initial begin\n"
      "    C = {A, B};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c0 = f.ctx.FindVariable("C[0]");
  auto* c1 = f.ctx.FindVariable("C[1]");
  auto* c2 = f.ctx.FindVariable("C[2]");
  auto* c3 = f.ctx.FindVariable("C[3]");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  ASSERT_NE(c3, nullptr);
  EXPECT_EQ(c0->value.ToUint64(), 10u);
  EXPECT_EQ(c1->value.ToUint64(), 20u);
  EXPECT_EQ(c2->value.ToUint64(), 30u);
  EXPECT_EQ(c3->value.ToUint64(), 40u);
}

}  // namespace
