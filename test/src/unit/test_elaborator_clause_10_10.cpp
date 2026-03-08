// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §10.10: Empty unpacked array concatenation elaborates without errors.
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

// §10.10: Unpacked array concatenation with descending-range target.
TEST(SimCh10j, UnpackedArrayConcatDescending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [2:0];\n"
      "  initial begin\n"
      "    arr = {10, 20, 30};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e2->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
  EXPECT_EQ(e0->value.ToUint64(), 30u);
}

// §10.10: Mixed scalars and arrays in unpacked array concatenation.
TEST(ElabCh10j, MixedScalarArrayElaborates) {
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
