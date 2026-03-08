// §10.10.1

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §10.10.1: Unpacked array concat vs assignment pattern produce the same result.
TEST(SimCh10j, ConcatAndPatternEquivalent) {
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
