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

// §10.10: Basic unpacked array concatenation elaborates.
TEST(ElabCh10j, UnpackedArrayConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Array items in unpacked array concatenation elaborate.
TEST(ElabCh10j, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
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

// §10.10: Queue target with unpacked array concatenation.
TEST(ElabCh10j, QueueConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10.2: Concatenation braces disambiguate based on target type.
TEST(ElabCh10j, ConcatBracesDisambiguateByTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte B;\n"
      "  byte BA[2];\n"
      "  initial begin\n"
      "    B = {4'h6, 4'hf};\n"
      "    BA = {4'h6, 4'hf};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Unpacked array concatenation from scalar elements.
TEST(SimCh10j, UnpackedArrayConcatScalarElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = {1, 2, 3};\n"
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
  EXPECT_EQ(e0->value.ToUint64(), 1u);
  EXPECT_EQ(e1->value.ToUint64(), 2u);
  EXPECT_EQ(e2->value.ToUint64(), 3u);
}

// §10.10: Array item expansion in unpacked array concatenation.
TEST(SimCh10j, UnpackedArrayConcatArrayExpansion) {
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
