#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ArrayLiteralElaboration, SimpleArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[1:0] = '{10, 20};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, NestedBracesOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ms_t;\n"
             "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, DefaultKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] arr [0:3];\n"
             "  initial arr = '{default: 8'd0};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, SizeMismatchError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayLiteralElaboration, FlatInitIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayLiteralElaboration, DuplicateIndexError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[0:2] = '{0: 1, 1: 2, 0: 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayLiteralElaboration, ReplicationOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{3{0}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, IndexKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{0: 10, 1: 20, 2: 30};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TooFewElementsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[0:2] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayLiteralElaboration, PositionalArrayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayLiteralElaboration, NarrowToWideElementOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:1] = '{1'b1, 1'b1};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TypeKeyArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{int: 42};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, KeyedPatternUncoveredElementError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[0:2] = '{0: 10, 2: 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
