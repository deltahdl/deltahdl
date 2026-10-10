#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewValidation, NewSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  initial d = new[10];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, NewSizeWithInitElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int src[] = '{1, 2, 3};\n"
             "  initial d = new[5](src);\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, NewZeroSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  initial d = new[0];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, DeclWithNewElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = new[4];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, SelfReferenceResizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = '{1, 2, 3};\n"
             "  initial d = new[6](d);\n"
             "endmodule\n"));
}

// §7.5.1 with A.6.2: `new [n]` is no expression. It stands only as the whole
// right-hand side of a blocking assignment or a declaration assignment, never
// in a nonblocking or continuous one or as an operand, and only where the
// left-hand side is a dynamic array: a fixed dimension or a keyword type is
// nothing it constructs. An element of an array whose next dimension is
// dynamic, a subroutine's dynamic array argument and a structure member it
// cannot see the type of are left alone.
TEST(DynamicArrayNewValidation, NewStandsOnlyWhereItConstructsADynamicArray) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int d[];\n"
      "  int f[3];\n"
      "  int x;\n"
      "  wire w;\n"
      "  int arr3 [1][2][] = new [4];\n"
      "  int arr [2][];\n"
      "  struct { int m[]; } s;\n"
      "  assign w = new [2];\n"
      "  initial begin\n"
      "    d <= new [2];\n"
      "    f = new [3];\n"
      "    x = new [2];\n"
      "    d = new [2] + 1;\n"
      "    d = new [2];\n"
      "    arr[0] = new [4];\n"
      "    s.m = new [2];\n"
      "  end\n"
      "  task t(input int a[]); int b[3] = new [3]; a = new [1]; endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMisplaced = "'new' stands only as the whole right-hand";
  EXPECT_TRUE(ReportedError(diags, "'new' is assigned to 'arr3'", 6, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, kMisplaced, 9, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, kMisplaced, 11, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'new' is assigned to 'f'", 12, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'new' is assigned to 'x'", 13, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, kMisplaced, 14, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'new' is assigned to 'b'", 19, "7.5.1"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 15u) << d.message;
    EXPECT_NE(d.loc.line, 16u) << d.message;
    EXPECT_NE(d.loc.line, 17u) << d.message;
    EXPECT_EQ(d.message.find("'new' is assigned to 'a'"), std::string::npos);
  }
}

}  // namespace
