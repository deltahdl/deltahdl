#include <gtest/gtest.h>

#include <cstdint>
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

TEST(DynamicArrayNewValidation,
     NewOnAnAssociativeArrayOrPastADynamicDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa [int]; int sa [string]; int arr [2][][];\n"
      "  int arr3 [1][2][] = new [4];\n"
      "  initial begin\n"
      "    aa = new[2];\n"
      "    sa = new[2];\n"
      "    arr[0] = new[4];\n"
      "    arr[0][1][1] = new[2];\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "'arr3', which is neither a dynamic array",
                            3, "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'aa', which is neither a dynamic array", 5,
                            "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'sa', which is neither a dynamic array", 6,
                            "7.5.1"));
  EXPECT_TRUE(ReportedError(diags, "'arr', which is neither a dynamic array", 8,
                            "7.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(DynamicArrayNewValidation, DimensionWithoutAnIndexOnTheLeftIsReported) {
  ElabFixture f;
  bool parse_failed = false;
  ElaborateSrcReportingParse(
      "module t;\n"
      "  int arr [2][][];\n"
      "  initial arr[0][] = new[2];\n"
      "endmodule\n",
      f, "", parse_failed);
  EXPECT_TRUE(parse_failed);
  ASSERT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.Diagnostics().front().loc.line, 3u);
}

TEST(DynamicArrayNewValidation,
     DISABLED_InitializerNotAssignmentCompatibleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int d []; string s [3]; logic [31:0] l [3]; int aa [int]; "
      "int m [2][2];\n"
      "  int e [] = new[3](s);\n"
      "  initial begin\n"
      "    d = new[3](5);\n"
      "    d = new[3](s);\n"
      "    d = new[3](l);\n"
      "    d = new[3](aa);\n"
      "    d = new[2](m);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {3u, 5u, 6u, 7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(diags, "assignment compatible", line, "7.5.1"))
        << line;
  }
}

TEST(DynamicArrayNewValidation,
     InitializerOfAnEquivalentElementTypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  bit signed [31:0] b [3]; int q [$]; int d [];\n"
      "  int e [] = new[3](b);\n"
      "  initial begin d = new[3](b); d = new[2](q); d = new[4](e); end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
