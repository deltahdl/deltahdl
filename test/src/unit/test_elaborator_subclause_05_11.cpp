#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayLiteralElaboration, MatchingElementCountElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:3];\n"
             "  initial n = '{0, 1, 2};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, FlatLiteralForMultiDimRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:3] = '{0, 1, 2, 3, 4, 5};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 6 elements, but array dimension requires 2", 2,
      "10.9.1"));
}

TEST(ArrayLiteralElaboration, ReplicationReachingAcrossDimensionsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:3] = '{6{4}};\n"
      "  int m [1:2][1:3] = '{2{1, 2, 3}};\n"
      "  int k [1:2][1:3] = '{2{'{3{4}}}};\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 3u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "assignment pattern has 6 elements, but array dimension requires 2",
        line, "10.9.1"))
        << line;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "assignment pattern has", 4,
                             "10.9.1"));
}

TEST(ArrayLiteralElaboration, WrongElementCountRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:3] = '{0, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 2,
      "10.9.1"));
}

TEST(ArrayLiteralElaboration, ReplicationFillsDimension) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:3];\n"
             "  initial n = '{3{4}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TypePrefixedArrayLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = triple'{0, 1, 2};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, AssignmentContextProvidesType) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = '{0, 1, 2};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, IndexKeyWithDefaultElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = '{1:1, default:0};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, ReplicationSupplyingTooFewElementsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:3] = '{2{4}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 2,
      "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ReplicationOfSeveralItemsFillingDimensionAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:2][1:6] = '{2{'{3{4, 5}}}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, ReplicationByParameterFillingDimensionAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  parameter int N = 3;\n"
             "  int n [1:3] = '{N{4}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, WrongElementCountInProceduralAssignmentRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a [0:2];\n"
      "  initial a = '{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 3,
      "10.9.1"));
}

TEST(ArrayLiteralElaboration, WrongElementCountForTypedefArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int i3_t [0:2];\n"
      "  i3_t ints = '{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 3,
      "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     UntypedPatternOutsideAssignmentLikeContextRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    $display(\"%p\", '{1, 2});\n"
      "    x = '{1, 2} + 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "assignment pattern without a type prefix outside an assignment-like "
      "context";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "10.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "10.9"));
}

TEST(ArrayLiteralElaboration,
     UntypedPatternInEachAssignmentLikeContextAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef int pair_t [0:1];\n"
             "module t;\n"
             "  parameter pair_t P = '{1, 2};\n"
             "  pair_t w, v, u;\n"
             "  pair_t nested [0:1];\n"
             "  bit c;\n"
             "  assign w = '{3, 4};\n"
             "  function automatic pair_t f(pair_t a);\n"
             "    return '{a[1], a[0]};\n"
             "  endfunction\n"
             "  initial begin\n"
             "    v = '{7, 8};\n"
             "    u = f('{9, 10});\n"
             "    v = ('{1, 1});\n"
             "    v = c ? '{2, 2} : '{3, 3};\n"
             "    nested = '{'{4, 4}, '{5, 5}};\n"
             "    v = pair_t'('{6, 6});\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
