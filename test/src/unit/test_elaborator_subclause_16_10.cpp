#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LocalVariableElaboration, FormalArgumentRedeclaredInSequenceBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence sub_seq3(lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a ##1 lv);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, FormalArgumentRedeclaredInPropertyBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(lv);\n"
      "    bit lv;\n"
      "    @(posedge clk) lv |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, LocalFormalArgumentRedeclaredInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(local input int lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a, b) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, FreshBodyLocalAlongsideFormalElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(lv);\n"
      "    int guard;\n"
      "    @(posedge clk) (a, guard = b) ##1 lv;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalVariableElaboration, InstantiatedSequencesLocalIsNotVisible) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, c, do1;\n"
      "  int data_in, data_out;\n"
      "  sequence sub_seq1;\n"
      "    int v1;\n"
      "    (a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);\n"
      "  endsequence\n"
      "  sequence seq1;\n"
      "    c ##1 sub_seq1 ##1 (do1 == v1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v1' is a local variable of sequence 'sub_seq1' "
                            "and is not visible outside its body",
                            10, "16.10"));
}

TEST(LocalVariableElaboration, LocalOfASequenceNotInstantiatedIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk, a);\n"
      "  sequence s1; int v; (a, v = 1) ##1 (v == 1); endsequence\n"
      "  sequence s2(x); x; endsequence\n"
      "  assert property (@(posedge clk) s2(a) ##1 v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'v'", 4,
                            "23.9"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "is a local variable", 4, "16.10"));
}

TEST(LocalVariableFlow, AReferenceToAnUnassignedLocalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  property p1;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x++) |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    int y;\n"
      "    @(posedge clk) ((a, y = 1) or b) ##1 (c == y);\n"
      "  endproperty\n"
      "  sequence s3;\n"
      "    int u, v = u + 1;\n"
      "    a;\n"
      "  endsequence\n"
      "  sequence s4;\n"
      "    int w;\n"
      "    (a, w = 1) ##1 (c == w);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  auto reported = [&](const char* name, int line) {
    return ReportedError(f.diag.Diagnostics(),
                         std::string("the local variable '") + name +
                             "' is referenced at a point where it is "
                             "unassigned",
                         line, "16.10");
  };
  EXPECT_TRUE(reported("x", 5));
  EXPECT_TRUE(reported("y", 9));
  EXPECT_TRUE(reported("u", 12));
  EXPECT_FALSE(reported("w", 17));
}

TEST(LocalVariableFlow, ALocalInsideAnActualOfTriggeredIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, c;\n"
      "  int data_in;\n"
      "  sequence sub(lv);\n"
      "    (a, lv = data_in) ##1 (lv > 0);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1 + 1).triggered;\n"
      "  endsequence\n"
      "  sequence top2;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1).triggered;\n"
      "  endsequence\n"
      "  sequence top3;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1 + 1).matched;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable passed to an instance that triggered is applied to "
      "shall be an entire actual argument";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a local variable passed to an instance that "
                            "matched is applied to shall be an entire actual "
                            "argument",
                            17, "16.13.5"));
}

TEST(LocalVariableFlow, TriggeredOnASequenceReadingTheFormalFirstIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, c;\n"
      "  int data_in;\n"
      "  sequence sub(lv);\n"
      "    (a && lv > 0) ##1 (1, lv = data_in);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v1;\n"
      "    (c, v1 = 1) ##1 sub(v1).triggered;\n"
      "  endsequence\n"
      "  sequence top2;\n"
      "    int v1;\n"
      "    (c, v1 = 1) ##1 sub(v1).matched;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'sub' references its formal 'lv', bound to the "
                            "local variable 'v1', before it assigns it",
                            9, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'sub' references its formal 'lv', bound to the "
                            "local variable 'v1', before it assigns it",
                            13, "16.13.5"));
}

TEST(LocalVariableFlow, AnAssignmentOnAnEmptyMatchingSequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  int e;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 (b[*0:1], x = e) ##1 c[*2];\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int x;\n"
      "    @(posedge clk) (a ##1 b[*0:1], x = e) ##1 c[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable assignment may not be attached to a sequence that "
      "admits an empty match";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.10"));
}

TEST(LocalVariableFlow,
     AThroughoutConditionReadingAnUnassignedLocalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (x > 0) throughout (a ##1 (b, x = 1));\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int y;\n"
      "    @(posedge clk) (a, y = 1) ##1 ((y > 0) throughout (a ##1 b));\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the local variable 'x' is referenced at a point "
                            "where it is unassigned",
                            5, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the local variable 'y'", 9,
                             "16.10"));
}

TEST(LocalVariableFlow, AnAssignmentOnAnEmptyMatchInsideAnOrGroupIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  int e;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 ((b[*0:1], x = e) or c) ##1 c[*2];\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 ((a ##1 b[*0:1], x = e) or c) ##1 c[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable assignment may not be attached to a sequence that "
      "admits an empty match";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.10"));
}

}  // namespace
