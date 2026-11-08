#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IfMatchesElaboration, IfMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration, IfMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    if (x matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration, RealValueWithIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    if (r matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            6, "12.6.2"));
}

TEST(IfMatchesElaboration,
     RealValueWithIntegralPatternInGuardedClauseRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    if (r matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            8, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueMatchesInTrailingClauseRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    if (en &&& r matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            8, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) if (r matches 8'd5) y = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            5, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else if (r matches 8'd5) y = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            5, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInARandcaseItemIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial randcase 1: if (r matches 8'd5) y = 8'd1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            4, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { if (r matches 8'd5) y = 8'd1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            6, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { if (r matches 8'd5) y = 8'd1; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            7, "12.6.2"));
}

TEST(IfMatchesElaboration, PatternIdentifierReadInTheElseArmIsUnresolved) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int y;\n"
      "  initial begin\n"
      "    if (v matches tagged Valid .n &&& n > 0) y = n;\n"
      "    else y = n;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'n'", 6,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(IfMatchesElaboration, AssignmentToPatternIdentifierInTrueArm) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { bit [3:0] Bt; int I; } U;\n"
      "  U u = tagged Bt 4'd3;\n"
      "  initial if (u matches tagged Bt .b) begin\n"
      "    b = 4'd5;\n"
      "    $display(\"%0d\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration,
     AssignmentToPatternIdentifierInFalseArmIsUndeclared) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { bit [3:0] Bt; int I; } U;\n"
      "  U u = tagged Bt 4'd3;\n"
      "  initial if (u matches tagged Bt .b) $display(\"%0d\", b);\n"
      "  else b = 4'd5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'b'",
                            5, "23.9"));
}

TEST(IfMatchesElaboration, MethodCallThroughPatternIdentifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B} E;\n"
      "  typedef union tagged { E En; int I; } U;\n"
      "  U u = tagged En B;\n"
      "  string s;\n"
      "  initial begin\n"
      "    if (u matches tagged En .ev) $display(\"%s\", ev.name());\n"
      "    if (u matches tagged En .e2 &&& e2.name() == \"B\") s = \"y\";\n"
      "    s = u matches tagged En .e3 ? e3.name() : \"\";\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration, MethodCallThroughPatternIdentifierInFalseArm) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B} E;\n"
      "  typedef union tagged { E En; int I; } U;\n"
      "  U u = tagged En B;\n"
      "  initial if (u matches tagged En .ev) $display(\"%s\", ev.name());\n"
      "  else $display(\"%s\", ev.name());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'ev' resolves to no declaration",
                            6, "23.8"));
}

}  // namespace
