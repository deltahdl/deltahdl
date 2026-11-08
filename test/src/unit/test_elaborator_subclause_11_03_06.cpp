#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentWithinExpressionElaboration, SimpleAssignInExprInProcedural) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, b;\n"
             "  initial if ((a = b)) ;\n"
             "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration, CompoundAssignInExprInProcedural) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a;\n"
             "  initial a = (a += 1);\n"
             "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration, AssignInContinuousAssignIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     ProceduralContinuousAssignWithoutEmbeddedAssignIsLegal) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, c;\n"
             "  initial assign c = a;\n"
             "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInForkArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial fork\n"
      "    assign c = (a = b);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInAssertionPassStatementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic ok;\n"
      "  initial assert (ok) assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInAssertionFailStatementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic armed;\n"
      "  initial assert (armed) else assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInRandcaseItemIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial randcase 1: assign c = (a = b); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInRandsequenceCodeBlockIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { assign c = (a = b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            5, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInAProceduralEventControlIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a = 0, b = 1;\n"
      "  initial begin\n"
      "    @((a = b)) $display(\"ran\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInANestedOrIntraAssignmentEventControlIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a = 0, b = 1, c;\n"
      "  initial begin\n"
      "    if (b) @(posedge (a += 1)) c = 1;\n"
      "    c = @((a = b)) 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            5, "11.3.6"));
}

TEST(AssignInExprElaboration, AssignmentWithinForceExpressionReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial force c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal "
                            "in this context",
                            3, "11.3.6"));
}

TEST(AssignInExprElaboration, AssignmentOutsideProceduralStatementReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input var int p); endmodule\n"
      "module m;\n"
      "  int y, z;\n"
      "  int x = (y = 1);\n"
      "  localparam int L = (2 + 1);\n"
      "  sub u(.p((z = 2)));\n"
      "endmodule\n",
      f, "m");
  for (uint32_t line : {4u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "assignment operator within expression is "
                              "illegal in this context",
                              line, "11.3.6"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

void ExpectTypeReferenceAssignmentReported(const std::string& line) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n" +
          line + "\nendmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is "
                            "illegal in this context",
                            3, "11.3.6"));
}

TEST(AssignInExprElaboration, AssignmentInATypeReferenceOfAContinuousAssign) {
  ExpectTypeReferenceAssignmentReported(
      "  assign c = type((a = b)) == type(logic);");
}

TEST(AssignInExprElaboration, AssignmentInATypeReferenceOfAnInitializer) {
  ExpectTypeReferenceAssignmentReported(
      "  logic d = type((a += 1)) == type(logic);");
}

TEST(AssignInExprElaboration, AssignmentInATypeReferenceOfANetInitializer) {
  ExpectTypeReferenceAssignmentReported(
      "  wire w = type((a = b)) != type(bit);");
}

TEST(AssignInExprElaboration,
     AssignmentInATypeReferenceOfAProceduralContinuousAssign) {
  ExpectTypeReferenceAssignmentReported(
      "  initial assign c = type((a = b)) == type(logic);");
}

TEST(AssignInExprElaboration, AssignmentInATypeReferenceOfABlockingAssign) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, c;\n"
             "  initial c = type((a = b)) == type(logic);\n"
             "endmodule\n"));
}

}  // namespace
