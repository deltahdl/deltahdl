#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(StreamingOperatorElaboration, StreamingAsAssignmentSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = {>> {a, b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingWithBitStreamCast) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = int'({<< byte {a}});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingNestedInStreaming) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, RealTargetForStreamingSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real dst;\n"
      "  logic [7:0] a;\n"
      "  initial dst = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, EventTargetForStreamingSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] a;\n"
      "  initial e = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, StreamingAsArithOperandRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, StreamingAsAssignmentTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] src;\n"
      "  initial {>> {a, b}} = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, ChandleTargetForStreamingSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle c;\n"
      "  logic [7:0] a;\n"
      "  initial c = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingConcatWidthIsTheSumOfItsOperandWidths) {
  TypedefMap typedefs;
  Expr first;
  first.kind = ExprKind::kIntegerLiteral;
  first.text = "4'b1100";

  Expr second;
  second.kind = ExprKind::kIntegerLiteral;
  second.text = "4'b0011";

  Expr stream;
  stream.kind = ExprKind::kStreamingConcat;
  stream.op = TokenKind::kGtGt;
  stream.elements = {&first, &second};

  EXPECT_EQ(InferExprWidth(&stream, typedefs), 8u);
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial fork\n"
      "    dst = a + {>> {b}};\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (dst = a + {>> {b}}; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

TEST(StreamingOperatorElaboration, StreamingAsArithOperandInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; dst = a + {>> {b}})\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  logic armed;\n"
      "  initial assert (armed) else dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial randcase 1: dst = a + {>> {b}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { dst = a + {>> {b}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

TEST(StreamingConcatElaboration,
     OperandUseInInitializersAndSubroutinesReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x = 3;\n"
      "  int y = {<< {x}} + 1;\n"
      "  function int f(int v);\n"
      "    return {<< {v}} + 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int z = {<< {x}} + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 5u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "streaming concatenation shall not be used as "
                              "an operand",
                              line, "11.4.14"));
  }
}

TEST(StreamingConcatElaboration, StreamAsInitializerOrReturnValueAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x = 3;\n"
             "  int y = {<< {x}};\n"
             "  function int f(int v);\n"
             "    return {<< {v}};\n"
             "  endfunction\n"
             "  initial begin\n"
             "    automatic int z = {<< {x}};\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StreamingConcatElaboration, StreamAssignedWithinAnExpressionAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] a, b, x, y;\n"
             "  initial begin\n"
             "    x = ({>> {a}} = b);\n"
             "    x = (y = {<< {a}});\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StreamingConcatElaboration,
     StreamCompoundAssignedWithinAnExpressionReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial x = ({>> {a}} += b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      3, "11.4.14"));
}

TEST(StreamingConcatElaboration, StreamInAStatementsOtherExpressionsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    for (int i = 0; {>> {a}}; i++) x = 0;\n"
      "    case (x) {>> {a}}: x = 1; endcase\n"
      "    @({>> {a}}) x = 2;\n"
      "    #({>> {a}}) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "streaming concatenation shall not be used as an operand of an "
        "expression other than an assignment or bit-stream cast",
        line, "11.4.14"));
  }
}

}  // namespace
