#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;
namespace {

TEST(LoopSyntaxParsing, ForWithMultipleVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = 10; i < j; i++, j--)\n"
      "      a = i + j;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForCommaSeparatedUntypedInit) {
  auto r = Parse(
      "module m;\n"
      "  integer i, j;\n"
      "  initial begin\n"
      "    for (i = 0, j = 10; i < j; i++, j--)\n"
      "      a = i + j;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 12.7.1: a for-loop may leave for_initialization empty and steer itself with
// a variable that an earlier declaration introduced. The A.6.8 file carries
// the bare production case.
TEST(LoopSyntaxParsing, ForEmptyInitWithLoopVariableDeclaredPriorToLoop) {
  auto r = Parse(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    for (; i < 5; i++)\n"
      "      a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForEmptyCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0;; i++) begin\n"
      "      if (i == 5) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 12.7.1 c): for_step normally modifies the loop-control variable, but it is
// optional, and the body may do that work instead. The A.6.8 file carries the
// bare production case.
TEST(LoopSyntaxParsing, ForEmptyStepWithLoopVariableModifiedInBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10;)\n"
      "      i = i + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A for-loop step may be a function/subroutine call, not only an assignment
// or an increment/decrement expression.
TEST(LoopSyntaxParsing, ForFunctionCallStep) {
  auto r = Parse(
      "module m;\n"
      "  function void next(); endfunction\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 5; next())\n"
      "      ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForMixedLocalAndNonLocalInitIsIllegal) {
  auto r = Parse(
      "module m;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    for (x = 0, int y = 0; y < 5; y++)\n"
      "      x = y;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags,
                    "this for-loop initialization mixes a locally declared "
                    "control variable with one declared outside the loop",
                    4, "12.7.1"));
}

TEST(LoopSyntaxParsing, ForAllComponentsEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (;;)\n"
      "      break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.7.1's for_variable_declaration names a data type once and then one or
// more `variable_identifier = expression`, so a declarator after the comma
// that brings no data type of its own declares a variable of the one before
// it, and one that does starts a declaration of its own type.
TEST(LoopSyntaxParsing, ForDeclaratorWithoutTypeTakesThePrecedingType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int a = 0, b = 1, byte c = 2, d = 3; a < 4; a++) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_init_types.size(), 4u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->for_init_types[2].kind, DataTypeKind::kByte);
  EXPECT_EQ(stmt->for_init_types[3].kind, DataTypeKind::kByte);
}

// The preceding declarator's whole data type is taken, its packed dimension
// with it.
TEST(LoopSyntaxParsing, ForDeclaratorWithoutTypeTakesThePackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (logic [7:0] a = 0, b = 1; a < 4; a++) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 2u);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kLogic);
  EXPECT_NE(stmt->for_init_types[1].packed_dim_left, nullptr);
}

}  // namespace
