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

TEST(LoopSyntaxParsing, ForInitWithPackageScopedTypeDeclares) {
  auto r = Parse(
      "package pkg; typedef int word_t; int v; endpackage\n"
      "module m;\n"
      "  int n;\n"
      "  initial begin\n"
      "    for (pkg::word_t i = 0; i < 4; i++) n++;\n"
      "    for (pkg::v = 0; pkg::v < 2; pkg::v++) n++;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  const Stmt* decl = body->stmts[0];
  ASSERT_EQ(decl->for_init_types.size(), 1u);
  EXPECT_EQ(decl->for_init_types[0].kind, DataTypeKind::kNamed);
  EXPECT_EQ(decl->for_init_types[0].scope_name, "pkg");
  EXPECT_EQ(decl->for_init_types[0].type_name, "word_t");
  const Stmt* plain = body->stmts[1];
  ASSERT_EQ(plain->for_inits.size(), 1u);
  for (const auto& t : plain->for_init_types)
    EXPECT_EQ(t.kind, DataTypeKind::kImplicit);
}

}  // namespace
