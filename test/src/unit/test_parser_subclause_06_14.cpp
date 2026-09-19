#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  chandle handle;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kChandle);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "handle");
}

TEST(ChandleDataType, ConstantPrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

TEST(ChandleDataType, ChandleMultipleDecls) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  chandle h1, h2;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleFunctionReturn) {
  auto r = Parse(
      "module m;\n"
      "  function chandle get_handle();\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kChandle);
}

TEST(ChandleDataType, ChandleFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void use_handle(chandle h);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleAssignNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  initial h = null;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleEqualityWithNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h == null) ? 1 : 0;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleTaskArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task do_something(chandle h);\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleInequalityNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h != null) ? 1 : 0;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleCaseEqualityNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h === null) ? 1 : 0;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleCaseInequalityNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h !== null) ? 1 : 0;\n"
              "endmodule\n"));
}

TEST(ChandleDataType, ChandleChandleEquality) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle a, b;\n"
              "  int r;\n"
              "  initial r = (a == b) ? 1 : 0;\n"
              "endmodule\n"));
}

// §6.14 (printed page 111) makes chandle a data type, declared as
// `chandle name;`, and A.2.2.1 (printed page 1182) lists it among data_type's
// bare keyword alternatives, so a block item opening with it is a
// data_declaration wherever A.2.8 places one: the locals of a function or
// task body and the head of a seq_block. IsDataTypeKeyword left the keyword
// out, so the parser read such a line as an expression statement and reported
// "expected expression" under §11.2.
TEST(ChandleDataType, ChandleQueueFirstLocalOfFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    chandle tmp[$];\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* f = FindItemByName(r.cu->modules[0]->items, "f");
  ASSERT_NE(f, nullptr);
  ASSERT_GE(f->func_body_stmts.size(), 1u);
  EXPECT_EQ(f->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(f->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(f->func_body_stmts[0]->var_name, "tmp");
  EXPECT_EQ(f->func_body_stmts[0]->var_unpacked_dims.size(), 1u);
}

TEST(ChandleDataType, ChandleQueueFirstLocalOfTask) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    chandle tmp[$];\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FindItemByName(r.cu->modules[0]->items, "t");
  ASSERT_NE(t, nullptr);
  ASSERT_GE(t->func_body_stmts.size(), 1u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(t->func_body_stmts[0]->var_name, "tmp");
  EXPECT_EQ(t->func_body_stmts[0]->var_unpacked_dims.size(), 1u);
}

TEST(ChandleDataType, ChandleFirstItemOfSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    chandle h;\n"
      "    h = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_decl_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(body->stmts[0]->var_name, "h");
}

}  // namespace
