#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConstConstantParsing, ConstIntAtModuleLevel) {
  auto r = Parse("module m; const int MAX = 100; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ConstConstantParsing, ConstIntInProceduralBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const int x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

TEST(ConstConstantParsing, ConstVarKeywordInProceduralBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const var int x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ConstConstantParsing, ConstWithLifetimeInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    const var automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ConstConstantParsing, ConstRealDecl) {
  auto r = Parse(
      "module t;\n"
      "  const real PI = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ConstConstantParsing, ConstStringDecl) {
  auto r = Parse(
      "module t;\n"
      "  const string GREETING = \"Hi\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ConstConstantParsing, ConstLogicWithPackedRange) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ConstConstantParsing, ConstLogicCapturesNameAndInit) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "MAX");
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ConstConstantParsing, ConstIntDecl) {
  auto r = Parse(
      "module t;\n"
      "  const int LIMIT = 100;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ConstConstantParsing, ConstVarWithExplicitType) {
  auto r = Parse(
      "module m;\n"
      "  const var logic [7:0] MASK = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->data_type.is_const);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ConstConstantParsing, ConstInBlockSetsConstFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const int C = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_TRUE(body->stmts[0]->var_is_const);
}

TEST(ConstConstantParsing, ConstInitializedFromParameterReference) {
  auto r = Parse(
      "module m #(parameter P = 5);\n"
      "  const int x = P + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->data_type.is_const);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ConstConstantParsing, ConstWithStaticLifetimeInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    const var static int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
