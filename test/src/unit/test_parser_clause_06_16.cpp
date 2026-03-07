#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

// §6.16: string type has dynamic width (0 at compile time).
TEST(TypeEval, StringTypeWidthZero) {
  DataType dt;
  dt.kind = DataTypeKind::kString;
  EXPECT_EQ(EvalTypeWidth(dt), 0u);
}

// §6.16: string is not integral.
TEST(TypeEval, StringNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kString));
}

// §6.16: string is not 4-state.
TEST(TypeEval, StringNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kString));
}

TEST(ParserA212, VarDataTypeString) {
  auto r = Parse("module m(input string name); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringBlockDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string msg;\n"
      "    msg = \"test\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function void print_msg(string s);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, Sec6_5_StringVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  string msg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "msg");
}

TEST(ParserCh509, StringLiteral_AsParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string MSG = \"default message\";\n"
              "endmodule"));
}

TEST(ParserSection6, BlockVarDecl_StringType) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string s;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
  EXPECT_EQ(stmt->var_name, "s");
}

TEST(ParserSection11, StringCompareEquality) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s1, s2;\n"
              "  initial begin\n"
              "    s1 = \"hello\";\n"
              "    s2 = \"hello\";\n"
              "    if (s1 == s2) $display(\"equal\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection8, StringTypeModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  string name;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "name");
}

TEST(ParserSection8, StringTypeWithInit) {
  auto r = Parse(
      "module m;\n"
      "  string greeting = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection8, StringTypeBlockLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    string s;\n"
      "    s = \"world\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringInProcedural) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    string s = \"test\";\n"
              "    $display(s);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringDeclBasic) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "s");
}

TEST(ParserSection6, StringDeclWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  string name = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, StringDeclEmptyInit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string s = \"\";\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringParameterDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string DEFAULT_NAME = \"John Smith\";\n"
              "  string myName = DEFAULT_NAME;\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringInFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void greet(string name);\n"
              "    $display(\"Hello %s\", name);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringFunctionReturn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function string get_msg();\n"
              "    return \"ok\";\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringComparison) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string a, b;\n"
              "  initial begin\n"
              "    a = \"abc\";\n"
              "    b = \"def\";\n"
              "    if (a == b) $display(\"equal\");\n"
              "    if (a != b) $display(\"not equal\");\n"
              "    if (a < b) $display(\"less\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, MultipleStringDecls) {
  auto r = Parse(
      "module m;\n"
      "  string x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

}  // namespace
