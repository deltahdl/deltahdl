// §6.16: String data type

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA212, VarDataTypeString) {
  // var_data_type: data_type (non_integer_type)
  auto r = Parse("module m(input string name); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// string
TEST(ParserA221, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}
// =========================================================================
// §6.16: String in block scope
// =========================================================================
TEST(ParserSection6, StringBlockDecl) {
  // §6.16: string declared inside an initial block.
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
  // §6.16: string as a function argument type.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function void print_msg(string s);\n"
              "  endfunction\n"
              "endmodule\n"));
}
// 23. String variable declaration.
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
// Step 1a: string type in block-level declarations (fixes 6.19.5.6)
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
// =============================================================================
// Section 8.6 -- String data type
// =============================================================================
// Module-level string variable declaration.
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

// String variable with initializer.
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
// String variable inside block-level declaration.
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
  // String declared inside procedural block
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    string s = \"test\";\n"
              "    $display(s);\n"
              "  end\n"
              "endmodule\n"));
}
// =============================================================================
// LRM section 6.16 -- String data type
// =============================================================================
TEST(ParserSection6, StringDeclBasic) {
  // string variable declaration (LRM 6.16)
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
  // string variable with initial value
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
  // string initialized to empty string
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string s = \"\";\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringParameterDecl) {
  // parameter string (LRM 6.16)
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
  // String comparison operators
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
