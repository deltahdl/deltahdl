#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §6.14: chandle width is at least pointer-sized (64-bit).
TEST(TypeEval, ChandleWidth64) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

// §6.14: chandle is not integral.
TEST(TypeEval, ChandleNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
}

// §6.14: chandle is not 4-state.
TEST(TypeEval, ChandleNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kChandle));
}

TEST(ParserA221, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kChandle);
}

TEST(ParserSection6, Sec6_5_ChandleVarDecl) {
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

TEST(ParserA84, ConstantPrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

TEST(ParserSection6, ChandleMultipleDecls) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  chandle h1, h2;\n"
              "endmodule\n"));
}

TEST(ParserSection6, ChandleVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(item->name, "ch");
}

// §6.14: chandle as function return type.
TEST(ParserSection6, ChandleFunctionReturn) {
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

// §6.14: chandle as function argument.
TEST(ParserSection6, ChandleFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void use_handle(chandle h);\n"
              "  endfunction\n"
              "endmodule\n"));
}

// §6.14: chandle assignment to null.
TEST(ParserSection6, ChandleAssignNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  initial h = null;\n"
              "endmodule\n"));
}

// §6.14: chandle equality with null.
TEST(ParserSection6, ChandleEqualityWithNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h == null) ? 1 : 0;\n"
              "endmodule\n"));
}

}  // namespace
