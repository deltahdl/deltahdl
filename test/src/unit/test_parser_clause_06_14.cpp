#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(TypeEval, ChandleWidth64) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(TypeEval, ChandleNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
}

TEST(TypeEval, ChandleNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kChandle));
}

TEST(NetAndVariableTypeParsing, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kChandle);
}

TEST(DataTypeParsing, ChandleVarDecl) {
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

TEST(PrimaryParsing, ConstantPrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

TEST(DataTypeParsing, ChandleMultipleDecls) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  chandle h1, h2;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, ChandleVarDeclSimple) {
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

TEST(DataTypeParsing, ChandleFunctionReturn) {
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

TEST(DataTypeParsing, ChandleFunctionArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void use_handle(chandle h);\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, ChandleAssignNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  initial h = null;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, ChandleEqualityWithNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  chandle h;\n"
              "  int r;\n"
              "  initial r = (h == null) ? 1 : 0;\n"
              "endmodule\n"));
}

}  // namespace
