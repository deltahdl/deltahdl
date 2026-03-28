#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// "Parameter constants can be initialized with a literal."
// The three examples from §6.20.

TEST(ParameterConstantParsing, LocalparamByteInitWithStringLiteral) {
  auto r = Parse(
      "module m;\n"
      "  localparam byte colon1 = \":\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "colon1");
  EXPECT_TRUE(item->is_localparam);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kStringLiteral);
}

TEST(ParameterConstantParsing, SpecparamInitWithIntegerLiteral) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam);
  ASSERT_NE(item, nullptr);
}

TEST(ParameterConstantParsing, ParameterLogicInitWithLiteral) {
  auto r = Parse(
      "module m;\n"
      "  parameter logic flag = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "flag");
  EXPECT_FALSE(item->is_localparam);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kIntegerLiteral);
}

// All three parameter constant kinds parse in a single module.
TEST(ParameterConstantParsing, AllThreeParameterConstantKindsParse) {
  auto r = Parse(
      "module m;\n"
      "  parameter int P = 1;\n"
      "  localparam int LP = 2;\n"
      "  specparam SP = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam));
}

}  // namespace
