#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection9, Sec9_2_2_2_AlwaysCombVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysVarDecl(r);
}

TEST(ParserSection9, Sec9_2_2_FunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  function logic [7:0] add(input logic [7:0] x, y);\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  always_comb result = add(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kCall);
}

TEST(ParserSection9, Sec9_2_2_2_AlwaysCombFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [3:0] mux2(input logic sel,\n"
              "                            input logic [3:0] a, b);\n"
              "    return sel ? a : b;\n"
              "  endfunction\n"
              "  logic sel;\n"
              "  logic [3:0] a, b, y;\n"
              "  always_comb y = mux2(sel, a, b);\n"
              "endmodule\n"));
}

TEST(ParserSection9, Sec9_2_2_ImplicitSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb c = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);

  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserSection9b, AlwaysCombWithAssertion) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    a = b & c;\n"
      "    assert (a != 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection9, Sec9_2_2_2_AlwaysCombEmptySensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

TEST(ParserSection9c, AlwaysCombWithFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [3:0] mux(input logic sel,\n"
              "                           input logic [3:0] a, b);\n"
              "    return sel ? a : b;\n"
              "  endfunction\n"
              "  logic sel;\n"
              "  logic [3:0] a, b, y;\n"
              "  always_comb y = mux(sel, a, b);\n"
              "endmodule\n"));
}

}
