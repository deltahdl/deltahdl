// §6.21: Scope and lifetime

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- lifetime ---
// static | automatic
TEST(ParserA213, LifetimeStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, LifetimeAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int y;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA28, DataDeclAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_automatic, true);
}

TEST(ParserA28, DataDeclStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_static, true);
}

}  // namespace
