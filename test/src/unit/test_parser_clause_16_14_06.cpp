#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(EmbeddedConcurrentAssertion, AssertPropertyEmbeddedInAlways) {
  EXPECT_TRUE(
      ParseOk("module m(input logic clk, input logic a);\n"
              "  always @(posedge clk) begin\n"
              "    assert property (a |-> a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(EmbeddedConcurrentAssertion, CoverPropertyEmbeddedInAlways) {
  EXPECT_TRUE(
      ParseOk("module m(input logic clk, input logic a);\n"
              "  always @(posedge clk) begin\n"
              "    cover property (a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(EmbeddedConcurrentAssertion, AstFlagsProceduralConcurrentAssertion) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    assert property (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  ASSERT_NE(result.cu, nullptr);
  ASSERT_FALSE(result.cu->modules.empty());

  auto* mod = result.cu->modules.back();
  Stmt* found = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kAlwaysBlock) {
      auto* body = it->body;
      ASSERT_NE(body, nullptr);
      if (body->kind == StmtKind::kBlock && !body->stmts.empty()) {
        found = body->stmts.front();
      } else if (body->kind == StmtKind::kAssertImmediate) {
        found = body;
      }
    }
  }
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(found->is_procedural_concurrent);
  EXPECT_FALSE(found->is_deferred);
}

}  // namespace
