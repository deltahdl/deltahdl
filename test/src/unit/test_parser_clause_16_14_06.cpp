#include "fixture_parser.h"

using namespace delta;

namespace {

// §16.14.6 P1: "A concurrent assertion statement can also be embedded in a
// procedural block."  Observe that `assert property (...)` is accepted
// inside an always procedure as a procedural concurrent assertion
// (distinct from the §16.3 immediate `assert (expr)` form).
TEST(EmbeddedConcurrentAssertion, AssertPropertyEmbeddedInAlways) {
  EXPECT_TRUE(ParseOk(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    assert property (a |-> a);\n"
      "  end\n"
      "endmodule\n"));
}

// §16.14.6: cover property is one of the concurrent assertion kinds (§16.2)
// that can also appear in a procedural block.  Exercises a different
// parser entry point (ParseImmediateCover) than the assert/assume form.
TEST(EmbeddedConcurrentAssertion, CoverPropertyEmbeddedInAlways) {
  EXPECT_TRUE(ParseOk(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    cover property (a);\n"
      "  end\n"
      "endmodule\n"));
}

// §16.14.6 P2: "The term *procedural concurrent assertion* is used to
// refer to any concurrent assertion statement that appears in procedural
// code."  Observe that the AST node carries the procedural-concurrent
// flag, distinguishing it from a §16.3 immediate assertion that shares
// the same keyword.
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
  // The always procedure is the last module item; drill into its body.
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
