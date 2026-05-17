#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.3 "The immediate_assertion_statement is a statement_item and can be
// specified anywhere a procedural statement is specified." Elaboration must
// accept immediate assertions in initial, always, and always_comb procedural
// scopes without producing diagnostics.

TEST(ImmediateAssertionElaboration, AssertInInitialBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  initial assert(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, AssumeInAlwaysCombElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  always_comb assume(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, CoverInAlwaysBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) cover(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.3 "The optional statement label (identifier and colon) creates a named
// block around the assertion statement (or any other statement)."
TEST(ImmediateAssertionElaboration, LabeledAssertElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  initial begin chk: assert(a); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.3 cross-links to §20.10 — the body says "The information about
// assertion failure can be printed using one of the severity system tasks
// in the action block, as described in 20.10." Elaboration must accept the
// §20.10 severity tasks inside the action block.
TEST(ImmediateAssertionElaboration, ActionBlockWithSeverityTasksElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert(c) $info(\"pass\"); else $error(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.3 "There are two modes of immediate assertions, simple immediate
// assertions and deferred immediate assertions." Both forms must elaborate.
TEST(ImmediateAssertionElaboration, DeferredImmediateAssertionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial begin\n"
      "    assert #0 (c);\n"
      "    assume final (c);\n"
      "    cover #0 (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
