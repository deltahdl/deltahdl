#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Simple immediate assertion elaboration ---

TEST(AssertionStatementElaboration, AssertWithPassAndFail) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert(1) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssertSemicolonOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssertWithElseOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert(0) else $error(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssumeBasic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, CoverWithPassAction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial cover(1) $display(\"covered\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, CoverSemicolonOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial cover(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AllThreeKindsMixed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert(1);\n"
      "    assume(1);\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssertInAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    assert(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, AssertWithBeginEndActions) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert(1) begin $display(\"a\"); end "
      "else begin $display(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Deferred assertion elaboration ---

TEST(AssertionStatementElaboration, DeferredAssertElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, DeferredAssertFinalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert final (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, DeferredAssumeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, DeferredCoverElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionStatementElaboration, ModuleLevelDeferredAssertElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1;\n"
      "  assert #0 (a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
