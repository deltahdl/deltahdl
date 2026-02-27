// §16.3: Immediate assertions

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.10 Assertion statements — Elaboration
// =============================================================================
// simple_immediate_assert_statement elaborates
TEST(ElabA610, SimpleAssertElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert(1) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// simple_immediate_assume_statement elaborates
TEST(ElabA610, SimpleAssumeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// simple_immediate_cover_statement elaborates
TEST(ElabA610, SimpleCoverElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial cover(1) $display(\"covered\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// multiple assertion types in same module elaborate
TEST(ElabA610, MixedAssertionsElaborate) {
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

}  // namespace
