
#include "fixture_elaborator.h"

using namespace delta;

namespace {

}  // namespace

// =============================================================================
// §10.11 Net alias — elaboration
// =============================================================================

TEST(ElabClause1011, NetAliasNotSilentlyIgnored) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->aliases.size(), 1u);
  ASSERT_EQ(mod->aliases[0].nets.size(), 2u);
}

TEST(ElabClause1011, NetAliasThreeNets) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->aliases.size(), 1u);
  ASSERT_EQ(mod->aliases[0].nets.size(), 3u);
}

// =============================================================================
// §10.11 Net alias — validation (not yet implemented)
// =============================================================================

TEST(ElabClause1011, Validate_NetAlias_TypeCompatibility) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire [15:0] b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_SameTypeOk) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_NoVariables) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_NoSelfAlias) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  alias a = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_ImplicitNetCreation) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}
