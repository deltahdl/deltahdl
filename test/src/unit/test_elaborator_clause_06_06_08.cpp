// §6.6.8: Generic interconnect

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// --- §6.6.8 Interconnect restriction tests ---
TEST(Elaboration, InterconnectContAssign_Error) {
  // §6.6.8: interconnect nets cannot be used in continuous assignments.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  assign sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, InterconnectDecl_OK) {
  // §6.6.8: interconnect declaration is legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  // Check that bus is created as a net.
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") found = true;
  }
  EXPECT_TRUE(found);
}

}  // namespace
