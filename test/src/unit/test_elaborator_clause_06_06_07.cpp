// §6.6.7: User-defined nettypes

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

static void VerifyNetByName(const RtlirModule* mod, std::string_view name,
                            uint32_t expected_width, bool& found) {
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      found = true;
      EXPECT_EQ(n.width, expected_width);
    }
  }
}

namespace {

// §6.6.7: User-defined nettype creates a net with correct width.
TEST(SimCh6, NettypeCreatesNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net x;\n"
      "  assign x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  // Check RTLIR: x should be in mod->nets, not mod->variables.
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found_net = false;
  VerifyNetByName(mod, "x", 8u, found_net);
  EXPECT_TRUE(found_net) << "x should be elaborated as a net, not a variable";

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("x");
  ASSERT_NE(net, nullptr);
}

}  // namespace
