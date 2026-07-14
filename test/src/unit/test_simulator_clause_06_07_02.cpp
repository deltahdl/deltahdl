#include <gtest/gtest.h>

#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

static void VerifyNetByName(const RtlirModule* mod, std::string_view name,
                            uint32_t expected_width, bool& found) {
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      found = true;
      EXPECT_EQ(n.width, expected_width);
    }
  }
}

TEST(NettypeSimulation, NettypeCreatesNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net x;\n"
      "  assign x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

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

// §6.7.2: a net declared with a nettype uses any associated resolution
// function. Verify the resolution function is carried onto the lowered net
// in the simulator (not just recorded in the RTLIR).
TEST(NettypeSimulation, ResolvedNettypeNetCarriesResolveFunc) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] T;\n"
      "  function T Tsum(input T driver[]);\n"
      "    Tsum = driver[0];\n"
      "  endfunction\n"
      "  nettype T resolved_net with Tsum;\n"
      "  resolved_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* net = f.ctx.FindNet("x");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->resolve_func, "Tsum");
}

}  // namespace
