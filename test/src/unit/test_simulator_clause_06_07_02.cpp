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

TEST(NettypeSimulation, NettypeWideNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [15:0] wide_net;\n"
      "  wide_net y;\n"
      "  assign y = 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found_net = false;
  VerifyNetByName(mod, "y", 16u, found_net);
  EXPECT_TRUE(found_net) << "y should be elaborated as a net";
}

TEST(NettypeSimulation, NettypeNetIsTaggedInSimulator) {
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

  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") {
      found = true;
      EXPECT_TRUE(n.is_user_nettype);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
