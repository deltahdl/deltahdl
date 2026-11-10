#include <gtest/gtest.h>

#include <cstdint>
#include <string>
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

TEST(NettypeSimulation,
     DISABLED_UnpackedArrayNettypeNetHoldsTheArrayItIsDriven) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef real TR [5];\n"
      "  nettype TR wTR;\n"
      "  wTR w5;\n"
      "  real v [5] = '{1.0, 2.0, 3.0, 4.0, 5.0};\n"
      "  assign w5 = v;\n"
      "  initial #1 $display(\"%.1f %.1f\", w5[0], w5[4]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.0 5.0\n");
}

TEST(NettypeSimulation,
     DISABLED_ArrayOfUnpackedArrayNettypeNetsHoldsEachArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int TI [3];\n"
      "  nettype TI wTI;\n"
      "  wTI w6 [2];\n"
      "  assign w6[0] = '{1, 2, 3};\n"
      "  assign w6[1] = '{4, 5, 6};\n"
      "  initial #1 $display(\"%0d %0d\", w6[0][2], w6[1][0]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 4\n");
}

TEST(NettypeSimulation, UnpackedStructNettypeNetHoldsTheStructItIsDriven) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; real r; } TS;\n"
      "  nettype TS wTS;\n"
      "  wTS w;\n"
      "  assign w = '{7, 2.5};\n"
      "  initial #1 $display(\"%0d %.1f\", w.a, w.r);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 2.5\n");
}

}  // namespace
