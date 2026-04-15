// §23.3.1

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TopLevelModules, TopLevelModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(TopLevelModules, DollarRootAssignSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial $root.top.a = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("a");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(TopLevelModules, DollarRootReadSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd77;\n"
      "    dst = $root.top.src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("dst");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(TopLevelModules, DollarRootDisambiguatesFromLocalScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child child_inst();\n"
      "  initial begin\n"
      "    x = 8'd20;\n"
      "    x = $root.top.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 20u);
}

}  // namespace
