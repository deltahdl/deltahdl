#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ParameterizedModules, ParameterizedModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 4)(\n"
      "  input logic [W-1:0] a,\n"
      "  output logic [W-1:0] y);\n"
      "  assign y = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterizedModules, NonAnsiParameterizedModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 4)(a, y);\n"
      "  input [W-1:0] a;\n"
      "  output [W-1:0] y;\n"
      "  assign y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
