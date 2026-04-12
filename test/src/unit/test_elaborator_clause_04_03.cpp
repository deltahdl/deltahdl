#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventSimulationElaboration, ProcessBodyIsNotNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_NE(mod->processes[0].body, nullptr);
}

TEST(EventSimulationElaboration, BeginEndBlockInProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    x = x + 8'd1;\n"
      "    x = x + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_NE(mod->processes[0].body, nullptr);
}

}  // namespace
