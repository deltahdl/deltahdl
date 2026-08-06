

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ProgramReactiveSim, ProgramInitialObservesNbaUpdateFromModuleInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, c;\n"
      "  initial begin\n"
      "    b = 8'h00;\n"
      "    c = 8'h00;\n"
      "    b <= 8'hAA;\n"
      "  end\n"
      "  program p;\n"
      "    initial c = b;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xAAu);
}

TEST(ProgramReactiveSim, ProgramInitialNbaRoutedToReactiveNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, snap;\n"
      "  program p;\n"
      "    initial begin\n"
      "      b = 8'd0;\n"
      "      snap = 8'd0;\n"
      "      b <= 8'd7;\n"
      "      #0;\n"
      "      snap = b;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

TEST(ProgramReactiveSim, MultipleProgramInitialsAllRunInReactiveSet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x, a, b;\n"
      "  initial begin x = 8'h00; x <= 8'h55; end\n"
      "  program p;\n"
      "    initial a = x;\n"
      "    initial b = x;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0x55u);
}

}  // namespace
