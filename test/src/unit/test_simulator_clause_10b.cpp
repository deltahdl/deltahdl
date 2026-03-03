// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §10.4.2: NBA case default branch.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBACaseDefaultBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 99;\n"
      "    case (sel)\n"
      "      0: result <= 10;\n"
      "      1: result <= 20;\n"
      "      default: result <= 77;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bitwise NOT on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBABitwiseNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    result <= ~a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // ~0xF0 = 0x0F (in 8 bits).
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with replication on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAReplicationRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result <= {4{2'b10}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // {4{2'b10}} = 8'b10101010 = 0xAA.
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

}  // namespace
