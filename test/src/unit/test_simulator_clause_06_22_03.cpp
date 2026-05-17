#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.22.3: "Conversion between assignment-compatible types can involve loss
// of data by truncation or rounding." Assigning a wider integral source to
// a narrower integral sink shall truncate the upper bits at simulation time.
TEST(AssignmentCompatibleSimulation, NarrowerSinkTruncatesUpperBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [15:0] wide;\n"
      "  logic [7:0]  narrow;\n"
      "  initial begin\n"
      "    wide = 16'hABCD;\n"
      "    narrow = wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// §6.22.3: "All equivalent types ... are assignment-compatible types." A
// reg→logic assignment (equivalent under §6.22.2(c)) shall propagate the
// source value verbatim at simulation time.
TEST(AssignmentCompatibleSimulation, EquivalentAssignmentPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  reg   [7:0] r;\n"
      "  logic [7:0] l;\n"
      "  initial begin\n"
      "    r = 8'h77;\n"
      "    l = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("l");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x77u);
}

}  // namespace
