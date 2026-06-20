#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpportsall system task end to end so the checkpoint
// semantics of §21.7.3.3 are observed as the production task path applies them.
// The extended VCD port checkpoint reuses the inherited 4-state checkpoint
// machinery (§21.7.1.4).
class DumpportsallSysTask : public VcdTestBase {};

// §21.7.3.3: $dumpportsall creates a checkpoint recording the current value of
// every selected port. The filename argument denoting the $dumpports file is
// accepted.
TEST_F(DumpportsallSysTask, WritesCheckpointOfCurrentValues) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    SetupClkDataDump(f, vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpportsall", {MkStr(f.arena, "ports.vcd")}),
             f.ctx, f.arena);
  }
  auto content = ReadVcd();
  auto pos = content.find("$dumpall");
  EXPECT_NE(pos, std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);            // scalar current
  EXPECT_NE(content.find("b10100101 \""), std::string::npos);  // vector current
  EXPECT_NE(content.find("$end", pos), std::string::npos);  // checkpoint closed
}

// §21.7.3.3: with no dump file open the $dumpportsall task is a harmless no-op.
TEST_F(DumpportsallSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpportsall", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
