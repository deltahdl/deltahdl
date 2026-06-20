#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpall system task end to end so the checkpoint semantics of
// §21.7.1.4 are observed as the production task path applies them.
class DumpallSysTask : public VcdTestBase {};

// $dumpall creates a checkpoint that records the current value of every
// selected variable, delimited by the $dumpall/$end keywords.
TEST_F(DumpallSysTask, DumpallWritesCheckpointOfCurrentValues) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  auto* data = MakeVar(f, "data", 8, 0xA5);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);    // ident '!'
    vcd.RegisterSignal("data", 8, data);  // ident '"'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpall", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  auto pos = content.find("$dumpall");
  EXPECT_NE(pos, std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);            // scalar current
  EXPECT_NE(content.find("b10100101 \""), std::string::npos);  // vector current
  EXPECT_NE(content.find("$end", pos), std::string::npos);  // checkpoint closed
}

// While dumping is enabled the dumper records only the variables that change in
// a time increment; variables that did not change are not dumped.
TEST_F(DumpallSysTask, EnabledDumpRecordsOnlyChangedVariables) {
  SimFixture f;
  auto* changed = MakeVar(f, "changed", 8, 0x3C);
  changed->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
  auto* steady = MakeVar(f, "steady", 8, 0xA5);
  steady->prev_value = MakeLogic4VecVal(f.arena, 8, 0xA5);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("changed", 8, changed);  // ident '!'
    vcd.RegisterSignal("steady", 8, steady);    // ident '"'
    vcd.EndDefinitions();
    EXPECT_TRUE(vcd.IsEnabled());
    vcd.WriteTimestamp(100);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b00111100 !"), std::string::npos);   // changed dumped
  EXPECT_EQ(content.find("b10100101 \""), std::string::npos);  // steady skipped
}

// With no dump file open the $dumpall task is a harmless no-op.
TEST_F(DumpallSysTask, DumpallWithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpall", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
