#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpoff/$dumpon system tasks end to end so the suspend and
// resume semantics of §21.7.1.3 are observed as the production task path
// applies them.
class DumpOffOnSysTask : public VcdTestBase {};

// When $dumpoff executes, a checkpoint is emitted in which every selected
// variable is recorded as x.
TEST_F(DumpOffOnSysTask, DumpOffWritesAllXCheckpoint) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  auto* data = MakeVar(f, "data", 8, 0xA5);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);   // ident '!'
    vcd.RegisterSignal("data", 8, data);  // ident '"'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);    // scalar dumped as x
  EXPECT_NE(content.find("bx \""), std::string::npos);  // vector dumped as x
}

// Between $dumpoff and $dumpon no value changes are dumped: once suspended the
// writer stops emitting even timestamps.
TEST_F(DumpOffOnSysTask, DumpOffSuspendsValueChanges) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
    EXPECT_FALSE(vcd.IsEnabled());
    // A new value at a later time must not appear while dumping is suspended.
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    vcd.WriteTimestamp(300);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("#300"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// When $dumpon executes, dumping resumes and a checkpoint of each variable's
// current value is emitted.
TEST_F(DumpOffOnSysTask, DumpOnResumesWithCurrentValues) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0xA5);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
    // The value that changed while suspended is the one reported at resume.
    data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);
    EvalExpr(MkSysCall(f.arena, "$dumpon", {}), f.ctx, f.arena);
    EXPECT_TRUE(vcd.IsEnabled());
    vcd.WriteTimestamp(400);  // recording is live again
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("b00111100 !"), std::string::npos);  // 0x3C current value
  EXPECT_NE(content.find("#400"), std::string::npos);
}

// With no dump file open the suspend/resume tasks are harmless no-ops.
TEST_F(DumpOffOnSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$dumpon", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

// $dumpoff with no selected variables still emits the checkpoint markers; the
// body between them is empty because there is nothing to record.
TEST_F(DumpOffOnSysTask, DumpOffWithNoSignalsEmitsEmptyCheckpoint) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpoff\n$end"), std::string::npos);
}

// The tasks can bound the dump period more than once: each $dumpoff opens a
// fresh suspended window and each $dumpon resumes it, so repeated cycles emit a
// checkpoint per task invocation.
TEST_F(DumpOffOnSysTask, RepeatedSuspendResumeCycles) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
    EvalExpr(MkSysCall(f.arena, "$dumpon", {}), f.ctx, f.arena);
    EvalExpr(MkSysCall(f.arena, "$dumpoff", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  auto count = [](const std::string& s, const std::string& sub) {
    size_t n = 0;
    for (size_t pos = s.find(sub); pos != std::string::npos;
         pos = s.find(sub, pos + sub.size())) {
      ++n;
    }
    return n;
  };
  EXPECT_EQ(count(content, "$dumpoff"), 2u);
  EXPECT_EQ(count(content, "$dumpon"), 1u);
}

}
}
