#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpportsoff/$dumpportson system tasks end to end so the
// suspend and resume semantics of §21.7.3.2 are observed as the production task
// path applies them. The extended VCD port dump reuses the inherited 4-state
// suspend/resume machinery (§21.7.1.3) for the checkpoints themselves.
class DumpportsOffOnSysTask : public VcdTestBase {};

// §21.7.3.2: when $dumpportsoff executes a checkpoint is written in which every
// selected port is recorded as x. The filename argument denoting the $dumpports
// file is accepted.
TEST_F(DumpportsOffOnSysTask, DumpportsoffWritesAllXCheckpoint) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    SetupClkDataDump(f, vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {MkStr(f.arena, "ports.vcd")}),
             f.ctx, f.arena);
    EXPECT_FALSE(vcd.IsEnabled());
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("x!"), std::string::npos);     // scalar port dumped x
  EXPECT_NE(content.find("bx \""), std::string::npos);  // vector port dumped x
}

// §21.7.3.2: after $dumpportsoff, port values are no longer dumped from that
// simulation time forward. With no filename argument the suspension applies to
// the $dumpports dump.
TEST_F(DumpportsOffOnSysTask, DumpportsoffSuspendsForwardDumping) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
    // A later value change must not appear while the dump is suspended.
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    vcd.WriteTimestamp(300);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("#300"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// §21.7.3.2: when $dumpportson executes, all ports of the associated $dumpports
// call have their current value dumped, and recording resumes.
TEST_F(DumpportsOffOnSysTask, DumpportsonResumesWithCurrentValues) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0xA5);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
    // The value that changed while suspended is the one reported at resume.
    data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);
    EvalExpr(MkSysCall(f.arena, "$dumpportson", {}), f.ctx, f.arena);
    EXPECT_TRUE(vcd.IsEnabled());
    vcd.WriteTimestamp(400);  // recording is live again
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b00111100 !"), std::string::npos);  // 0x3C resumed
  EXPECT_NE(content.find("#400"), std::string::npos);
}

// §21.7.3.2: if $dumpportsoff is executed while port dumping is already
// suspended for the file, the task is ignored, so no second suspend checkpoint
// is written.
TEST_F(DumpportsOffOnSysTask, DumpportsoffIgnoredWhenAlreadySuspended) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"),
            1u);  // second suspend ignored
}

// §21.7.3.2: if $dumpportson is executed while the ports are already being
// dumped, the task is ignored, so no resume checkpoint is written.
TEST_F(DumpportsOffOnSysTask, DumpportsonIgnoredWhenAlreadyDumping) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    // Dumping is active from the start, so a $dumpportson is a no-op.
    EvalExpr(MkSysCall(f.arena, "$dumpportson", {}), f.ctx, f.arena);
    EXPECT_TRUE(vcd.IsEnabled());
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);  // resume ignored
}

// §21.7.3.2: with no dump file open the suspend/resume tasks are harmless
// no-ops.
TEST_F(DumpportsOffOnSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$dumpportson", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
