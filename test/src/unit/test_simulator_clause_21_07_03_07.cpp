#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the general rules that apply to every extended VCD control task
// (§21.7.3.7): a filename naming a file no $dumpports call opened is ignored,
// and the no-argument form runs the default action. The rules are observed end
// to end as the production control-task dispatch applies them, using
// $dumpportsoff/$dumpportson (whose suspend/resume is visible through the
// writer's enabled state) and $dumpportsall (whose checkpoint is visible in the
// file) as representative control tasks.
class ExtendedVcdControlRules : public VcdTestBase {};

// Opens a $dumpports output named "ports.vcd" through the production task path
// so the file name is registered, leaving the writer enabled and the ports
// dumped. Shared by the rule tests below.
static void OpenPortsDump(SimFixture& f, VcdWriter& vcd) {
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);
  EvalExpr(MkSysCall(f.arena, "$dumpports", {MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);
}

// §21.7.3.7: a control task whose filename does not match any file specified in
// a $dumpports call shall be ignored. $dumpportsoff naming an unopened file
// leaves the dump untouched, so the writer stays enabled and no suspend
// checkpoint is written.
TEST_F(ExtendedVcdControlRules, IgnoresControlTaskNamingUnopenedFile) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);  // ident '!'
    vcd.EndDefinitions();
    OpenPortsDump(f, vcd);

    EvalExpr(
        MkSysCall(f.arena, "$dumpportsoff", {MkStr(f.arena, "nomatch.vcd")}),
        f.ctx, f.arena);
    EXPECT_TRUE(vcd.IsEnabled());  // task ignored, dump still active
  }
  EXPECT_EQ(ReadVcd().find("$dumpoff"), std::string::npos);  // no checkpoint
}

// §21.7.3.7: when the control task's filename matches a file specified in a
// $dumpports call, the task is not ignored but acts on that dump. $dumpportsoff
// naming the opened file suspends it, so the writer is disabled.
TEST_F(ExtendedVcdControlRules, AppliesControlTaskNamingOpenedFile) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);  // ident '!'
    vcd.EndDefinitions();
    OpenPortsDump(f, vcd);

    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {MkStr(f.arena, "ports.vcd")}),
             f.ctx, f.arena);
    EXPECT_FALSE(vcd.IsEnabled());  // matched name: suspend applied
  }
  EXPECT_NE(ReadVcd().find("$dumpoff"), std::string::npos);  // checkpoint written
}

// §21.7.3.7: for the tasks that have only optional arguments, issuing the task
// with no arguments runs the default action. $dumpportsoff with no filename
// suspends the dump (the default action covering every $dumpports file), so the
// writer is disabled even though an explicitly named file exists.
TEST_F(ExtendedVcdControlRules, NoArgumentFormRunsDefaultAction) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);  // ident '!'
    vcd.EndDefinitions();
    OpenPortsDump(f, vcd);

    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {}), f.ctx, f.arena);
    EXPECT_FALSE(vcd.IsEnabled());  // no filename: default action applied
  }
  EXPECT_NE(ReadVcd().find("$dumpoff"), std::string::npos);
}

// §21.7.3.7 edge: the ignore rule keys off filenames specified in $dumpports
// calls. When no $dumpports call has named an output file there is no specified
// name to mismatch, so a control task naming a file is not ignored but acts on
// the lone dump. Here the writer is attached without any $dumpports call, so a
// $dumpportsoff naming an otherwise-unknown file still suspends it.
TEST_F(ExtendedVcdControlRules, NamedTaskAppliesWhenNoDumpportsFilenameSpecified) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);  // ident '!'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);

    EvalExpr(MkSysCall(f.arena, "$dumpportsoff", {MkStr(f.arena, "any.vcd")}),
             f.ctx, f.arena);
    EXPECT_FALSE(vcd.IsEnabled());  // no specified name to mismatch: applied
  }
  EXPECT_NE(ReadVcd().find("$dumpoff"), std::string::npos);
}

// §21.7.3.7: the filename match must be drawn from the task's trailing
// string-literal argument. $dumpportslimit leads with a required filesize, so a
// call carrying only that filesize names no file and is not ignored; the byte
// budget is enforced even though an explicitly named $dumpports file exists (a
// limit comment is inserted and later value changes stop).
TEST_F(ExtendedVcdControlRules, LimitTaskAppliesWithoutFilename) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    OpenPortsDump(f, vcd);  // registers the explicit file name "ports.vcd"

    EvalExpr(MkSysCall(f.arena, "$dumpportslimit", {MkInt(f.arena, 200)}), f.ctx,
             f.arena);
    data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
    for (uint64_t t = 1; t <= 40; ++t) {
      data->value = MakeLogic4VecVal(f.arena, 8, t & 0xFF);
      vcd.WriteTimestamp(t * 10);
      vcd.DumpChangedValues(0);
      data->prev_value = data->value;
    }
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$comment"), std::string::npos);  // limit enforced
  EXPECT_EQ(content.find("#400\n"), std::string::npos);    // late dumps stopped
}

// §21.7.3.7: the ignore rule reaches $dumpportslimit too, and the filename it
// matches is the trailing argument that follows the filesize. Naming an unopened
// file there leaves the limit unset, so dumping continues unbounded: no limit
// comment appears and the late value changes are retained.
TEST_F(ExtendedVcdControlRules, LimitTaskIgnoredWhenTrailingFilenameUnmatched) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    OpenPortsDump(f, vcd);  // registers the explicit file name "ports.vcd"

    EvalExpr(MkSysCall(f.arena, "$dumpportslimit",
                       {MkInt(f.arena, 200), MkStr(f.arena, "nomatch.vcd")}),
             f.ctx, f.arena);
    data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
    for (uint64_t t = 1; t <= 40; ++t) {
      data->value = MakeLogic4VecVal(f.arena, 8, t & 0xFF);
      vcd.WriteTimestamp(t * 10);
      vcd.DumpChangedValues(0);
      data->prev_value = data->value;
    }
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // limit never set
  EXPECT_NE(content.find("#400\n"), std::string::npos);    // late dumps retained
}

}  // namespace
}  // namespace delta
