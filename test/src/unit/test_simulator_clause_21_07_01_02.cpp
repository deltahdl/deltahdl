#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdValueChangeSim : public VcdTestBase {};

TEST_F(VcdValueChangeSim, ScalarValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 1);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(VcdValueChangeSim, VectorValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 8, 0xA5);
    vcd.RegisterSignal("data", 8, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

// Exercises the $dumpvars system task itself (not just the writer) so the
// argument handling defined by §21.7.1.2 is observed end to end.
class DumpvarsSysTask : public VcdTestBase {};

// With no arguments, $dumpvars dumps every variable in the model.
TEST_F(DumpvarsSysTask, NoArgumentsDumpsEveryVariable) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    SetupClkDataDump(f, vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars", {}), f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);         // clk
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // data
}

// A scope argument names an individual variable; the leading argument is the
// level count and is not treated as a variable to dump.
TEST_F(DumpvarsSysTask, NamedVariableSelectsOnlyThatVariable) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    SetupClkDataDump(f, vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars",
                       {MkInt(f.arena, 0), MkId(f.arena, "data")}),
             f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // data dumped
  EXPECT_EQ(content.find("1!"), std::string::npos);         // clk omitted
}

// The leading argument is consumed as the level count, so supplying only a
// level (no scope list) still dumps every variable rather than selecting none.
TEST_F(DumpvarsSysTask, LevelCountAloneDumpsEveryVariable) {
  SimFixture f;
  {
    VcdWriter vcd(tmp_path_);
    SetupClkDataDump(f, vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars", {MkInt(f.arena, 0)}), f.ctx,
             f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);         // clk
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // data
}

// A hierarchical scope argument resolves to the variable named by its
// trailing component.
TEST_F(DumpvarsSysTask, HierarchicalNameMatchesLeafVariable) {
  SimFixture f;
  auto* net1 = MakeVar(f, "net1", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("net1", 1, net1);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars",
                       {MkInt(f.arena, 0), MkId(f.arena, "top.mod2.net1")}),
             f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);  // net1 dumped
}

// A scope list may name several individual variables at once; exactly the
// named ones are dumped and the rest are left out.
TEST_F(DumpvarsSysTask, MultipleNamedVariablesSelected) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 1);
  auto* b = MakeVar(f, "b", 1, 0);
  auto* c = MakeVar(f, "c", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("a", 1, a);  // ident '!'
    vcd.RegisterSignal("b", 1, b);  // ident '"'
    vcd.RegisterSignal("c", 1, c);  // ident '#'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(
        MkSysCall(f.arena, "$dumpvars",
                  {MkInt(f.arena, 0), MkId(f.arena, "a"), MkId(f.arena, "b")}),
        f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);   // a dumped
  EXPECT_NE(content.find("0\""), std::string::npos);  // b dumped
  EXPECT_EQ(content.find("1#"), std::string::npos);   // c omitted
}

// A scope that matches no registered variable selects nothing: the dump block
// is still emitted but carries no value changes.
TEST_F(DumpvarsSysTask, UnknownScopeSelectsNothing) {
  SimFixture f;
  auto* clk = MakeVar(f, "clk", 1, 1);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("clk", 1, clk);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars",
                       {MkInt(f.arena, 0), MkId(f.arena, "nosuchsignal")}),
             f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);  // block present
  EXPECT_EQ(content.find("1!"), std::string::npos);         // clk not dumped
}

// With no dump file open there is nowhere to write, so the task is a harmless
// no-op rather than a failure.
TEST_F(DumpvarsSysTask, NoDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpvars", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

// $dumpvars may be invoked as often as desired; each call emits its dump.
TEST_F(DumpvarsSysTask, MayBeInvokedRepeatedly) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 1);
  auto* b = MakeVar(f, "b", 1, 0);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("a", 1, a);
    vcd.RegisterSignal("b", 1, b);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumpvars",
                       {MkInt(f.arena, 0), MkId(f.arena, "a")}),
             f.ctx, f.arena);
    EvalExpr(MkSysCall(f.arena, "$dumpvars",
                       {MkInt(f.arena, 0), MkId(f.arena, "b")}),
             f.ctx, f.arena);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);   // a from first call
  EXPECT_NE(content.find("0\""), std::string::npos);  // b from second call
}

}  // namespace
}  // namespace delta
