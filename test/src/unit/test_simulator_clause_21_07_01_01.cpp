#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// $dumpfile records the name of the VCD file to be opened.
TEST(DumpfileSysTask, RecordsRequestedName) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$dumpfile", {MkStr(f.arena, "module1.dump")});
  EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "module1.dump");
}

// The name may also come from a non-literal expression whose value
// carries the character string, such as a string-typed variable.
TEST(DumpfileSysTask, RecordsNameFromStringExpression) {
  SysTaskFixture f;
  auto* var = MakeVar(f, "fname", 64, 0);
  var->value = StringToLogic4Vec(f.arena, "wave.vcd");
  auto* expr = MkSysCall(f.arena, "$dumpfile", {MkId(f.arena, "fname")});
  EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "wave.vcd");
}

// An integral value whose bytes hold a character string is also a
// valid filename source.
TEST(DumpfileSysTask, RecordsNameFromIntegralValue) {
  SysTaskFixture f;
  auto* var = MakeVar(f, "code", 32, 0x77617665);  // ASCII "wave"
  auto* expr = MkSysCall(f.arena, "$dumpfile", {MkId(f.arena, "code")});
  EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "wave");
}

// Each invocation specifies the name anew, so a later call overrides
// an earlier one.
TEST(DumpfileSysTask, LastInvocationDeterminesName) {
  SysTaskFixture f;
  EvalExpr(MkSysCall(f.arena, "$dumpfile", {MkStr(f.arena, "first.vcd")}),
           f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$dumpfile", {MkStr(f.arena, "second.vcd")}),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "second.vcd");
}

// With no argument the name defaults to "dump.vcd".
TEST(DumpfileSysTask, DefaultsWhenArgumentOmitted) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$dumpfile", {});
  EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dump.vcd");
}

}  // namespace
