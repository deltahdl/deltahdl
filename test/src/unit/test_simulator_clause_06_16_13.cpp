#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Octtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(8)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "10");
}

TEST(StringMethods, OcttoaZero) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(0)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "0");
}

TEST(StringMethods, OcttoaOverwritesExisting) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "old");
  auto* call = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(64)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "100");
}

// The text characterizes octtoa as the inverse of atooct (§6.16.9): the octal
// string it stores must parse back to the original integer.
TEST(StringMethods, OcttoaIsInverseOfAtooct) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* store = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(511)});
  EvalExpr(store, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "777");
  auto* parse = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(parse, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 511u);
}

}  // namespace
