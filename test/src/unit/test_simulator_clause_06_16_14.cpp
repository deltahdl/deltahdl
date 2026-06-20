#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Bintoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(10)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "1010");
}

TEST(StringMethods, BintoaZero) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(0)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "0");
}

TEST(StringMethods, BintoaOverwritesExisting) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "old");
  auto* call = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(5)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "101");
}

// The text characterizes bintoa as the inverse of atobin (§6.16.9): the binary
// string it stores must parse back to the original integer.
TEST(StringMethods, BintoaIsInverseOfAtobin) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* store = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(13)});
  EvalExpr(store, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "1101");
  auto* parse = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(parse, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 13u);
}

}  // namespace
