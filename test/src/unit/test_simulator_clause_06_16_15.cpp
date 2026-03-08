#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Realtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");

  double d = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  std::string result = VecToString(var->value);
  EXPECT_FALSE(result.empty());

  EXPECT_NE(result.find("2.5"), std::string::npos);
}

}  // namespace
