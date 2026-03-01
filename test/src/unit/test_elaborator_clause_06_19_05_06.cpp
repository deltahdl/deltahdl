// §6.19.5.6: Name()

#include "builders_ast.h"
#include "fixture_enum_methods.h"
#include "fixture_evaluator.h"
#include "fixture_lexer.h"
#include "fixture_preprocessor.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EnumMethods, NameForUnknownValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);  // Not a valid member
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // name() returns empty string for invalid enum values.
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
