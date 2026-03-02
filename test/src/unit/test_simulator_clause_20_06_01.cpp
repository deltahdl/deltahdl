// §20.6.1: Type name function

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ============================================================================
// §20.6.1 — $typename
// ============================================================================
TEST(Section20, Typename) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Returns a string-encoded result; just verify it doesn't crash and
  // returns a non-zero width.
  EXPECT_GT(result.width, 0u);
}

}  // namespace
