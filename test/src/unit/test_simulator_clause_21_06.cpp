// §21.6: Command line input

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

static Expr* MakeStrLit(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  // Store with surrounding quotes, matching parser convention.
  auto len = text.size() + 2;
  char* buf = static_cast<char*>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

namespace {

// ============================================================================
// §20.11 — $test$plusargs, $value$plusargs
// ============================================================================
TEST(Section20, TestPlusargsNotFound) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
