// §21.3.3: Formatting data to a string

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
// §21.3.3 — $sformatf
// ============================================================================
TEST(Section20, SformatfBasic) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$sformatf",
                  {MakeStrLit(f.arena, "val=%d"), MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // $sformatf returns a string as a Logic4Vec; the width should be
  // text.size()*8. "val=42" is 6 chars = 48 bits.
  EXPECT_EQ(result.width, 48u);
}

}  // namespace
