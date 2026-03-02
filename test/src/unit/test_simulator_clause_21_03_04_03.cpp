// §21.3.4.3: Reading formatted data

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
// §21.3.5 — $sscanf
// ============================================================================
TEST(Section21, SscanfDecimal) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MakeSysCall(f.arena, "$sscanf",
                  {MakeStrLit(f.arena, "42"), MakeStrLit(f.arena, "%d"),
                   MakeId(f.arena, "scanned")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // 1 item scanned
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

}  // namespace
