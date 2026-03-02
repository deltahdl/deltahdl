// §21.5: Writing memory array data to a file

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
// §21.4 — $writememh, $writememb
// ============================================================================
TEST(Section21, WritememhBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememh.txt";

  auto* var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeSysCall(
      f.arena, "$writememh",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeId(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());

  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

}  // namespace
