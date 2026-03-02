// §21.3.2: File output system tasks

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
// §21.3.3 — $fdisplay, $fwrite
// ============================================================================
TEST(Section21, FdisplayToFile) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fdisplay.txt";

  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* fd_lit = MakeInt(f.arena, fd_val.ToUint64());
  auto* disp_expr = MakeSysCall(
      f.arena, "$fdisplay",
      {fd_lit, MakeStrLit(f.arena, "value=%d"), MakeInt(f.arena, 99)});
  EvalExpr(disp_expr, f.ctx, f.arena);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  // Read back and verify.
  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_EQ(contents, "value=99\n");

  std::remove(tmp_path.c_str());
}

}  // namespace
