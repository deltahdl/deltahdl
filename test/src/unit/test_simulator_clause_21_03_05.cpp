#include <cstdio>
#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, FtellAndFseek) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* ftell_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos = EvalExpr(ftell_expr, f.ctx, f.arena);
  EXPECT_EQ(pos.ToUint64(), 0u);

  auto* fseek_expr =
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 3), MkInt(f.arena, 0)});
  EvalExpr(fseek_expr, f.ctx, f.arena);

  auto* ftell2_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos2 = EvalExpr(ftell2_expr, f.ctx, f.arena);
  EXPECT_EQ(pos2.ToUint64(), 3u);

  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('d'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, RewindResetsPosition) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ABCDEF";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('A'));

  auto* rewind_expr = MkSysCall(f.arena, "$rewind", {MkInt(f.arena, fd)});
  EvalExpr(rewind_expr, f.ctx, f.arena);

  auto* fgetc2_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: operation 1 sets the position to the current location plus offset.
TEST(SysTask, FseekFromCurrentPosition) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek_cur.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx, f.arena);

  // From the current position (2), advance by one more to land on 'd'.
  EvalExpr(MkSysCall(f.arena, "$fseek",
                     {MkInt(f.arena, fd), MkInt(f.arena, 1), MkInt(f.arena, 1)}),
           f.ctx, f.arena);
  auto ch = EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx,
                     f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('d'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: operation 2 sets the position to EOF plus the signed offset, so a
// negative 32-bit offset seeks backward from the end of the file.
TEST(SysTask, FseekFromEndWithSignedOffset) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek_end.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  // 0xFFFFFFFE is a 32-bit -2; from EOF (6) this resolves to position 4 ('e').
  EvalExpr(MkSysCall(f.arena, "$fseek",
                     {MkInt(f.arena, fd), MkInt(f.arena, 0xFFFFFFFEu),
                      MkInt(f.arena, 2)}),
           f.ctx, f.arena);
  auto ch = EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx,
                     f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('e'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: $ftell returns EOF (-1) when the position cannot be obtained.
TEST(SysTask, FtellReturnsEofOnError) {
  SysTaskFixture f;
  auto pos = EvalExpr(MkSysCall(f.arena, "$ftell", {MkInt(f.arena, 0x12345u)}),
                      f.ctx, f.arena);
  EXPECT_EQ(pos.ToUint64(), static_cast<uint64_t>(-1));
}

// §21.3.5: $rewind reports -1 when the reposition fails (invalid descriptor).
TEST(SysTask, RewindReturnsEofOnError) {
  SysTaskFixture f;
  auto code = EvalExpr(
      MkSysCall(f.arena, "$rewind", {MkInt(f.arena, 0x12345u)}), f.ctx, f.arena);
  EXPECT_EQ(code.ToUint64(), static_cast<uint64_t>(-1));
}

// §21.3.5: $fseek reports 0 for a successful reposition and -1 on failure.
TEST(SysTask, FseekReturnsCode) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek_code.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  auto ok = EvalExpr(
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 3), MkInt(f.arena, 0)}),
      f.ctx, f.arena);
  EXPECT_EQ(ok.ToUint64(), 0u);

  // An invalid descriptor cannot be repositioned, so the error code is used.
  auto bad = EvalExpr(
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, 0x12345u), MkInt(f.arena, 0), MkInt(f.arena, 0)}),
      f.ctx, f.arena);
  EXPECT_EQ(bad.ToUint64(), static_cast<uint64_t>(-1));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: repositioning with $fseek shall cancel any pending $ungetc push-back.
TEST(SysTask, FseekCancelsUngetc) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek_ungetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  // Push back a character that would otherwise be returned by the next read.
  EvalExpr(MkSysCall(f.arena, "$ungetc",
                     {MkInt(f.arena, static_cast<uint64_t>('Z')),
                      MkInt(f.arena, fd)}),
           f.ctx, f.arena);
  // The reposition discards the push-back, so reading resumes from the file.
  EvalExpr(MkSysCall(f.arena, "$fseek",
                     {MkInt(f.arena, fd), MkInt(f.arena, 0), MkInt(f.arena, 0)}),
           f.ctx, f.arena);
  auto ch = EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx,
                     f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('a'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: repositioning with $rewind shall also cancel any $ungetc push-back.
TEST(SysTask, RewindCancelsUngetc) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_rewind_ungetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$ungetc",
                     {MkInt(f.arena, static_cast<uint64_t>('Z')),
                      MkInt(f.arena, fd)}),
           f.ctx, f.arena);
  EvalExpr(MkSysCall(f.arena, "$rewind", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  auto ch = EvalExpr(MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)}), f.ctx,
                     f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('a'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.5: $fseek may set the position past the end of the existing data; the
// reposition succeeds and the resulting offset is reported by $ftell.
TEST(SysTask, FseekBeyondEndOfFile) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek_past_eof.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  // The file holds six bytes; seeking to offset 100 from the start lands well
  // beyond the data yet still reports success.
  auto code = EvalExpr(
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 100), MkInt(f.arena, 0)}),
      f.ctx, f.arena);
  EXPECT_EQ(code.ToUint64(), 0u);

  auto pos = EvalExpr(MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)}), f.ctx,
                      f.arena);
  EXPECT_EQ(pos.ToUint64(), 100u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}
