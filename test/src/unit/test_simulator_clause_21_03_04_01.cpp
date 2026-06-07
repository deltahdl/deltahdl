#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(IoSystemTaskTest, Ungetc) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_ungetc.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "XY";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  auto* ug = MakeSysCall(f.arena, "$ungetc",
                         {MakeInt(f.arena, 'Z'), MakeInt(f.arena, fd)});
  EvalExpr(ug, f.ctx, f.arena);

  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('Z'));

  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('X'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

// §21.3.4.1: $fgetc reads a single byte and returns its value; once the data is
// exhausted the read fails and yields EOF, represented as -1 (0xFFFFFFFF in the
// 32-bit result). The successful read of 'Z' covers the byte-read behavior, so a
// separate byte-only test would be redundant.
TEST(IoSystemTaskTest, FgetcReturnsEofAtEndOfFile) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fgetc_eof.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "Z";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
  ASSERT_NE(fd, 0u);

  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(getc1, f.ctx, f.arena).ToUint64(),
            static_cast<uint64_t>('Z'));
  // No further data remains: the next read returns EOF.
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(getc2, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(tmp_path.c_str());
}

// §21.3.4.1: a successful $ungetc sets its result to zero (the host library
// returns the pushed character, so the simulator must normalize it to zero).
TEST(IoSystemTaskTest, UngetcReturnsZeroOnSuccess) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_ungetc_ok.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "PQ";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
  ASSERT_NE(fd, 0u);

  auto* ug = MakeSysCall(f.arena, "$ungetc",
                         {MakeInt(f.arena, 'K'), MakeInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(ug, f.ctx, f.arena).ToUint64(), 0u);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(tmp_path.c_str());
}

// §21.3.4.1: when the push back cannot be performed, $ungetc sets its result to
// EOF rather than zero. Pushing EOF itself is rejected by the host stream, which
// drives the failure branch deterministically.
TEST(IoSystemTaskTest, UngetcReturnsEofOnError) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_ungetc_err.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "PQ";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
  ASSERT_NE(fd, 0u);

  // 0xFFFFFFFF narrows to -1, i.e. EOF, which the stream refuses to push back.
  auto* ug = MakeSysCall(
      f.arena, "$ungetc",
      {MakeInt(f.arena, 0xFFFFFFFFu), MakeInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(ug, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(tmp_path.c_str());
}

// §21.3.4.1: a returned byte occupies only the low 8 bits, so the maximal byte
// value 0xFF reads back as 0x000000FF and stays distinct from the EOF sentinel
// (-1). This is the differentiation the standard relies on for a wide result.
TEST(IoSystemTaskTest, FgetcDistinguishesHighByteFromEof) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fgetc_ff.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs.put(static_cast<char>(0xFF));
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  uint64_t fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
  ASSERT_NE(fd, 0u);

  auto* getc = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  uint64_t value = EvalExpr(getc, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(value, 0xFFu);
  EXPECT_NE(value, 0xFFFFFFFFu);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(tmp_path.c_str());
}

}
