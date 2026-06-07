#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

// §21.3.4.2 "Reading a line at a time": $fgets reads characters from a file
// descriptor into a destination variable until the variable is filled, a
// newline is read (and kept), or end-of-file is reached. The variable's
// capacity is its number of whole bytes -- a most-significant partial byte is
// not counted. The call returns the number of characters read, or zero when an
// error or end-of-file produced no characters.

using namespace delta;

namespace {

// Writes `content` to a fresh temp file, opens it for reading, and returns the
// file descriptor.
static uint64_t OpenForRead(SysTaskFixture& f, const std::string& tmp,
                            const std::string& content) {
  {
    std::ofstream ofs(tmp, std::ios::binary);
    ofs << content;
  }
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  return EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
}

static uint64_t Fgets(SysTaskFixture& f, const char* var_name, uint64_t fd) {
  auto* expr = MkSysCall(f.arena, "$fgets",
                         {MkId(f.arena, var_name), MkInt(f.arena, fd)});
  return EvalExpr(expr, f.ctx, f.arena).ToUint64();
}

// B1: reading stops once the destination variable is filled. A 24-bit variable
// holds three bytes, so a longer line is truncated to its first three
// characters and the returned count is three.
TEST(FgetsLineRead, FillsToVariableCapacity) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_210304_02_capacity.txt";
  uint64_t fd = OpenForRead(f, tmp, "ABCDEF\n");
  ASSERT_NE(fd, 0u);

  auto* dest = f.ctx.CreateVariable("cap_var", 24);
  dest->value = MakeLogic4VecVal(f.arena, 24, 0);

  EXPECT_EQ(Fgets(f, "cap_var", fd), 3u);
  EXPECT_EQ(dest->value.ToUint64(), 0x414243u);  // "ABC"

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// C: a width that is not a multiple of eight contributes only its whole bytes.
// A 20-bit variable spans two whole bytes plus a partial byte that is ignored,
// so at most two characters are read -- proving the floor, not the ceiling, of
// the byte count is used.
TEST(FgetsLineRead, PartialByteNotCounted) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_210304_02_partial.txt";
  uint64_t fd = OpenForRead(f, tmp, "ABCD");
  ASSERT_NE(fd, 0u);

  auto* dest = f.ctx.CreateVariable("partial_var", 20);
  dest->value = MakeLogic4VecVal(f.arena, 20, 0);

  EXPECT_EQ(Fgets(f, "partial_var", fd), 2u);
  EXPECT_EQ(dest->value.ToUint64(), 0x4142u);  // "AB"

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// B2: a newline terminates the read and is itself transferred into the
// variable; subsequent characters remain available for the next call.
TEST(FgetsLineRead, StopsAtNewlineAndKeepsIt) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_210304_02_newline.txt";
  uint64_t fd = OpenForRead(f, tmp, "Hi\nmore\n");
  ASSERT_NE(fd, 0u);

  auto* dest = f.ctx.CreateVariable("nl_var", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  EXPECT_EQ(Fgets(f, "nl_var", fd), 3u);  // "Hi\n"
  EXPECT_EQ(dest->value.ToUint64() & 0xFFu,
            static_cast<uint64_t>('\n'));  // newline kept as the last byte

  EXPECT_EQ(Fgets(f, "nl_var", fd), 5u);  // "more\n"

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// B3/D/E: a final newline-less line is read to end-of-file and its character
// count returned; a further read at end-of-file produces no characters and
// returns zero.
TEST(FgetsLineRead, ReturnsZeroAtEndOfFile) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_210304_02_eof.txt";
  uint64_t fd = OpenForRead(f, tmp, "AB");
  ASSERT_NE(fd, 0u);

  auto* dest = f.ctx.CreateVariable("eof_var", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  EXPECT_EQ(Fgets(f, "eof_var", fd), 2u);  // "AB" up to EOF
  EXPECT_EQ(Fgets(f, "eof_var", fd), 0u);  // nothing left to read

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// C (edge): a variable narrower than a single byte has no whole bytes, so its
// capacity is zero and no characters can be read -- the count returned is zero
// and the data in the file is left untouched for a later, wider read.
TEST(FgetsLineRead, SubByteVariableReadsNothing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_210304_02_subbyte.txt";
  uint64_t fd = OpenForRead(f, tmp, "AB");
  ASSERT_NE(fd, 0u);

  auto* narrow = f.ctx.CreateVariable("narrow_var", 4);
  narrow->value = MakeLogic4VecVal(f.arena, 4, 0);
  EXPECT_EQ(Fgets(f, "narrow_var", fd), 0u);  // 4 bits -> 0 whole bytes

  // The unread byte is still available to a variable that can hold it.
  auto* wide = f.ctx.CreateVariable("wide_var", 8);
  wide->value = MakeLogic4VecVal(f.arena, 8, 0);
  EXPECT_EQ(Fgets(f, "wide_var", fd), 1u);
  EXPECT_EQ(wide->value.ToUint64(), static_cast<uint64_t>('A'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
