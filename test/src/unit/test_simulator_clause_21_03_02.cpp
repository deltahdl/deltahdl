#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

static std::string ReadAll(const std::string& path) {
  std::ifstream ifs(path);
  std::stringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

TEST(IoSystemTaskTest, FdisplayToFile) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fdisplay.txt";

  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* fd_lit = MakeInt(f.arena, fd_val.ToUint64());
  auto* disp_expr =
      MakeSysCall(f.arena, "$fdisplay",
                  {fd_lit, MkStr(f.arena, "value=%d"), MakeInt(f.arena, 99)});
  EvalExpr(disp_expr, f.ctx, f.arena);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  EXPECT_EQ(ReadAll(tmp_path), "value=99\n");
  std::remove(tmp_path.c_str());
}

// §21.3.2: $fdisplay terminates with a newline; $fwrite does not.
TEST(IoSystemTaskTest, FwriteSuppressesNewline) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fwrite.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fwrite",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "raw=%d"),
                        MakeInt(f.arena, 7)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  EXPECT_EQ(ReadAll(path), "raw=7");
  std::remove(path.c_str());
}

// §21.3.2: the b/h/o suffix supplies the radix when no format string is given.
TEST(IoSystemTaskTest, FwriteRadixSuffixes) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_radix.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fwriteh",
                       {MakeInt(f.arena, fd), MakeInt(f.arena, 0xab)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fwriteo",
                       {MakeInt(f.arena, fd), MakeInt(f.arena, 8)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fwriteb",
                       {MakeInt(f.arena, fd), MakeInt(f.arena, 5)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);

  std::string contents = ReadAll(path);
  EXPECT_NE(contents.find("ab"), std::string::npos);
  EXPECT_NE(contents.find("10"), std::string::npos);   // 8 in octal
  EXPECT_NE(contents.find("101"), std::string::npos);  // 5 in binary
  std::remove(path.c_str());
}

// §21.3.2: $fstrobe writes to the file using the descriptor for control,
// just like $strobe but routed through the file descriptor.
TEST(IoSystemTaskTest, FstrobeWritesToFile) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fstrobe.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "s=%d"),
                        MakeInt(f.arena, 42)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  EXPECT_EQ(ReadAll(path), "s=42\n");
  std::remove(path.c_str());
}

// §21.3.2: $fmonitor writes to the file under control of the descriptor; any
// number of $fmonitor tasks can be set up simultaneously active (we exercise
// two file targets in succession without one cancelling the other).
TEST(IoSystemTaskTest, FmonitorWritesToFile) {
  SimFixture f;
  std::string path_a = "/tmp/deltahdl_test_fmon_a.txt";
  std::string path_b = "/tmp/deltahdl_test_fmon_b.txt";

  auto fda =
      EvalExpr(
          MakeSysCall(f.arena, "$fopen",
                      {MkStr(f.arena, path_a.c_str()), MkStr(f.arena, "w")}),
          f.ctx, f.arena)
          .ToUint64();
  auto fdb =
      EvalExpr(
          MakeSysCall(f.arena, "$fopen",
                      {MkStr(f.arena, path_b.c_str()), MkStr(f.arena, "w")}),
          f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fda), MkStr(f.arena, "a=%d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fdb), MkStr(f.arena, "b=%d"),
                        MakeInt(f.arena, 2)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fda)}), f.ctx,
           f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fdb)}), f.ctx,
           f.arena);

  EXPECT_EQ(ReadAll(path_a), "a=1\n");
  EXPECT_EQ(ReadAll(path_b), "b=2\n");
  std::remove(path_a.c_str());
  std::remove(path_b.c_str());
}

// §21.3.2: $fstrobe and $fmonitor are controlled by the descriptor argument,
// so they must accept an mcd just as $fdisplay does and fan out to every
// channel selected by its set bits.
TEST(IoSystemTaskTest, FstrobeAndFmonitorAcceptMcd) {
  SimFixture f;
  std::string path_a = "/tmp/deltahdl_test_strobe_mcd_a.txt";
  std::string path_b = "/tmp/deltahdl_test_strobe_mcd_b.txt";

  auto mcd_a =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_a.c_str())}),
               f.ctx, f.arena)
          .ToUint64();
  auto mcd_b =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_b.c_str())}),
               f.ctx, f.arena)
          .ToUint64();

  uint64_t combined = mcd_a | mcd_b;
  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, combined), MkStr(f.arena, "x=%d"),
                        MakeInt(f.arena, 4)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, combined), MkStr(f.arena, "y=%d"),
                        MakeInt(f.arena, 5)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, combined)}), f.ctx,
           f.arena);

  EXPECT_EQ(ReadAll(path_a), "x=4\ny=5\n");
  EXPECT_EQ(ReadAll(path_b), "x=4\ny=5\n");
  std::remove(path_a.c_str());
  std::remove(path_b.c_str());
}

// §21.3.2: every b/h/o suffix variant of $fdisplay, $fstrobe, and $fmonitor
// must dispatch through the same suffix-aware path as $fwrite*, producing the
// expected radix when no format string is given. Per §21.2.1.2 a non-decimal
// radix without an explicit %0 field width always shows leading zeros padded to
// the operand's bit width; the unsized integer literal arguments here are
// 32-bit (§5.7.1), so hex pads to 8 digits, octal to 11, and binary to 32.
TEST(IoSystemTaskTest, DisplayStrobeMonitorRadixSuffixesAllDispatch) {
  SimFixture f;
  struct Case {
    const char* task;
    uint64_t value;
    const char* expected;
  };
  const Case kCases[] = {
      {"$fdisplayh", 0xab, "000000ab\n"},
      {"$fdisplayo", 8, "00000000010\n"},
      {"$fdisplayb", 5, "00000000000000000000000000000101\n"},
      {"$fstrobeh", 0xcd, "000000cd\n"},
      {"$fstrobeo", 9, "00000000011\n"},
      {"$fstrobeb", 6, "00000000000000000000000000000110\n"},
      {"$fmonitorh", 0xef, "000000ef\n"},
      {"$fmonitoro", 7, "00000000007\n"},
      {"$fmonitorb", 3, "00000000000000000000000000000011\n"},
  };
  for (const auto& c : kCases) {
    std::string path =
        std::string("/tmp/deltahdl_test_radix_") + (c.task + 1) + ".txt";
    auto fd = EvalExpr(MakeSysCall(
                           f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
                       f.ctx, f.arena)
                  .ToUint64();
    EvalExpr(MakeSysCall(f.arena, c.task,
                         {MakeInt(f.arena, fd), MakeInt(f.arena, c.value)}),
             f.ctx, f.arena);
    EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
             f.arena);
    EXPECT_EQ(ReadAll(path), c.expected) << "task=" << c.task;
    std::remove(path.c_str());
  }
}

// §21.3.2: a multichannel descriptor with no channel bits set selects no
// files; the file-output task must complete without writing anywhere.
TEST(IoSystemTaskTest, FdisplayMcdWithNoChannelsBitsWritesNothing) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_empty_mcd.txt";

  auto mcd =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())}),
               f.ctx, f.arena)
          .ToUint64();

  // mcd with no bits set selects nothing — even though the underlying file
  // was opened, no write is directed to it because the descriptor argument
  // selects no channels.
  EvalExpr(MakeSysCall(f.arena, "$fdisplay",
                       {MakeInt(f.arena, 0u), MkStr(f.arena, "ghost=%d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd)}), f.ctx,
           f.arena);
  EXPECT_EQ(ReadAll(path), "");
  std::remove(path.c_str());
}

// §21.3.2: $fclose is the means by which an active $fstrobe or $fmonitor task
// is cancelled. After the descriptor is closed, follow-up tasks naming that
// descriptor must not produce additional output.
TEST(IoSystemTaskTest, FcloseCancelsActiveStrobeAndMonitor) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_cancel_strobe_monitor.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "s=%d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "m=%d"),
                        MakeInt(f.arena, 2)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "post_s=%d"),
                        MakeInt(f.arena, 9)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "post_m=%d"),
                        MakeInt(f.arena, 9)}),
           f.ctx, f.arena);

  EXPECT_EQ(ReadAll(path), "s=1\nm=2\n");
  std::remove(path.c_str());
}

// §21.3.2: an mcd selects every file whose channel bit is set; a single
// $fdisplay through that mcd writes to all selected files.
TEST(IoSystemTaskTest, FdisplayMcdFansOut) {
  SimFixture f;
  std::string path_a = "/tmp/deltahdl_test_mcd_a.txt";
  std::string path_b = "/tmp/deltahdl_test_mcd_b.txt";

  auto mcd_a =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_a.c_str())}),
               f.ctx, f.arena)
          .ToUint64();
  auto mcd_b =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_b.c_str())}),
               f.ctx, f.arena)
          .ToUint64();

  uint64_t mcd_combined = mcd_a | mcd_b;
  EvalExpr(MakeSysCall(f.arena, "$fdisplay",
                       {MakeInt(f.arena, mcd_combined),
                        MkStr(f.arena, "hello=%d"), MakeInt(f.arena, 9)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd_combined)}),
           f.ctx, f.arena);

  EXPECT_EQ(ReadAll(path_a), "hello=9\n");
  EXPECT_EQ(ReadAll(path_b), "hello=9\n");
  std::remove(path_a.c_str());
  std::remove(path_b.c_str());
}

}  // namespace
