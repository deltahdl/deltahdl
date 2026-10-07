#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

// These tests are about §21.3.2's file output tasks -- which of them terminate
// with a newline, how a multichannel descriptor fans out, when a strobe or
// monitor is cancelled -- and not about how a value is rendered. They therefore
// write %0d rather than %d.
//
// The distinction is not cosmetic. §21.2.1.2 sizes %d automatically, to the
// widest value the expression can hold, padding with leading spaces: its table
// gives `%d` on `32'd10` as `:        10:`. Only `%0d` yields the minimum
// width, with no leading spaces or zeros. Asserting an unpadded string against
// %d makes each of these tests depend on the width deltahdl assigns the
// expression, which is a separate question from the one being asked here.

static std::string ReadAll(const std::string& path) {
  std::ifstream ifs(path);
  std::stringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

// Drives a whole module through parse -> elaborate -> lower -> run so the
// file-output task under test receives a descriptor produced by a real $fopen
// (its §21.3.1 dependency), not a hand-built descriptor value.
static void RunFullSource(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
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
                  {fd_lit, MkStr(f.arena, "value=%0d"), MakeInt(f.arena, 99)});
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
                       {MakeInt(f.arena, fd), MkStr(f.arena, "raw=%0d"),
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
                       {MakeInt(f.arena, fd), MkStr(f.arena, "s=%0d"),
                        MakeInt(f.arena, 42)}),
           f.ctx, f.arena);
  // §21.2.2: a strobe writes at the end of the time step.
  f.scheduler.Run();

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
                       {MakeInt(f.arena, fda), MkStr(f.arena, "a=%0d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fdb), MkStr(f.arena, "b=%0d"),
                        MakeInt(f.arena, 2)}),
           f.ctx, f.arena);
  // §21.2.3: each monitor writes its list at the end of the time step.
  f.scheduler.Run();

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
                       {MakeInt(f.arena, combined), MkStr(f.arena, "x=%0d"),
                        MakeInt(f.arena, 4)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, combined), MkStr(f.arena, "y=%0d"),
                        MakeInt(f.arena, 5)}),
           f.ctx, f.arena);
  f.scheduler.Run();

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
    // §21.2.3: a monitor's first write comes at the end of the time step.
    f.scheduler.Run();
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
                       {MakeInt(f.arena, 0u), MkStr(f.arena, "ghost=%0d"),
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
                       {MakeInt(f.arena, fd), MkStr(f.arena, "s=%0d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "m=%0d"),
                        MakeInt(f.arena, 2)}),
           f.ctx, f.arena);
  // §21.2.3: the monitor writes its list at the end of the time step.
  f.scheduler.Run();
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "post_s=%0d"),
                        MakeInt(f.arena, 9)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "post_m=%0d"),
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
                        MkStr(f.arena, "hello=%0d"), MakeInt(f.arena, 9)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd_combined)}),
           f.ctx, f.arena);

  EXPECT_EQ(ReadAll(path_a), "hello=9\n");
  EXPECT_EQ(ReadAll(path_b), "hello=9\n");
  std::remove(path_a.c_str());
  std::remove(path_b.c_str());
}

// ---------------------------------------------------------------------------
// §21.3.2 end-to-end: the file-output task's first argument is the mcd/fd its
// §21.3.1 dependency ($fopen) produces from real source. Each test drives the
// full parse/elaborate/lower/run pipeline and reads back what the run wrote.
// ---------------------------------------------------------------------------

// §21.3.2: $fdisplay directs its formatted output to the file named by the fd
// first argument and appends a newline, as its $display counterpart does.
TEST(IoSystemTaskTest, FdisplayThroughFdFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_fdisplay_fd.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fdisplay(fd, \"v=%0d\", 5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "v=5\n");
  std::remove(kPath.c_str());
}

// §21.3.2: $fwrite writes the same formatted text to the fd but, like $write,
// suppresses the trailing newline.
TEST(IoSystemTaskTest, FwriteThroughFdFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_fwrite_fd.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fwrite(fd, \"v=%0d\", 5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "v=5");
  std::remove(kPath.c_str());
}

// §21.3.2: the first argument may equally be a multichannel descriptor; the
// output is directed to the channel the mcd selects.
TEST(IoSystemTaskTest, FdisplayThroughMcdFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_fdisplay_mcd.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"" +
          kPath +
          "\");\n"
          "    $fdisplay(mcd, \"v=%0d\", 9);\n"
          "    $fclose(mcd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "v=9\n");
  std::remove(kPath.c_str());
}

// §21.3.2: $fstrobe writes to the file under control of its descriptor, the
// file counterpart of $strobe.
TEST(IoSystemTaskTest, FstrobeThroughFdFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_fstrobe_fd.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fstrobe(fd, \"s=%0d\", 3);\n"
          "    #1 $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "s=3\n");
  std::remove(kPath.c_str());
}

// §21.3.2: $fmonitor writes to the file under control of its descriptor, the
// file counterpart of $monitor.
TEST(IoSystemTaskTest, FmonitorThroughFdFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_fmonitor_fd.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fmonitor(fd, \"m=%0d\", 4);\n"
          "    #1 $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "m=4\n");
  std::remove(kPath.c_str());
}

// §21.3.2: two mcds bitwise-OR'd together form a descriptor that directs a
// single file-output task to every selected channel. The mcds and their OR are
// all produced by real source expressions.
TEST(IoSystemTaskTest, McdFanoutViaBitwiseOrFromSource) {
  SimFixture f;
  const std::string kPathA = "/tmp/deltahdl_e2e_fanout_a.txt";
  const std::string kPathB = "/tmp/deltahdl_e2e_fanout_b.txt";
  std::remove(kPathA.c_str());
  std::remove(kPathB.c_str());
  RunFullSource(
      "module t;\n"
      "  integer a, b, both;\n"
      "  initial begin\n"
      "    a = $fopen(\"" +
          kPathA +
          "\");\n"
          "    b = $fopen(\"" +
          kPathB +
          "\");\n"
          "    both = a | b;\n"
          "    $fdisplay(both, \"fan=%0d\", 3);\n"
          "    $fclose(both);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPathA), "fan=3\n");
  EXPECT_EQ(ReadAll(kPathB), "fan=3\n");
  std::remove(kPathA.c_str());
  std::remove(kPathB.c_str());
}

// §21.3.2: $fclose is the means by which an active $fstrobe/$fmonitor task is
// cancelled; a task naming the descriptor after it is closed produces no more
// output. Driven end-to-end from source. The monitor writes its list at the
// end of the time step it was set up in (§21.2.3), so the close comes a step
// later.
TEST(IoSystemTaskTest, FcloseCancelsFmonitorFromSource) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_e2e_cancel_fmonitor.txt";
  std::remove(kPath.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fmonitor(fd, \"m=%0d\", 1);\n"
          "    #1 $fclose(fd);\n"
          "    $fmonitor(fd, \"post=%0d\", 2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(kPath), "m=1\n");
  std::remove(kPath.c_str());
}

// §21.3.2 (printed page 667): $fmonitor works as $monitor does (§21.2.3),
// writing its list when called and again at the end of each time step in which
// an argument changed, and any number of $fmonitor tasks may be active at once:
// two on one descriptor each write on the change, a third set up later writes
// beside them, and an $fclose cancels all three (§21.3.1) before a later change
// could write again.
TEST(IoSystemTaskTest, FmonitorsWriteOnEveryChangeUntilClosed) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fmon_changes.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r;\n"
      "  int v = 1;\n"
      "  string line;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fmonitor(fd, \"A %0d\", v);\n"
          "    $fmonitor(fd, \"B %0d\", v);\n"
          "    #1 v = 2;\n"
          "    #1 v = 2;\n"
          "    $fmonitor(fd, \"C %0d\", v + 1);\n"
          "    #1 $fclose(fd);\n"
          "    v = 5;\n"
          "    #1 r = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, r) > 0) $write(\"%s\", line);\n"
          "    $fclose(r);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "A 1\nB 1\nA 2\nB 2\nC 3\n");
  std::remove(path.c_str());
}

// §21.3.2 with §21.2.1.5: a write made at the end of a later time step still
// reads the list in the instance the $fmonitor was written in, and its %m
// names that instance, whichever process ran last. §21.3.1: a multichannel
// monitor is cancelled with the channel it writes, which a later $fopen hands
// to another file that the monitor then leaves alone.
TEST(IoSystemTaskTest, FmonitorKeepsItsScopeAndItsChannels) {
  SimFixture f;
  std::string sub_path = "/tmp/deltahdl_test_fmon_sub.txt";
  std::string mcd_path = "/tmp/deltahdl_test_fmon_mcd.txt";
  std::string reuse_path = "/tmp/deltahdl_test_fmon_reuse.txt";
  RunCapture(
      "module sub(input integer fd);\n"
      "  int x = 1;\n"
      "  initial begin #0 $fmonitor(fd, \"x=%0d %m\", x); #2 x = 7; end\n"
      "endmodule\n"
      "module t;\n"
      "  integer fd, m, m2;\n"
      "  int v = 1;\n"
      "  sub u(fd);\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          sub_path +
          "\", \"w\");\n"
          "    m = $fopen(\"" +
          mcd_path +
          "\");\n"
          "    $fmonitor(m, \"M %0d\", v);\n"
          "    #2 v = 2;\n"
          "    #1 $fclose(m);\n"
          "    m2 = $fopen(\"" +
          reuse_path +
          "\");\n"
          "    v = 3;\n"
          "    #1 $fclose(fd);\n"
          "    $fclose(m2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(ReadAll(sub_path), "x=1 t.u\nx=7 t.u\n");
  EXPECT_EQ(ReadAll(mcd_path), "M 1\nM 2\n");
  EXPECT_EQ(ReadAll(reuse_path), "");
  std::remove(sub_path.c_str());
  std::remove(mcd_path.c_str());
  std::remove(reuse_path.c_str());
}

// §21.3.2 with §21.2.2 (printed page 664): $fstrobe writes its arguments at
// the end of the time step, after every blocking assignment of the step has
// landed, so v = 2 made after the call is what the file holds; the $fwrite
// either side of it is written at once. An $fclose in the same step cancels
// a strobe (§21.3.1).
TEST(IoSystemTaskTest, FstrobeWritesAtTheEndOfTheTimeStep) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fstrobe_end.txt";
  std::string cancelled = "/tmp/deltahdl_test_fstrobe_cancelled.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, r;\n"
      "  int v = 1;\n"
      "  string line;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    c = $fopen(\"" +
          cancelled +
          "\", \"w\");\n"
          "    $fwrite(fd, \"w %0d\\n\", v);\n"
          "    $fstrobe(fd, \"s %0d\", v);\n"
          "    $fstrobe(c, \"gone %0d\", v);\n"
          "    $fclose(c);\n"
          "    v = 2;\n"
          "    #1 $fwrite(fd, \"w %0d\\n\", 3);\n"
          "    $fclose(fd);\n"
          "    r = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, r) > 0) $write(\"%s\", line);\n"
          "    $fclose(r);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "w 1\ns 2\nw 3\n");
  EXPECT_EQ(ReadAll(cancelled), "");
  std::remove(path.c_str());
  std::remove(cancelled.c_str());
}

// §21.3.2 (printed page 667): the file output tasks take the same kinds of
// argument as the tasks they are built on once the descriptor is taken off --
// every argument written in order, a literal after an expression included, an
// expression under the task's radix where no template takes it, an omitted
// argument as a space, and %p formatting an aggregate.
TEST(IoSystemTaskTest, FileTasksTakeTheDisplayArgumentList) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_file_arg_list.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  class C; string n = \"nm\"; endclass\n"
      "  C c = new;\n"
      "  s_t s = '{1, 2};\n"
      "  integer fd, r;\n"
      "  string line;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fdisplayh(fd, 8'hff, \"|\");\n"
          "    $fwriteb(fd, 3'd5, \"|\\n\");\n"
          "    $fdisplay(fd, \"%p\", s);\n"
          "    $fdisplay(fd, \"%s\", c.n, , \"x\");\n"
          "    $fwrite(fd, \"%0d\", 5);\n"
          "    $fwrite(fd, \"|\\n\");\n"
          "    $fclose(fd);\n"
          "    r = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, r) > 0) $write(\"%s\", line);\n"
          "    $fclose(r);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "ff|\n101|\n'{a:1, b:2}\nnm x\n5|\n");
  std::remove(path.c_str());
}

// §21.3.2 with §26.2 and §26.3 (printed pages 808-811): a descriptor held in
// a package variable is one storage location, so the one a package function's
// $fopen assigned is the one the importing module writes through, by its bare
// name and as fio::fd, from forked processes at different times.
TEST(IoSystemTaskTest, DescriptorInAPackageVariableOpenedByAPackageFunction) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_package_fd.txt";
  std::string out = RunCapture(
      "package fio;\n"
      "  integer fd;\n"
      "  function automatic void open_log(string n);\n"
      "    fd = $fopen(n, \"w\");\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import fio::*;\n"
      "  integer rfd;\n"
      "  string line;\n"
      "  initial begin\n"
      "    open_log(\"" +
          path +
          "\");\n"
          "    $display(\"%0d\", fd != 0);\n"
          "    fork\n"
          "      begin #1 $fdisplay(fio::fd, \"p1 at %0t\", $time);\n"
          "            #2 $fdisplay(fd, \"p1 at %0t\", $time); end\n"
          "      begin #2 $fdisplay(fd, \"p2 at %0t\", $time); end\n"
          "    join\n"
          "    $fclose(fd);\n"
          "    rfd = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, rfd) > 0) $write(\"%s\", line);\n"
          "    $fclose(rfd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1\np1 at 1\np2 at 2\np1 at 3\n");
  std::remove(path.c_str());
}

// §21.3.2 with §21.2.2 and §8.6: $fstrobe and $fmonitor called in a class
// method write their lists at the end of the step as the method sees them --
// the object's property bare and as this.v, a static property, and for the
// strobe the method's local, which §13.3.2 bars from a monitor. Each wrote 0.
TEST(IoSystemTaskTest, FstrobeAndFmonitorInAClassMethodReadTheMethodsObject) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fstrobe_method.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, rfd;\n"
      "  string line;\n"
      "  class W;\n"
      "    int v = 1;\n"
      "    static int s = 5;\n"
      "    task run(integer d);\n"
      "      int loc = 7;\n"
      "      $fstrobe(d, \"fs %0d %0d %0d %0d\", v, this.v, s, loc);\n"
      "      $fmonitor(d, \"fm %0d %0d %0d\", v, this.v, s);\n"
      "      v = 4;\n"
      "    endtask\n"
      "  endclass\n"
      "  W w = new;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    w.run(fd);\n"
          "    #1 $fclose(fd);\n"
          "    rfd = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, rfd) > 0) $write(\"%s\", line);\n"
          "    $fclose(rfd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "fs 4 4 5 7\nfm 4 4 5\n");
  std::remove(path.c_str());
}

// §21.3.2 with §21.2.3 and §8.5: $fmonitor works "just like" $monitor, so a
// class property read through a handle is followed too -- written again when
// its value changes, not when a write leaves it as it was, and no more once
// $fclose has cancelled the monitor.
TEST(IoSystemTaskTest, FmonitorOfAPropertyThroughAHandleFollowsItsWrites) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fmonitor_property.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  class C; int p = 1; endclass\n"
      "  C h = new;\n"
      "  integer fd, rfd;\n"
      "  string line;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fmonitor(fd, \"fm %0d\", h.p);\n"
          "    #1 h.p = 7;\n"
          "    #1 h.p = 7;\n"
          "    #1 h.p = 8;\n"
          "    #1 $fclose(fd);\n"
          "    #1 h.p = 9;\n"
          "    rfd = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    while ($fgets(line, rfd) > 0) $write(\"%s\", line);\n"
          "    $fclose(rfd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "fm 1\nfm 7\nfm 8\n");
  std::remove(path.c_str());
}

}  // namespace
