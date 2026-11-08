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

static std::string ReadAll(const std::string& path) {
  std::ifstream ifs(path);
  std::stringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

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
  EXPECT_NE(contents.find("10"), std::string::npos);
  EXPECT_NE(contents.find("101"), std::string::npos);
  std::remove(path.c_str());
}

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
  f.scheduler.Run();

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  EXPECT_EQ(ReadAll(path), "s=42\n");
  std::remove(path.c_str());
}

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
    f.scheduler.Run();
    EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
             f.arena);
    EXPECT_EQ(ReadAll(path), c.expected) << "task=" << c.task;
    std::remove(path.c_str());
  }
}

TEST(IoSystemTaskTest, FdisplayMcdWithNoChannelsBitsWritesNothing) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_empty_mcd.txt";

  auto mcd =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fdisplay",
                       {MakeInt(f.arena, 0u), MkStr(f.arena, "ghost=%0d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd)}), f.ctx,
           f.arena);
  EXPECT_EQ(ReadAll(path), "");
  std::remove(path.c_str());
}

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
      "      $fmonitor(fd, \"fm %0d %0d %0d\", v, this.v, s);\n"
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
