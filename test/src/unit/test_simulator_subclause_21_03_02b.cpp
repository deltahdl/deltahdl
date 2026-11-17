#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_placeholder_paths.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

std::string FilePath(const std::string& tag, int index) {
  return PlaceholderPath("t210302b", tag, index);
}

std::string RunWithPaths(const std::string& tag, const std::string& src,
                         SimFixture& f) {
  return RunWithPlaceholderPaths("t210302b", tag, src, f);
}

void RemovePaths(const std::string& tag) {
  RemovePlaceholderPaths("t210302b", tag);
}

std::string NotImplemented(const std::string& name) {
  return name + " is not a system task or system function this tool implements";
}

TEST(FileOutputTasks, McdOrExpressionInTheCallReachesBothFiles) {
  SimFixture f;
  RunWithPaths("orExpr",
               "module t;\n"
               "  integer a, b;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\");\n"
               "    b = $fopen(\"<P1>\");\n"
               "    $fdisplay(a | b, \"d=%0d\", 1);\n"
               "    $fwrite(a | b, \"w=%0d\\n\", 2);\n"
               "    $fdisplayh(a | b, 8'hab);\n"
               "    $fwriteb(a | b, 2'b10, \"\\n\");\n"
               "    $fclose(a | b);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("orExpr", 0)), "d=1\nw=2\nab\n10\n");
  EXPECT_EQ(SlurpFile(FilePath("orExpr", 1)), "d=1\nw=2\nab\n10\n");
  RemovePaths("orExpr");
}

TEST(FileOutputTasks, McdOrExpressionInTheCallDrivesStrobeAndMonitor) {
  SimFixture f;
  RunWithPaths("orTimed",
               "module t;\n"
               "  integer a, b;\n"
               "  int v = 1;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\");\n"
               "    b = $fopen(\"<P1>\");\n"
               "    $fstrobe(a | b, \"s=%0d\", v);\n"
               "    v = 2;\n"
               "    #1 $fmonitor(a | b, \"m=%0d\", v);\n"
               "    #1 v = 3;\n"
               "    #1 $fclose(a | b);\n"
               "    v = 4;\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("orTimed", 0)), "s=2\nm=2\nm=3\n");
  EXPECT_EQ(SlurpFile(FilePath("orTimed", 1)), "s=2\nm=2\nm=3\n");
  RemovePaths("orTimed");
}

TEST(FileOutputTasks, FcloseOfAnMcdOrExpressionClosesBothFiles) {
  SimFixture f;
  RunWithPaths("orClose",
               "module t;\n"
               "  integer a, b;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\");\n"
               "    b = $fopen(\"<P1>\");\n"
               "    $fdisplay(a, \"a1\");\n"
               "    $fdisplay(b, \"b1\");\n"
               "    $fclose(a | b);\n"
               "    $fdisplay(a, \"a2\");\n"
               "    $fdisplay(b, \"b2\");\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("orClose", 0)), "a1\n");
  EXPECT_EQ(SlurpFile(FilePath("orClose", 1)), "b1\n");
  RemovePaths("orClose");
}

TEST(FileOutputTasks, McdExpressionSettingBitZeroAlsoWritesStandardOutput) {
  SimFixture f;
  testing::internal::CaptureStdout();
  std::string out = RunWithPaths("bitZero",
                                 "module t;\n"
                                 "  integer a;\n"
                                 "  initial begin\n"
                                 "    a = $fopen(\"<P0>\");\n"
                                 "    $fdisplay(a | 1, \"std=%0d\", 4);\n"
                                 "    $fclose(a);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f);
  std::fflush(stdout);
  out += testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "std=4\n");
  EXPECT_EQ(SlurpFile(FilePath("bitZero", 0)), "std=4\n");
  RemovePaths("bitZero");
}

TEST(FileOutputTasks, McdSelectedByAConditionalExpressionInTheCall) {
  SimFixture f;
  RunWithPaths("cond",
               "module t;\n"
               "  integer a, b;\n"
               "  bit sel;\n"
               "  initial begin\n"
               "    a = $fopen(\"<P0>\");\n"
               "    b = $fopen(\"<P1>\");\n"
               "    sel = 1;\n"
               "    $fdisplay(sel ? a : b, \"one\");\n"
               "    sel = 0;\n"
               "    $fdisplay(sel ? a : b, \"two\");\n"
               "    $fclose(a);\n"
               "    $fclose(b);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("cond", 0)), "one\n");
  EXPECT_EQ(SlurpFile(FilePath("cond", 1)), "two\n");
  RemovePaths("cond");
}

TEST(FileOutputTasks, FmonitorIgnoresAChangeOfTimeAlone) {
  SimFixture f;
  RunWithPaths("time",
               "module t;\n"
               "  integer fd;\n"
               "  int v = 1;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w\");\n"
               "    $fmonitor(fd, \"%0t %0d\", $time, v);\n"
               "    #3 v = 2;\n"
               "    #2 $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("time", 0)), "0 1\n3 2\n");
  RemovePaths("time");
}

TEST(FileOutputTasks, FmonitorIgnoresAChangeOfStimeAlone) {
  SimFixture f;
  RunWithPaths("stime",
               "module t;\n"
               "  integer fd;\n"
               "  int v = 1;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w\");\n"
               "    $fmonitor(fd, \"%0d %0d\", $stime, v);\n"
               "    #3 v = 2;\n"
               "    #2 $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("stime", 0)), "0 1\n3 2\n");
  RemovePaths("stime");
}

TEST(FileOutputTasks, FmonitorIgnoresAChangeOfRealtimeAlone) {
  SimFixture f;
  RunWithPaths("realtime",
               "module t;\n"
               "  integer fd;\n"
               "  int v = 1;\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w\");\n"
               "    $fmonitor(fd, \"%0.1f %0d\", $realtime, v);\n"
               "    #3 v = 2;\n"
               "    #2 $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("realtime", 0)), "0.0 1\n3.0 2\n");
  RemovePaths("realtime");
}

TEST(FileOutputTasks, FmonitorOnWithNoArgumentIsNotATask) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $fmonitoron;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$fmonitoron"),
                            2, "20.1"));
}

TEST(FileOutputTasks, FmonitorOnWithADescriptorIsNotATask) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial $fmonitoron(fd);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$fmonitoron"),
                            3, "20.1"));
}

TEST(FileOutputTasks, FmonitorOffWithNoArgumentIsNotATask) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $fmonitoroff;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$fmonitoroff"), 2, "20.1"));
}

TEST(FileOutputTasks, FmonitorOffWithADescriptorIsNotATask) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial $fmonitoroff(fd);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$fmonitoroff"), 3, "20.1"));
}

TEST(FileOutputTasks, MonitorOnAndMonitorOffAreTasks) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial begin $monitoroff; $monitoron; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FileOutputTasks, EveryTaskWritesFromEveryProceduralPlace) {
  SimFixture f;
  RunWithPaths("places",
               "interface ifc;\n"
               "  integer fd;\n"
               "  task automatic put(int v); $fwrite(fd, \"i%0d \", v); "
               "endtask\n"
               "endinterface\n"
               "program p(input integer fd);\n"
               "  initial begin #1 $fwrite(fd, \"p \"); #5; end\n"
               "endprogram\n"
               "class C;\n"
               "  function void put(integer fd); $fwriteo(fd, 6'o10, \" \"); "
               "endfunction\n"
               "endclass\n"
               "module t;\n"
               "  integer fd;\n"
               "  ifc i();\n"
               "  p pp(fd);\n"
               "  C c;\n"
               "  function void f1(); $fdisplayb(fd, 2'b01); endfunction\n"
               "  task t1(); $fstrobeh(fd, 8'h1f); endtask\n"
               "  for (genvar g = 0; g < 1; g++) begin : gen\n"
               "    initial #2 $fwrite(fd, \"g \");\n"
               "  end\n"
               "  initial begin\n"
               "    fd = $fopen(\"<P0>\", \"w\");\n"
               "    i.fd = fd;\n"
               "    c = new;\n"
               "    #1 i.put(7);\n"
               "    c.put(fd);\n"
               "    f1();\n"
               "    t1();\n"
               "    #2 $fclose(fd);\n"
               "  end\n"
               "endmodule\n",
               f);
  EXPECT_EQ(SlurpFile(FilePath("places", 0)), "i7 10 01\np 1f\ng ");
  RemovePaths("places");
}

}  // namespace
