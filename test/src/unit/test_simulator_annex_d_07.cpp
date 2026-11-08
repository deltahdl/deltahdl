#include <gtest/gtest.h>

#include <filesystem>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <system_error>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

std::string FreshLogPath(const std::string& stem) {
  namespace fs = std::filesystem;
  fs::path path = fs::temp_directory_path() / ("deltahdl_annex_d_07_" + stem);
  std::error_code ec;
  fs::remove(path, ec);
  return path.string();
}

TEST(OptionalLogSim, LoggingEnabledByDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
}

TEST(OptionalLogSim, NologDisablesOutput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $nolog;\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.LoggingEnabled());
}

TEST(OptionalLogSim, LogReenablesOutput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $nolog;\n"
      "    $log;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
}

TEST(OptionalLogSim, LogFilenameOpensNewFile) {
  std::string path = FreshLogPath("opens.log");
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $log(\"" +
          path +
          "\");\n"
          "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LogFile(), path);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_TRUE(std::filesystem::exists(path));
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, LogFilenameReenablesOutput) {
  std::string path = FreshLogPath("reenables.log");
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $nolog;\n"
      "    $log(\"" +
          path +
          "\");\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), path);
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, MostRecentLogFileWins) {
  std::string first = FreshLogPath("wins_first.log");
  std::string second = FreshLogPath("wins_second.log");
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          first +
          "\");\n"
          "    $log(\"" +
          second +
          "\");\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LogFile(), second);
  std::error_code ec;
  std::filesystem::remove(first, ec);
  std::filesystem::remove(second, ec);
}

TEST(OptionalLogSim, NologPreservesLogFile) {
  std::string path = FreshLogPath("preserved.log");
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          path +
          "\");\n"
          "    $nolog;\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), path);
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, BareLogPreservesLogFile) {
  std::string path = FreshLogPath("kept.log");
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          path +
          "\");\n"
          "    $nolog;\n"
          "    $log;\n"
          "  end\n"
          "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), path);
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, BareLogLeavesNoFilenameByDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $log;\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), "");
}

TEST(OptionalLogSim, LogFileHoldsACopyOfWhatIsPrintedToStandardOutput) {
  std::string path = FreshLogPath("copy.log");
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          path +
          "\");\n"
          "    $display(\"hello %0d\", 42);\n"
          "    $write(\"tail\");\n"
          "  end\n"
          "endmodule\n",
      f);
  std::ostringstream tail;
  std::streambuf* old_buf = std::cout.rdbuf(tail.rdbuf());
  f.ctx.Out().put('!');
  f.ctx.Out().flush();
  std::cout.rdbuf(old_buf);
  EXPECT_EQ(out + tail.str(), "hello 42\ntail!");
  EXPECT_EQ(SlurpFile(path), "hello 42\ntail!");
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, NologWithholdsTheCopyAndBareLogResumesIt) {
  std::string path = FreshLogPath("resume.log");
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          path +
          "\");\n"
          "    $display(\"one\");\n"
          "    $nolog;\n"
          "    $display(\"two\");\n"
          "    $log;\n"
          "    $display(\"three\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "one\ntwo\nthree\n");
  EXPECT_EQ(SlurpFile(path), "one\nthree\n");
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, ANewFileNameClosesTheOldFileAndDirectsOutputToTheNew) {
  std::string first = FreshLogPath("first.log");
  std::string second = FreshLogPath("second.log");
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"" +
          first +
          "\");\n"
          "    $display(\"first\");\n"
          "    $log(\"" +
          second +
          "\");\n"
          "    $display(\"second\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(first), "first\n");
  EXPECT_EQ(SlurpFile(second), "second\n");
  std::error_code ec;
  std::filesystem::remove(first, ec);
  std::filesystem::remove(second, ec);
}

TEST(OptionalLogSim, FileOutputTasksPrintingToStandardOutputAreCopied) {
  std::string path = FreshLogPath("fileio.log");
  std::string other = FreshLogPath("other.txt");
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    $log(\"" +
          path +
          "\");\n"
          "    $fdisplay(32'h8000_0001, \"via %s\", \"fd\");\n"
          "    $fwrite(1, \"via mcd\");\n"
          "    fd = $fopen(\"" +
          other +
          "\", \"w\");\n"
          "    $fdisplay(fd, \"elsewhere\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "via fd\nvia mcd");
  std::error_code ec;
  std::filesystem::remove(path, ec);
  std::filesystem::remove(other, ec);
}

}  // namespace
