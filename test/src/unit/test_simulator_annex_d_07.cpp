#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <system_error>

#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"
#include "helpers_reported_error.h"
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

std::string WithLogPath(std::string src, const std::string& path) {
  for (auto at = src.find("<P>"); at != std::string::npos;
       at = src.find("<P>", at + path.size())) {
    src.replace(at, 3, path);
  }
  return src;
}

struct LoggedRun {
  std::string out;
  std::string log;
};

LoggedRun RunLogged(const std::string& stem, const std::string& src,
                    SimFixture& f) {
  std::string path = FreshLogPath(stem);
  LoggedRun run;
  run.out = RunCapture(WithLogPath(src, path), f);
  run.log = SlurpFile(path);
  std::error_code ec;
  std::filesystem::remove(path, ec);
  return run;
}

TEST(OptionalLogSim, LogAndNologWorkWhereverTheyRun) {
  constexpr const char* kPlacements[] = {
      "module t;\n"
      "  task open_log; $log(\"<P>\"); endtask\n"
      "  task off; $nolog; endtask\n"
      "  task on; $log; endtask\n"
      "  initial begin\n"
      "    open_log();\n"
      "    $display(\"a\");\n"
      "    off();\n"
      "    $display(\"b\");\n"
      "    on();\n"
      "    $display(\"c\");\n"
      "  end\n"
      "endmodule\n",
      "module t;\n"
      "  function void open_log; $log(\"<P>\"); endfunction\n"
      "  function void off; $nolog; endfunction\n"
      "  function void on; $log; endfunction\n"
      "  initial begin\n"
      "    open_log();\n"
      "    $display(\"a\");\n"
      "    off();\n"
      "    $display(\"b\");\n"
      "    on();\n"
      "    $display(\"c\");\n"
      "  end\n"
      "endmodule\n",
      "module t;\n"
      "  class C;\n"
      "    function void open_log; $log(\"<P>\"); endfunction\n"
      "    function void off; $nolog; endfunction\n"
      "    function void on; $log; endfunction\n"
      "  endclass\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.open_log();\n"
      "    $display(\"a\");\n"
      "    c.off();\n"
      "    $display(\"b\");\n"
      "    c.on();\n"
      "    $display(\"c\");\n"
      "  end\n"
      "endmodule\n",
      "program p;\n"
      "  initial begin\n"
      "    $log(\"<P>\");\n"
      "    $display(\"a\");\n"
      "    $nolog;\n"
      "    $display(\"b\");\n"
      "    $log;\n"
      "    $display(\"c\");\n"
      "  end\n"
      "endprogram\n",
  };
  for (const char* src : kPlacements) {
    SimFixture f;
    LoggedRun run = RunLogged("placement.log", src, f);
    EXPECT_FALSE(f.has_errors) << src;
    EXPECT_EQ(run.out, "a\nb\nc\n") << src;
    EXPECT_EQ(run.log, "a\nc\n") << src;
  }
}

TEST(OptionalLogSim, MonitorAndStrobeTextIsCopied) {
  SimFixture f;
  LoggedRun run = RunLogged("monitor.log",
                            "module t;\n"
                            "  int x;\n"
                            "  initial begin\n"
                            "    $log(\"<P>\");\n"
                            "    x = 1;\n"
                            "    $strobe(\"strobed %0d\", x);\n"
                            "    $monitor(\"monitored %0d\", x);\n"
                            "    #1 x = 2;\n"
                            "  end\n"
                            "endmodule\n",
                            f);
  EXPECT_NE(run.out.find("strobed 1"), std::string::npos) << run.out;
  EXPECT_NE(run.out.find("monitored 2"), std::string::npos) << run.out;
  EXPECT_EQ(run.log, run.out);
}

TEST(OptionalLogSim, SeverityAndFinishTextOnStandardOutputIsCopied) {
  SimFixture f;
  LoggedRun run = RunLogged("severity.log",
                            "module t;\n"
                            "  initial begin\n"
                            "    $log(\"<P>\");\n"
                            "    $info(\"info_text\");\n"
                            "    $warning(\"warning_text\");\n"
                            "    $error(\"error_text\");\n"
                            "    $fatal(1, \"fatal_text\");\n"
                            "  end\n"
                            "endmodule\n",
                            f);
  for (const char* text : {"info_text", "warning_text", "$finish"}) {
    EXPECT_NE(run.out.find(text), std::string::npos) << run.out;
  }
  EXPECT_EQ(run.log, run.out);
}

TEST(OptionalLogSim, AnExistingFileIsCreatedAfresh) {
  std::string path = FreshLogPath("stale.log");
  {
    std::ofstream stale(path);
    stale << "stale\n";
  }
  SimFixture f;
  RunCapture(WithLogPath("module t;\n"
                         "  initial begin\n"
                         "    $log(\"<P>\");\n"
                         "    $display(\"fresh\");\n"
                         "  end\n"
                         "endmodule\n",
                         path),
             f);
  EXPECT_EQ(SlurpFile(path), "fresh\n");
  std::error_code ec;
  std::filesystem::remove(path, ec);
}

TEST(OptionalLogSim, NamingTheCurrentLogFileCreatesItAfresh) {
  SimFixture f;
  LoggedRun run = RunLogged("again.log",
                            "module t;\n"
                            "  initial begin\n"
                            "    $log(\"<P>\");\n"
                            "    $display(\"one\");\n"
                            "    $log(\"<P>\");\n"
                            "    $display(\"two\");\n"
                            "  end\n"
                            "endmodule\n",
                            f);
  EXPECT_EQ(run.log, "two\n");
}

constexpr const char* kLogForm =
    "$log is written as a task statement with no argument or with one string "
    "naming the log file, and this call is not";

constexpr const char* kNologForm =
    "$nolog is written as a task statement with no argument, and this call is "
    "not";

std::string LogCall(const std::string& args) {
  std::string call = "$log(\"";
  call += FreshLogPath("form.log");
  call += "\"";
  call += args;
  call += ")";
  return call;
}

TEST(OptionalLogForm, DISABLED_NologWithAnArgumentIsReported) {
  ExpectOnlyTheMalformedCallReported("$nolog", "$nolog(\"x\")", kNologForm,
                                     "D.7");
}

TEST(OptionalLogForm, DISABLED_LogWithTwoArgumentsIsReported) {
  ExpectOnlyTheMalformedCallReported(LogCall(""), LogCall(", 3"), kLogForm,
                                     "D.7");
  FreshLogPath("form.log");
}

TEST(OptionalLogForm, DISABLED_LogWhoseArgumentIsNoStringIsReported) {
  ExpectOnlyTheMalformedCallReported(LogCall(""), "$log(5)", kLogForm, "D.7");
  FreshLogPath("form.log");
  std::error_code ec;
  std::filesystem::remove("5", ec);
}

TEST(OptionalLogForm, DISABLED_LogAndNologUsedAsFunctionsAreReported) {
  ExpectOnlyTheMalformedCallReported("$log", "v = $log", kLogForm, "D.7");
  ExpectOnlyTheMalformedCallReported("$nolog", "v = $nolog", kNologForm, "D.7");
}

TEST(OptionalLogForm, DISABLED_AStringVariableIsNeverTakenAsTheFileName) {
  std::string path = FreshLogPath("by_value.log");
  std::error_code ec;
  std::filesystem::remove("log_name", ec);
  SimFixture f;
  RunCapture(WithLogPath("module t;\n"
                         "  string log_name;\n"
                         "  initial begin\n"
                         "    log_name = \"<P>\";\n"
                         "    $log(log_name);\n"
                         "    $display(\"by value\");\n"
                         "  end\n"
                         "endmodule\n",
                         path),
             f);
  bool named_after_identifier = std::filesystem::exists("log_name");
  std::filesystem::remove("log_name", ec);
  EXPECT_FALSE(named_after_identifier);
  EXPECT_TRUE(SlurpFile(path) == "by value\n" ||
              ReportedError(f.diag.Diagnostics(), kLogForm, 5, "D.7"));
  std::filesystem::remove(path, ec);
}

}  // namespace
