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

// The path of a log file under the host's temporary directory, cleared of any
// copy an earlier run left, so what a test reads back is what its own run
// wrote. A test splices it into its source as the filename argument D.7 gives
// $log.
std::string FreshLogPath(const std::string& stem) {
  namespace fs = std::filesystem;
  fs::path path = fs::temp_directory_path() / ("deltahdl_annex_d_07_" + stem);
  std::error_code ec;
  fs::remove(path, ec);
  return path.string();
}

// Annex D.7: a log file mirrors all standard output, so logging is enabled to
// begin with -- before any $log or $nolog has run.
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

// Annex D.7: the $nolog task disables output to the log file.
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

// Annex D.7: the $log task reenables output that a preceding $nolog disabled.
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

// Annex D.7: a filename argument to $log closes the current log file and
// creates a new one, so the named file becomes the active log file.
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

// Annex D.7: the filename form of $log also reenables output, just as the bare
// form does, so output disabled by $nolog resumes to the newly named file.
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

// Annex D.7: each $log filename argument opens a fresh log file, so when
// several are issued the file named most recently is the active one.
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

// Annex D.7: $nolog only disables output to the log file; it does not close or
// rename the file. After a filename has been established, a $nolog leaves that
// name in place while turning output off.
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

// Annex D.7: only the filename form of $log opens a new file. A bare $log
// merely reenables output, so after a file has been named it keeps directing
// output to that same file rather than replacing it.
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

// Annex D.7: a bare $log with no argument names no file, so with no preceding
// filename argument the active log file remains unset.
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

// Annex D.7: the log file holds a copy of all the text printed to the standard
// output. Naming a file with $log opens it, and the text $display and $write
// then print to the standard output is copied there as printed -- the
// formatted values, the newline $display appends and the absence of one after
// $write -- while the standard output still receives it. Text put one
// character at a time reaches the same copy, since the stream is the tool's
// standard output however a caller writes to it.
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

// Annex D.7: $nolog disables output to the log file and $log reenables it. The
// text printed between the two is absent from the log file and present on the
// standard output, which the tasks say nothing about, and the text printed
// after the bare $log is copied again.
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

// Annex D.7: a file name argument to $log closes the old log file, creates a
// new one and directs output to it. The text printed before the second name
// stays in the first file alone and the text printed after it goes to the
// second file alone.
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

// Annex D.7: the copy is of all the text printed to the standard output, so
// text a §21.3 file output task prints there -- $fdisplay to the STDOUT
// descriptor of §21.3.1 and $fwrite to the multichannel descriptor whose bit 0
// is the standard output -- is copied too, and text the same tasks print to a
// file of their own is not.
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
