#include "fixture_simulator.h"

using namespace delta;

namespace {

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
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $log(\"run.log\");\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LogFile(), "run.log");
  EXPECT_TRUE(f.ctx.LoggingEnabled());
}

// Annex D.7: the filename form of $log also reenables output, just as the bare
// form does, so output disabled by $nolog resumes to the newly named file.
TEST(OptionalLogSim, LogFilenameReenablesOutput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $nolog;\n"
      "    $log(\"run.log\");\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), "run.log");
}

// Annex D.7: each $log filename argument opens a fresh log file, so when
// several are issued the file named most recently is the active one.
TEST(OptionalLogSim, MostRecentLogFileWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"first.log\");\n"
      "    $log(\"second.log\");\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LogFile(), "second.log");
}

// Annex D.7: $nolog only disables output to the log file; it does not close or
// rename the file. After a filename has been established, a $nolog leaves that
// name in place while turning output off.
TEST(OptionalLogSim, NologPreservesLogFile) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"run.log\");\n"
      "    $nolog;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), "run.log");
}

// Annex D.7: only the filename form of $log opens a new file. A bare $log
// merely reenables output, so after a file has been named it keeps directing
// output to that same file rather than replacing it.
TEST(OptionalLogSim, BareLogPreservesLogFile) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $log(\"run.log\");\n"
      "    $nolog;\n"
      "    $log;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.LoggingEnabled());
  EXPECT_EQ(f.ctx.LogFile(), "run.log");
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

}  // namespace
