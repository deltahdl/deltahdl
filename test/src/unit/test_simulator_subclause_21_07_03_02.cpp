#include <gtest/gtest.h>

#include <string>

#include "fixture_extended_vcd_from_source.h"
#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_dump.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpportsOffOnSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t"});
  }
};

TEST_F(DumpportsOffOnSysTask, DumpportsoffWritesAllXCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [3:0] b;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    b = 4'b1010;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("bx \""), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsoffStopsDumpingFromThatTimeForward) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);
  EXPECT_EQ(content.find("#20"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsoffNoFilenameSuspendsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, SuspendCheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpoff"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsonResumesWithCurrentValues) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #5 d = 8'h3C;\n"
                        "    #5 $dumpportson(\"p.dump\");\n"
                        "    #10 d = 8'hFF;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("b111100 !"), std::string::npos);
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("b11111111 !"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, ResumeCheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#20\n$dumpon"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsonNoFilenameResumesAllStoppedFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 $dumpportson;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsoffIgnoredWhenAlreadySuspended) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 1u);
}

TEST_F(DumpportsOffOnSysTask, DumpportsonIgnoredWhenAlreadyDumping) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, NoFilenameResumeIgnoredWhenNothingStopped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportson;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, ResumeFilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, ResumeFilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, NoFilenameSuspendIgnoredWhenAlreadySuspended) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 $dumpportsoff;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 1u);
}

TEST_F(DumpportsOffOnSysTask, DumpportsoffUnknownFilenameLeavesDumpRunning) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, UnknownFilenameInVariableLeavesDumpRunning) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"other.vcd\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsOffOnSysTask, DumpportsonUnknownFilenameResumesNothing) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

class DumpportsOffOn : public ExtendedVcdFromSource {};

TEST_F(DumpportsOffOn, DISABLED_OffWritesUnknownPortRecordsThenNothing) {
  auto content =
      Run("    $dumpports(u, \"one.vcd\");\n"
          "    #1 $dumpportsoff(\"one.vcd\");\n"
          "    #1 a = 1'b1;\n"
          "    #1;\n");
  auto off = Section(content, "$dumpportsoff");
  EXPECT_EQ(StatesFor(off, PortCode(content, "u", "a")), "N") << content;
  EXPECT_EQ(StatesFor(off, PortCode(content, "u", "b")), "X") << content;
  EXPECT_EQ(off.find("\nx"), std::string::npos) << content;
  auto rest = content.substr(content.find("$end", content.find(off)));
  EXPECT_EQ(StatesFor(rest, PortCode(content, "u", "a")), "") << content;
}

TEST_F(DumpportsOffOn, OnWritesEachPortsCurrentValue) {
  auto content =
      Run("    $dumpports(u, \"one.vcd\");\n"
          "    #1 $dumpportsoff(\"one.vcd\");\n"
          "    #1 a = 1'b1;\n"
          "    #1 $dumpportson(\"one.vcd\");\n"
          "    #1;\n");
  auto on = Section(content, "$dumpportson");
  EXPECT_EQ(StatesFor(on, PortCode(content, "u", "a")), "U") << content;
  EXPECT_EQ(StatesFor(on, PortCode(content, "u", "b")), "H") << content;
}

TEST_F(DumpportsOffOn, DISABLED_WithNoFilenameEveryFileIsSuspendedAndResumed) {
  auto one =
      Run("    $dumpports(u, \"one.vcd\");\n"
          "    $dumpports(v, \"two.vcd\");\n"
          "    #1 $dumpportsoff;\n"
          "    #1 c = 1'b1;\n"
          "    #1 $dumpportson;\n"
          "    #1;\n");
  auto two = DumpFile("two.vcd");
  for (const auto& content : {one, two}) {
    EXPECT_EQ(CountSections(content, "$dumpportsoff"), 1u) << content;
    EXPECT_EQ(CountSections(content, "$dumpportson"), 1u) << content;
  }
  EXPECT_EQ(StatesFor(Section(two, "$dumpportsoff"), PortCode(two, "v", "c")),
            "N")
      << two;
  EXPECT_EQ(StatesFor(Section(two, "$dumpportson"), PortCode(two, "v", "c")),
            "U")
      << two;
}

TEST_F(DumpportsOffOn, RepeatedOffAndOnWriteOneSectionEach) {
  auto content =
      Run("    $dumpports(u, \"one.vcd\");\n"
          "    #1 $dumpportsoff;\n"
          "    #1 $dumpportsoff;\n"
          "    #1 $dumpportson;\n"
          "    #1 $dumpportson;\n"
          "    #1;\n");
  EXPECT_EQ(CountSections(content, "$dumpportsoff"), 1u) << content;
  EXPECT_EQ(CountSections(content, "$dumpportson"), 1u) << content;
}

}  // namespace
}  // namespace delta
