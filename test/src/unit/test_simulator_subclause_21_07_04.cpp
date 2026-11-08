#include <gtest/gtest.h>

#include <cstdio>
#include <ios>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_file_form.h"
#include "model_vcd_token_grammar.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class ExtendedVcdFileFormat : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src, bool close_file = false) {
    return RunVcdDump(src, {.scope = "t", .close_file = close_file});
  }
};

size_t CountSectionOpeners(const std::vector<std::string>& toks) {
  const char* openers[] = {
      "$date",    "$version", "$timescale",      "$scope",    "$var",
      "$upscope", "$comment", "$enddefinitions", "$dumpvars", "$dumpall",
      "$dumpoff", "$dumpon",  "$vcdclose"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  return opened;
}

TEST_F(ExtendedVcdFileFormat, DeclarationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    r = 3.5;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ExpectDeclarationCommandsStandApart(toks, 3);
  EXPECT_TRUE(HasLine(AllLines(content), "r3.5 \""));
}

TEST_F(ExtendedVcdFileFormat, SimulationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  ExpectSimulationTimesAreBareDecimals(toks);
  EXPECT_EQ(content.find("$end$"), std::string::npos);
  EXPECT_TRUE(NoFusedCommands(toks));
}

TEST_F(ExtendedVcdFileFormat, ValueChangeCommandsSeparatedFromNeighbors) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 begin a = 1'b1; v = 4'b1010; end\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b1010 \""));
  auto toks = Tokens(content);
  EXPECT_GE(CountToken(toks, "1!"), 1u);
}

TEST_F(ExtendedVcdFileFormat, WhitespaceTokenizationRecoversCommandStructure) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
  for (size_t i = 0; i + 1 < toks.size(); ++i) {
    if (toks[i] == "$upscope" || toks[i] == "$enddefinitions") {
      EXPECT_EQ(toks[i + 1], "$end") << "after " << toks[i];
    }
  }
}

TEST_F(ExtendedVcdFileFormat, DumperInsertedCommentIsSeparatedCommand) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 data = 8'h91;\n"
      "    #10 $dumpportslimit(1);\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
}

TEST_F(ExtendedVcdFileFormat, CloseCommandJoinsFileAsSeparatedSection) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      true);
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "final simulation time fused with another command: " << t;
    }
  }
}

TEST_F(ExtendedVcdFileFormat, TaskBodyProducedCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    start_dump;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
}

TEST_F(ExtendedVcdFileFormat, AlwaysProducedCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic go;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    go = 1'b0;\n"
      "    #5 go = 1'b1;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "  always @(posedge go) $dumpports(, \"dump2.dump\");\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_GE(CountToken(toks, "#15"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
}

std::vector<std::string> KeywordSequence(const std::vector<std::string>& toks) {
  std::vector<std::string> kws;
  for (const auto& t : toks) {
    if (t[0] == '$') kws.push_back(t);
  }
  return kws;
}

TEST_F(ExtendedVcdFileFormat, ExtendedFileSharesFourStateCommandStructure) {
  const char* body =
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "%s"
      "    #10 begin a = 1'b1; v = 4'b1010; end\n"
      "  end\n"
      "endmodule\n";
  auto src = [&](const char* dump_call) {
    char buf[512];
    snprintf(buf, sizeof(buf), body, dump_call);
    return std::string("module t;\n") + buf;
  };
  auto four_state =
      RunVcd(src("    $dumpfile(\"dump1.dump\");\n"
                 "    $dumpvars;\n"));
  auto extended = RunVcd(src("    $dumpports(, \"dump2.dump\");\n"));
  auto toks4 = Tokens(four_state);
  auto tokse = Tokens(extended);
  ASSERT_EQ(CountToken(toks4, "$var"), 2u);
  ASSERT_EQ(CountToken(tokse, "$var"), 2u);
  ASSERT_GE(CountToken(tokse, "$dumpvars"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks4));
  EXPECT_TRUE(NoFusedCommands(tokse));
  EXPECT_EQ(CountToken(toks4, "$end"), CountSectionOpeners(toks4));
  EXPECT_EQ(CountToken(tokse, "$end"), CountSectionOpeners(tokse));
  EXPECT_EQ(KeywordSequence(tokse), KeywordSequence(toks4));
}

TEST_F(ExtendedVcdFileFormat, RealValueCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  real r = 3.5;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 1.25;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "r3.5 \""));
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "r1.25 \""));
  EXPECT_TRUE(NoFusedCommands(Tokens(content)));
}

TEST_F(ExtendedVcdFileFormat, FileIsPlainLineOrientedText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic [7:0] v = 8'h00;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 a = 1'bx;\n"
      "    #10 a = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("b10xz01zx \""), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("z!"), std::string::npos);
  EXPECT_EQ(content.back(), '\n');
  for (unsigned char c : content) {
    bool text = (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(text) << "non-text byte 0x" << std::hex << int{c};
  }
}

TEST_F(ExtendedVcdFileFormat, WithoutWriterNoFileContentToFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(ReadVcd().empty());
}

class ExtendedVcdFormatChosenByTheSource : public VcdDumpFromSourceTestBase {
 protected:
  static std::string DesignCalling(const std::string& tasks) {
    return "module t;\n"
           "  logic [3:0] bus;\n"
           "  logic clk;\n"
           "  initial begin\n"
           "    bus = 4'b0000;\n"
           "    clk = 1'b0;\n" +
           tasks +
           "    #10 clk = 1'b1;\n"
           "    #10 bus = 4'b1010;\n"
           "  end\n"
           "endmodule\n";
  }
};

std::string PortValueChangeRecord(const std::string& line) {
  if (line.empty() || line[0] != 'p') return "";
  auto space = line.find(' ');
  if (space == std::string::npos || space < 4U) return "";
  if (line.compare(space + 1, 1, "<") != 0) return "";
  return line.substr(0, space - 2) + line.substr(space);
}

std::string PortValueChanges(const std::string& content) {
  std::string joined;
  for (const auto& line : Lines(content)) {
    auto record = PortValueChangeRecord(line);
    if (record.empty()) continue;
    if (!joined.empty()) joined += ' ';
    joined += record;
  }
  return joined;
}

TEST_F(ExtendedVcdFormatChosenByTheSource,
       DumpportsWritesPortNodesAndPortValues) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n"));

  auto content = DumpFile("portdump.vcd");
  EXPECT_NE(content.find("$var port [3:0] <0 bus $end"), std::string::npos);
  EXPECT_NE(content.find("$var port 1 <1 clk $end"), std::string::npos);
  auto changes = PortValueChanges(content);
  EXPECT_NE(changes.find("p0000 <0"), std::string::npos);
  EXPECT_NE(changes.find("p1010 <0"), std::string::npos);
  EXPECT_NE(changes.find("p0 <1"), std::string::npos);
  EXPECT_NE(changes.find("p1 <1"), std::string::npos);
}

TEST_F(ExtendedVcdFormatChosenByTheSource,
       DumpvarsWritesNeitherPortNodesNorPortValues) {
  RunSource(
      DesignCalling("    $dumpfile(\"vardump.vcd\");\n"
                    "    $dumpvars;\n"));

  auto content = DumpFile("vardump.vcd");
  EXPECT_NE(content.find("$var reg 4 ! bus $end"), std::string::npos);
  EXPECT_TRUE(HasLine(Lines(content), "$dumpvars"));
  EXPECT_EQ(content.find("$var port"), std::string::npos);
  EXPECT_EQ(PortValueChanges(content), "");
}

TEST_F(ExtendedVcdFormatChosenByTheSource,
       DumpportsKeysItsCheckpointWithTheExtendedKeyword) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n"));

  auto lines = Lines(DumpFile("portdump.vcd"));
  EXPECT_TRUE(HasLine(lines, "$dumpports"));
  EXPECT_FALSE(HasLine(lines, "$dumpvars"));
}

}  // namespace
}  // namespace delta
