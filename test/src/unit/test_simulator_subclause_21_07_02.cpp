#include <gtest/gtest.h>

#include <cstddef>
#include <ios>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_file_form.h"
#include "model_vcd_token_grammar.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class FourStateVcdFileFormat : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(src, {.scope = "t"});
  }
};

TEST_F(FourStateVcdFileFormat, DeclarationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    r = 3.5;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ExpectDeclarationCommandsStandApart(toks, 3);
  EXPECT_TRUE(HasLine(AllLines(content), "r3.5 \""));
}

TEST_F(FourStateVcdFileFormat, SimulationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
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

TEST_F(FourStateVcdFileFormat, ValueChangeCommandsSeparatedFromNeighbors) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
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

TEST_F(FourStateVcdFileFormat, WhitespaceTokenizationRecoversCommandStructure) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  const char* openers[] = {
      "$date",     "$version", "$timescale", "$scope",
      "$var",      "$upscope", "$comment",   "$enddefinitions",
      "$dumpvars", "$dumpall", "$dumpoff",   "$dumpon"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  EXPECT_EQ(CountToken(toks, "$end"), opened);
  for (size_t i = 0; i + 1 < toks.size(); ++i) {
    if (toks[i] == "$upscope" || toks[i] == "$enddefinitions") {
      EXPECT_EQ(toks[i + 1], "$end") << "after " << toks[i];
    }
  }
}

TEST_F(FourStateVcdFileFormat, DumperInsertedCommentIsSeparatedCommand) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h11;\n"
      "    #10 $dumplimit(1);\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  const char* openers[] = {
      "$date",     "$version", "$timescale", "$scope",
      "$var",      "$upscope", "$comment",   "$enddefinitions",
      "$dumpvars", "$dumpall", "$dumpoff",   "$dumpon"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  EXPECT_EQ(CountToken(toks, "$end"), opened);
}

TEST_F(FourStateVcdFileFormat, TaskBodyProducedCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
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

TEST_F(FourStateVcdFileFormat, FileIsPlainLineOrientedText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 a = 1'bx;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_EQ(content.back(), '\n');
  for (unsigned char c : content) {
    bool text = (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(text) << "non-text byte 0x" << std::hex << int{c};
  }
}

TEST_F(FourStateVcdFileFormat, WithoutWriterNoFileContentToFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
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

}  // namespace
}  // namespace delta
