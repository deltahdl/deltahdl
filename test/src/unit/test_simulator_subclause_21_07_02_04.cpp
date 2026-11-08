#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class FourStateVcdExampleE2E : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(
        src, {.scope = "t",
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

std::string Section(const std::string& content, std::string_view keyword) {
  auto start = content.find(keyword);
  if (start == std::string::npos) return {};
  auto end = content.find("$end", start);
  if (end == std::string::npos) return content.substr(start);
  return content.substr(start, end - start);
}

std::string Between(const std::string& content, std::string_view a,
                    std::string_view b) {
  auto pa = content.find(a);
  if (pa == std::string::npos) return "<bound-missing>";
  auto from = pa + a.size();
  auto pb = content.find(b, from);
  if (pb == std::string::npos) return "<bound-missing>";
  return content.substr(from, pb - from);
}

size_t CountOccurrences(const std::string& content, std::string_view needle) {
  size_t n = 0;
  for (auto pos = content.find(needle); pos != std::string::npos;
       pos = content.find(needle, pos + needle.size())) {
    ++n;
  }
  return n;
}

TEST_F(FourStateVcdExampleE2E, FileSectionsFollowExampleProgression) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin a = 1'b0; acc = 32'h1e; end\n"
      "  end\n"
      "endmodule\n");
  size_t last = 0;
  for (const char* mark :
       {"$date", "$version", "$timescale", "$scope", "$var", "$upscope",
        "$enddefinitions", "#500", "$dumpvars"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " out of order\n" << content;
    last = pos + std::strlen(mark);
  }
  EXPECT_EQ(content.find('#'), content.find("#500")) << content;
}

TEST_F(FourStateVcdExampleE2E, DumpvarsSectionFollowsItsTimeMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin a = 1'b0; acc = 32'h1e; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(Between(content, "$enddefinitions $end\n", "#500"), "") << content;
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("x!"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("bx \""), std::string::npos) << dumpvars;
  EXPECT_EQ(CountOccurrences(dumpvars, "!"), 1u) << dumpvars;
  EXPECT_NE(content.find("#505"), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, ThirtyTwoBitFormsAndPreDumpValuesFromSource) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [31:0] acc;\n"
      "  integer idx;\n"
      "  initial begin\n"
      "    acc = 32'h1e;\n"
      "    idx = 5;\n"
      "    #500 $dumpvars;\n"
      "    #5 idx = 6;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("32 ! acc $end"), std::string::npos) << content;
  EXPECT_NE(content.find("32 \" idx $end"), std::string::npos) << content;
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("b11110 !"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("b101 \""), std::string::npos) << dumpvars;
  EXPECT_EQ(dumpvars.find("bx"), std::string::npos) << dumpvars;
  EXPECT_EQ(content.find('#'), content.find("#500")) << content;
  EXPECT_NE(content.find("#505\nb110 \""), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, InitializerValueListsInDelayedCheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v = 8'h05;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    #500 $dumpvars;\n"
      "    #5 s = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("0!"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("b101 \""), std::string::npos) << dumpvars;
  EXPECT_EQ(dumpvars.find("bx"), std::string::npos) << dumpvars;
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
  EXPECT_NE(content.find("#505\n1!"), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, ContinuousAssignDrivenNetJoinsChangedGroups) {
  auto content = RunVcd(
      "module t;\n"
      "  logic d;\n"
      "  wire w;\n"
      "  assign w = d;\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 d = 1'b1;\n"
      "    #10 d = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto at10 = Between(content, "#10\n", "#20");
  EXPECT_NE(at10.find("1\""), std::string::npos) << content;
  auto from20 = content.substr(content.find("#20"));
  EXPECT_NE(from20.find("0\""), std::string::npos) << from20;
  EXPECT_EQ(CountOccurrences(content, "1\""), 1u) << content;
}

TEST_F(FourStateVcdExampleE2E, TaskBodyInvokedDumpallFollowsItsMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task checkpoint_now;\n"
      "    $dumpall;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 checkpoint_now;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
}

TEST_F(FourStateVcdExampleE2E, NbaProducedChangesListInTheirOwnGroupOnly) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 s <= 1'b1;\n"
      "    #10 v <= 8'h22;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(Between(content, "#10\n", "#20"), "1!\n") << content;
  auto from20 = content.find("#20");
  ASSERT_NE(from20, std::string::npos) << content;
  auto after20 = content.substr(from20);
  EXPECT_NE(after20.find("b100010 \""), std::string::npos) << after20;
  EXPECT_EQ(after20.find("1!"), std::string::npos) << after20;
}

TEST_F(FourStateVcdExampleE2E, LaterTimeUnitsListOnlyChangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic n1, n2, n3;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin n1 = 0; n2 = 1; n3 = 1; acc = 32'h1e; end\n"
      "    #5 n3 = 0;\n"
      "    #10 n3 = 1;\n"
      "    #10 n3 = 0;\n"
      "  end\n"
      "endmodule\n");
  auto at505 = Between(content, "#505\n", "#510");
  EXPECT_NE(at505.find("0\""), std::string::npos) << at505;
  EXPECT_NE(at505.find("1#"), std::string::npos) << at505;
  EXPECT_NE(at505.find("1$"), std::string::npos) << at505;
  EXPECT_NE(at505.find("b11110 !"), std::string::npos) << at505;
  EXPECT_EQ(Between(content, "#510\n", "#520"), "0$\n") << content;
  EXPECT_EQ(Between(content, "#520\n", "#530"), "1$\n") << content;
}

TEST_F(FourStateVcdExampleE2E, DumpallCheckpointFollowsItsOwnTimeMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] moving;\n"
      "  logic [7:0] steady;\n"
      "  initial begin\n"
      "    moving = 8'h11; steady = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 moving = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  EXPECT_EQ(Between(content, "#10\n", "#20"), "b100010 !\n") << content;
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
  EXPECT_NE(dumpall.find("b10100101 \""), std::string::npos) << dumpall;
}

TEST_F(FourStateVcdExampleE2E, SameTimeChangeAndDumpallShareOneMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #20 begin data = 8'h22; $dumpall; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  EXPECT_EQ(CountOccurrences(content, "b100010 !"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
}

TEST_F(FourStateVcdExampleE2E, DumpoffFollowsItsMarkerAndSilencesTheWindow) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 v = 8'h33;\n"
      "    #10 $dumpon;\n"
      "    #10 v = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpoff\n"), std::string::npos) << content;
  auto dumpoff = Section(content, "$dumpoff");
  EXPECT_NE(dumpoff.find("x!"), std::string::npos) << dumpoff;
  EXPECT_NE(dumpoff.find("bx \""), std::string::npos) << dumpoff;
  EXPECT_EQ(content.find("#30"), std::string::npos) << content;
  EXPECT_EQ(Between(content, "$dumpoff\nx!\nbx \"\n$end\n", "#40"), "")
      << content;
}

TEST_F(FourStateVcdExampleE2E, DumponFollowsItsMarkerAndResumesRecording) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 v = 8'h33;\n"
      "    #10 $dumpon;\n"
      "    #10 v = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#40\n$dumpon\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#40\n"), 1u) << content;
  auto dumpon = Section(content, "$dumpon");
  EXPECT_NE(dumpon.find("0!"), std::string::npos) << dumpon;
  EXPECT_NE(dumpon.find("b110011 \""), std::string::npos) << dumpon;
  EXPECT_EQ(CountOccurrences(content, "b110011 \""), 1u) << content;
  EXPECT_NE(content.find("#50\nb1000100 \""), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, SuppressedDumpallLeavesNoOrphanTimeMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("$dumpall"), std::string::npos) << content;
  EXPECT_EQ(content.find("#20"), std::string::npos) << content;
  EXPECT_NE(content.find("#30\n$dumpon\n"), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, IntegratedExampleReplaysInOrder) {
  auto content = RunVcd(
      "module t;\n"
      "  logic n1, n2, n3;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin n1 = 0; n2 = 1; n3 = 1; acc = 32'h1e; end\n"
      "    #5 n3 = 0;\n"
      "    #10 n3 = 1;\n"
      "    #10 n3 = 0;\n"
      "    #5 $dumpall;\n"
      "    #5 n3 = 1;\n"
      "    #460 $dumpoff;\n"
      "    #500 n2 = 0;\n"
      "    #500 $dumpon;\n"
      "    #10 n3 = 0;\n"
      "  end\n"
      "endmodule\n");
  size_t last = 0;
  for (const char* mark : {"$enddefinitions", "#500", "$dumpvars", "#505",
                           "#510", "#520", "#530", "#535", "$dumpall", "#540",
                           "#1000", "$dumpoff", "#2000", "$dumpon", "#2010"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos);
  EXPECT_NE(content.find("#535\n$dumpall\n"), std::string::npos);
  EXPECT_NE(content.find("#1000\n$dumpoff\n"), std::string::npos);
  EXPECT_NE(content.find("#2000\n$dumpon\n"), std::string::npos);
  EXPECT_EQ(content.find("#1500"), std::string::npos) << content;
  auto dumpon = Section(content, "$dumpon");
  EXPECT_NE(dumpon.find("0#"), std::string::npos) << dumpon;
  EXPECT_NE(content.find("#2010\n0$"), std::string::npos) << content;
}

TEST_F(FourStateVcdExampleE2E, NestedAndSiblingScopesComposeDefinitions) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    vcd.BeginScope("m1");
    vcd.RegisterSignal("net1", 1, nullptr);
    vcd.RegisterSignal("net2", 1, nullptr);
    vcd.RegisterSignal("net3", 1, nullptr);
    vcd.EndScope();
    vcd.BeginScope("t1", VcdScopeKind::kTask);
    VcdSignalSpec acc;
    acc.name = "accumulator";
    acc.width = 32;
    acc.data_type = VcdDataType::kLogic;
    vcd.RegisterSignal(acc);
    VcdSignalSpec idx;
    idx.name = "index";
    idx.width = 32;
    idx.data_type = VcdDataType::kInt;
    vcd.RegisterSignal(idx);
    vcd.EndScope();
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  size_t last = 0;
  for (const char* mark :
       {"$scope module top $end", "$scope module m1 $end", "net1", "net2",
        "net3", "$upscope $end", "$scope task t1 $end",
        "$var reg 32 $ accumulator $end", "$var integer 32 % index $end",
        "$upscope $end", "$upscope $end", "$enddefinitions $end"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  EXPECT_EQ(CountOccurrences(content, "$scope "), 3u);
  EXPECT_EQ(CountOccurrences(content, "$upscope $end"), 3u);
  EXPECT_EQ(Between(content, "$scope module top $end\n", "$scope module m1"),
            "")
      << content;
}

TEST_F(FourStateVcdExampleE2E, CommentMaySitBetweenDefinitionsAndFirstTime) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 0);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    vcd.RegisterSignal("a", 1, a);
    vcd.EndScope();
    vcd.EndDefinitions();
    vcd.WriteComment("values dumped from time 500 onward");
    vcd.ArmDumpvarsStart();
    vcd.DumpAllValues(500);
  }
  auto content = ReadVcd();
  size_t last = 0;
  for (const char* mark : {"$enddefinitions $end", "$comment",
                           "values dumped from time 500 onward", "$end", "#500",
                           "$dumpvars", "0!", "$end"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
}

}  // namespace
}  // namespace delta
