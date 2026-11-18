#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

std::set<std::string> VariableNames(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  auto* design = Elaborate(src, f);
  EXPECT_FALSE(f.has_errors);
  if (design == nullptr) return {};
  std::set<std::string> names;
  for (const auto& v : design->top_modules[0]->variables) {
    names.insert(std::string(v.name));
  }
  return names;
}

std::string SeverityBlock(const std::string& element, const std::string& body) {
  std::string src = element;
  src += " e;\n";
  src += body;
  src += "end";
  src += element;
  src += "\nmodule top;\n  e u();\nendmodule\n";
  SCOPED_TRACE(src);
  ElabFixture f;
  auto* design = Elaborate(src, f);
  if (design == nullptr) return "";
  const std::string& scope = design->last_elab_severity_scope;
  return scope.substr(scope.rfind('.') + 1);
}

constexpr const char* kSecondBlock = "  if (1) begin logic b; end\n";

TEST(GenerateConstructNumbering, TheCountRunsOnAcrossGenerateRegions) {
  EXPECT_EQ(VariableNames("module top;\n"
                          "  generate if (1) begin logic a; end endgenerate\n"
                          "  generate if (1) begin logic b; end endgenerate\n"
                          "  if (1) begin logic c; end\n"
                          "endmodule\n"),
            (std::set<std::string>{"genblk1_a", "genblk2_b", "genblk3_c"}));
}

TEST(GenerateConstructNumbering, AConstructBuildingNoBlockTakesItsNumber) {
  for (const std::string& first :
       {"  if (0) begin logic a; end\n",
        "  for (genvar i = 0; i < 0; i++) begin logic a; end\n",
        "  case (2) 1: begin logic a; end endcase\n",
        "  if (0) begin : n logic a; end\n"}) {
    std::string src = "module top;\n";
    src += first;
    src += kSecondBlock;
    src += "endmodule\n";
    EXPECT_EQ(VariableNames(src), (std::set<std::string>{"genblk2_b"}));
  }
}

TEST(GenerateConstructNumbering, NumberingRestartsInsideAnUnnamedBlock) {
  EXPECT_EQ(
      VariableNames("module top;\n"
                    "  if (1) begin if (1) begin logic a; end end\n"
                    "  for (genvar i = 0; i < 1; i++) if (1) logic b;\n"
                    "endmodule\n"),
      (std::set<std::string>{"genblk1_genblk1_a", "genblk2_0_genblk1_b"}));
}

TEST(GenerateConstructNumbering, TheClausesExampleNamesEachBlock) {
  EXPECT_EQ(VariableNames("module top;\n"
                          "  parameter genblk2 = 0;\n"
                          "  genvar i;\n"
                          "  if (genblk2) logic a;\n"
                          "  else logic b;\n"
                          "  if (genblk2) logic a;\n"
                          "  else logic b;\n"
                          "  for (i = 0; i < 1; i = i + 1) begin : g1\n"
                          "    if (1) logic a;\n"
                          "  end\n"
                          "  for (i = 0; i < 1; i = i + 1)\n"
                          "    if (1) logic a;\n"
                          "  if (1) logic a;\n"
                          "endmodule\n"),
            (std::set<std::string>{"genblk1_b", "genblk02_b", "g1_0_genblk1_a",
                                   "genblk4_0_genblk1_a", "genblk5_a"}));
}

TEST(GenerateConstructNumbering, ALoopWithABareItemNamesEachIteration) {
  EXPECT_EQ(VariableNames("module top;\n"
                          "  for (genvar i = 0; i < 2; i++) logic a;\n"
                          "endmodule\n"),
            (std::set<std::string>{"genblk1_0_a", "genblk1_1_a"}));
}

TEST(GenerateConstructNumbering, EachElementNumbersItsConstructs) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    EXPECT_EQ(SeverityBlock(element,
                            "  if (0) begin end\n"
                            "  if (1) begin $info(\"x\"); end\n"),
              "genblk2")
        << element;
  }
}

TEST(GenerateBlockLeadingZeros, EachKindOfDeclarationTakesLeadingZeros) {
  for (const std::string& decl :
       {"  wire genblk1;\n", "  genvar genblk1;\n",
        "  localparam genblk1 = 0;\n", "  typedef int genblk1;\n",
        "  task genblk1; endtask\n",
        "  function int genblk1; return 0; endfunction\n"}) {
    std::string src = "module top;\n";
    src += decl;
    src += "  if (1) begin logic a; end\n";
    src += "endmodule\n";
    EXPECT_TRUE(VariableNames(src).contains("genblk01_a")) << decl;
  }
  EXPECT_TRUE(VariableNames("module top (input logic genblk1);\n"
                            "  if (1) begin logic a; end\n"
                            "endmodule\n")
                  .contains("genblk01_a"));
}

TEST(GenerateBlockLeadingZeros, DISABLED_AnInstanceNameTakesLeadingZeros) {
  for (const std::string& inst : {"  s genblk1();\n", "  i genblk1();\n"}) {
    std::string src =
        "module s; endmodule\n"
        "interface i; endinterface\n"
        "module top;\n";
    src += inst;
    src += "  if (1) begin logic a; end\n";
    src += "endmodule\n";
    EXPECT_TRUE(VariableNames(src).contains("genblk01_a")) << inst;
  }
}

TEST(GenerateBlockLeadingZeros, ANamedBlockTakesLeadingZeros) {
  EXPECT_EQ(VariableNames("module top;\n"
                          "  if (1) begin : genblk2 logic a; end\n"
                          "  if (1) begin logic b; end\n"
                          "endmodule\n"),
            (std::set<std::string>{"genblk2_a", "genblk02_b"}));
}

TEST(GenerateBlockLeadingZeros, ALaterDeclarationTakesLeadingZeros) {
  EXPECT_TRUE(VariableNames("module top;\n"
                            "  if (1) begin logic a; end\n"
                            "  logic genblk1;\n"
                            "endmodule\n")
                  .contains("genblk01_a"));
}

TEST(GenerateBlockLeadingZeros, ANameNoDeclarationTakesKeepsNoZero) {
  EXPECT_EQ(VariableNames("module top;\n"
                          "  logic genblk2;\n"
                          "  if (1) begin logic a; end\n"
                          "endmodule\n"),
            (std::set<std::string>{"genblk2", "genblk1_a"}));
}

TEST(GenerateBlockLeadingZeros, AClashInsideANestedScope) {
  EXPECT_TRUE(VariableNames("module top;\n"
                            "  for (genvar i = 0; i < 1; i++) begin : g\n"
                            "    int genblk1;\n"
                            "    if (1) begin logic a; end\n"
                            "  end\n"
                            "endmodule\n")
                  .contains("g_0_genblk01_a"));
  EXPECT_TRUE(VariableNames("module top;\n"
                            "  if (1) begin\n"
                            "    int genblk1;\n"
                            "    if (1) begin logic a; end\n"
                            "  end\n"
                            "endmodule\n")
                  .contains("genblk1_genblk01_a"));
}

TEST(GenerateBlockLeadingZeros, EachElementAddsLeadingZeros) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    EXPECT_EQ(SeverityBlock(element,
                            "  logic genblk1;\n"
                            "  if (1) begin $info(\"x\"); end\n"),
              "genblk01")
        << element;
  }
}

}  // namespace
