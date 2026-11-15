#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_final_output.h"

using namespace delta;

namespace {

using Lines = std::vector<std::string>;
using Runs = std::vector<std::pair<std::string, std::string>>;

const char* const kSeen =
    "  final $display(\"seen %0d %0d %0d\", "
    "$rtoi(cg_1.%s.get_inst_coverage()),\n"
    "    $rtoi(cg_1.%s.get_inst_coverage()), "
    "$rtoi(cg_1.%s.get_inst_coverage()));\n";

std::string Seen(const Lines& points) {
  std::string text = kSeen;
  for (const auto& point : points) {
    size_t at = text.find("%s");
    text.replace(at, 2, point);
  }
  return text;
}

std::string Recorder(const std::string& item) {
  std::string text =
      "checker chk(logic clk, go, logic [3:0] op);\n"
      "  bit [3:0] op_d1 = 4'd0;\n"
      "  always_ff @(posedge clk) op_d1 <= op;\n"
      "  covergroup cg;\n"
      "    o0: coverpoint op_d1 { bins b = {4'd0}; }\n"
      "    o3: coverpoint op_d1 { bins b = {4'd3}; }\n"
      "    o5: coverpoint op_d1 { bins b = {4'd5}; }\n"
      "  endgroup\n"
      "  cg cg_1 = new();\n";
  text += item;
  text += Seen({"o0", "o3", "o5"});
  text += "endchecker\n";
  return text;
}

std::string Custom(const std::string& formal, const std::string& decls,
                   const std::string& arg) {
  std::string text = "checker chk(logic clk, go, logic [3:0] op);\n";
  text += decls;
  text += "  covergroup cg with function sample(bit [3:0] ";
  text += formal;
  text += ");\n";
  for (const char* value : {"0", "3", "6"}) {
    text += "    x";
    text += value;
    text += ": coverpoint ";
    text += formal;
    text += " { bins b = {4'd";
    text += value;
    text += "}; }\n";
  }
  text +=
      "  endgroup\n"
      "  cg cg_1 = new();\n"
      "  sequence s;\n"
      "    @(posedge clk) (go, cg_1.sample(";
  text += arg;
  text +=
      "));\n"
      "  endsequence\n"
      "  c1: cover property (s);\n";
  text += Seen({"x0", "x3", "x6"});
  text += "endchecker\n";
  return text;
}

const char* const kNamed =
    "  sequence s;\n"
    "    @(posedge clk) (go, cg_1.sample());\n"
    "  endsequence\n"
    "  c1: cover property (s);\n";

const char* const kStepped =
    "  initial begin\n"
    "    op = 4'd3;\n"
    "    #10 op = 4'd5;\n"
    "  end\n";

const char* const kAtEdge =
    "  initial op = 4'd0;\n"
    "  always @(posedge clk) op <= op + 4'd3;\n";

std::string Driven(const std::string& cu, const std::string& top) {
  std::string src = cu;
  src +=
      "module top;\n"
      "  logic clk = 0, go = 1;\n"
      "  logic [3:0] op;\n"
      "  always #5 clk = ~clk;\n"
      "  initial #17 go = 0;\n";
  src += top;
  src += "  initial #52 $finish;\nendmodule\n";
  return src;
}

void ExpectEach(const Runs& runs, const std::string& expected) {
  for (const auto& [label, src] : runs) {
    SCOPED_TRACE(label);
    SimFixture f;
    EXPECT_EQ(SortedOutput(src, f), (Lines{expected}));
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

Runs Places(const std::string& cu, const std::string& stimulus) {
  return {
      {"module", Driven(cu, stimulus + "  chk u(clk, go, op);\n")},
      {"checker", Driven(cu + "checker outer(logic clk, go, logic [3:0] op);\n"
                              "  chk u(clk, go, op);\n"
                              "endchecker\n",
                         stimulus + "  outer o(clk, go, op);\n")},
      {"interface",
       Driven(cu + "interface ifc(input logic clk, go, input logic [3:0] op);\n"
                   "  chk u(clk, go, op);\n"
                   "endinterface\n",
              stimulus + "  ifc i(clk, go, op);\n")},
      {"program",
       Driven(cu + "program prg(input logic clk, go, input logic [3:0] op);\n"
                   "  chk u(clk, go, op);\n"
                   "  initial #60;\n"
                   "endprogram\n",
              stimulus + "  prg p(clk, go, op);\n")},
      {"procedure",
       Driven(cu, stimulus + "  always @(posedge clk) chk u(clk, go, op);\n")},
  };
}

TEST(CheckerMatchItemSample, EachFormRecordsTheOldValueOncePerMatch) {
  Runs runs;
  for (const auto& [label, item] :
       Runs{{"named", kNamed},
            {"direct",
             "  c1: cover property (@(posedge clk) (go, cg_1.sample()) "
             "##0 1'b1);\n"},
            {"assert",
             "  a1: assert property (@(posedge clk) go |-> "
             "(1'b1, cg_1.sample()) ##0 1'b1);\n"},
            {"sequence",
             "  c1: cover sequence (@(posedge clk) (go, cg_1.sample()) ##0 "
             "1'b1);\n"}}) {
    runs.emplace_back(
        label, Driven(Recorder(item),
                      std::string(kStepped) + "  chk u(clk, go, op);\n"));
  }
  ExpectEach(runs, "seen 100 100 0");
}

TEST(CheckerMatchItemSample, ACheckerInEachPlaceRecordsTheOldValue) {
  ExpectEach(Places(Recorder(kNamed), kStepped), "seen 100 100 0");
}

TEST(CheckerCustomSample, EachArgumentIsPassedItsSampledValue) {
  Runs runs;
  for (const auto& [label, decls, arg, formal] : std::vector<
           std::tuple<std::string, std::string, std::string, std::string>>{
           {"assign", "  bit [3:0] ca;\n  assign ca = op;\n", "ca", "x"},
           {"always_comb", "  bit [3:0] cb;\n  always_comb cb = op;\n", "cb",
            "x"},
           {"formal", "", "op", "x"},
           {"shared name", "  bit [3:0] opcode_d1 = 4'd9;\n", "op",
            "opcode_d1"}}) {
    runs.emplace_back(label,
                      Driven(Custom(formal, decls, arg),
                             std::string(kAtEdge) + "  chk u(clk, go, op);\n"));
  }
  ExpectEach(runs, "seen 100 100 0");
}

TEST(CheckerCustomSample, ANonblockingWriteOfTheSameStepIsNotSeen) {
  ExpectEach(
      {{"always_ff", Driven(Custom("x",
                                   "  bit [3:0] d = 4'd0;\n"
                                   "  always_ff @(posedge clk) d <= op;\n",
                                   "d"),
                            std::string(kAtEdge) + "  chk u(clk, go, op);\n")}},
      "seen 100 0 0");
}

TEST(CheckerCustomSample, ACheckerInEachPlaceIsPassedTheSampledValue) {
  ExpectEach(Places(Custom("x", "", "op"), kAtEdge), "seen 100 100 0");
}

}  // namespace
