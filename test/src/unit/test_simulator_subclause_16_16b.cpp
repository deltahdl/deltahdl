#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_clock_resolution_runs.h"
#include "helpers_report_times.h"

using namespace delta;

namespace {

std::string Failing(const std::string& label, const std::string& property,
                    const char* kind = "assert") {
  return "  " + label + ": " + kind + " property (" + property +
         ") else $display(\"" + label + " at %0d\", $time);\n";
}

std::string Covering(const std::string& label, const std::string& spec,
                     const char* kind = "cover property") {
  return "  " + label + ": " + kind + " (" + spec + ") $display(\"" + label +
         " at %0d\", $time);\n";
}

TEST(DefaultClockLeadingRun, AnAssumeOrACoverSequenceTakesTheDefault) {
  std::string out = RunClockResolutionDesign(
      "module m(input logic a, b, clk);\n"
      "  default clocking dc @(negedge clk); endclocking\n"
      "  sequence s; a ##1 b; endsequence\n" +
      Failing("u1", "a |=> !b", "assume") +
      Covering("c1", "a ##1 b", "cover sequence") +
      Covering("c2", "s", "cover sequence") + "endmodule\n");
  EXPECT_EQ(ReportTimes(out, "u1"), "30");
  EXPECT_EQ(ReportTimes(out, "c1"), "30");
  EXPECT_EQ(ReportTimes(out, "c2"), "30");
}

TEST(DefaultClockLeadingRun, AnInterfacesOrProgramsDefaultLeadsItsAssertion) {
  std::string out = RunClockResolutionDesign(
      "interface ifc(input logic a, b, clk);\n"
      "  default clocking dc @(negedge clk); endclocking\n" +
          Failing("i1", "a |=> !b") +
          "endinterface\n"
          "program prg(input logic a, b, clk);\n"
          "  default clocking dc @(negedge clk); endclocking\n" +
          Failing("p1", "a |=> !b") + "endprogram\n",
      "  ifc ui(a, b, clk);\n"
      "  prg up(a, b, clk);\n");
  EXPECT_EQ(ReportTimes(out, "i1"), "30");
  EXPECT_EQ(ReportTimes(out, "p1"), "30");
}

TEST(DefaultClockLeadingRun, AGenerateBlocksOwnDefaultLeadsItsAssertion) {
  std::string out = RunClockResolutionDesign(
      "module m(input logic a, b, clk);\n" +
      Failing("m1", "@(posedge clk) a |=> !b") +
      "  if (1) begin : g\n"
      "    default clocking gc @(negedge clk); endclocking\n  " +
      Failing("g1", "a |=> !b") +
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ReportTimes(out, "m1"), "25");
  EXPECT_EQ(ReportTimes(out, "g1"), "30");
}

TEST(DefaultClockLeadingRun, ANestedModuleTakesTheEnclosingDefault) {
  std::string out = RunClockResolutionDesign(
      "module m(input logic a, b, clk);\n"
      "  default clocking dc @(negedge clk); endclocking\n"
      "  module n;\n  " +
      Failing("n1", "a |=> !b") +
      "  endmodule\n"
      "endmodule\n");
  EXPECT_EQ(ReportTimes(out, "n1"), "30");
}

TEST(DefaultClockLeadingRun, ADefaultGivenByNameLeads) {
  std::string out = RunClockResolutionDesign(
      "module m(input logic a, b, clk);\n"
      "  clocking cb @(negedge clk); endclocking\n"
      "  default clocking cb;\n" +
      Failing("d1", "a |=> !b") + "endmodule\n");
  EXPECT_EQ(ReportTimes(out, "d1"), "30");
}

std::string Pairs(const std::string& prefix,
                  const std::vector<std::string>& exprs,
                  const char* kind = "assert property") {
  std::string items;
  for (size_t i = 0; i < exprs.size(); ++i) {
    std::string tag = prefix + std::to_string(i);
    for (const char* side : {"i", "e"}) {
      std::string label = tag + side;
      std::string spec =
          side[0] == 'i' ? exprs[i] : "@(posedge clk) " + exprs[i];
      items.append("  ").append(label).append(": ").append(kind);
      items.append(" (").append(spec).append(")");
      items += std::string(kind).rfind("cover", 0) == 0 ? " " : " else ";
      items.append("$display(\"").append(label);
      items.append(" at %0d\", $time);\n");
    }
  }
  return items;
}

void ExpectPairsAgree(const std::string& out, const std::string& prefix,
                      size_t count) {
  for (size_t i = 0; i < count; ++i) {
    std::string tag = prefix + std::to_string(i);
    std::string written = ReportTimes(out, tag + "e");
    EXPECT_EQ(ReportTimes(out, tag + "i"), written) << tag;
    EXPECT_NE(written, "") << tag;
    EXPECT_NE(written, "5 15 25 35") << tag;
  }
}

constexpr const char* kMembers =
    "  typedef struct packed { logic f; logic [1:0] g; } ps_t;\n"
    "  typedef struct packed { ps_t n; } nest_t;\n"
    "  ps_t s;\n"
    "  nest_t s2;\n"
    "  struct { logic f; } us;\n"
    "  union packed { logic f; logic g; } un;\n"
    "  assign s.f = a;\n"
    "  assign s.g = {a, a};\n"
    "  assign s2.n.f = a;\n"
    "  assign s2.n.g = {a, 1'b0};\n"
    "  assign us.f = a;\n"
    "  assign un.f = a;\n";

constexpr const char* kPosedgeDefault =
    "  default clocking dc @(posedge clk); endclocking\n";

constexpr const char* kClockingBlock =
    "  clocking cb @(posedge clk); input a; endclocking\n";

void ExpectDefaultClocked(
    const std::string& head, const std::vector<std::string>& operands,
    const char* kind = "assert property",
    const std::string& tail = "endmodule\n",
    const std::string& instances = "  m u1(a, b, clk);\n") {
  std::string out = RunClockResolutionDesign(
      head + Pairs("p", operands, kind) + tail, instances);
  ExpectPairsAgree(out, "p", operands.size());
}

std::string ModuleHead(const std::string& declarations) {
  return "module m(input logic a, b, clk);\n" + declarations;
}

TEST(DefaultClockedMemberRun, DISABLED_AStructOrUnionMemberAsTheWholeProperty) {
  ExpectDefaultClocked(ModuleHead(std::string(kPosedgeDefault) + kMembers),
                       {"s.f", "us.f", "un.f"});
}

TEST(DefaultClockedMemberRun, AnExpressionOverAMemberAsTheWholeProperty) {
  ExpectDefaultClocked(ModuleHead(std::string(kPosedgeDefault) + kMembers),
                       {"!s.f", "s2.n.f", "s2.n.g[1]"});
}

TEST(DefaultClockedMemberRun, AnInstancesVariableByHierarchicalName) {
  ExpectDefaultClocked(
      "module sub(input logic a);\n  logic x;\n  assign x = a;\nendmodule\n" +
          ModuleHead(std::string(kPosedgeDefault) + "  sub u(a);\n"),
      {"u.x"});
}

constexpr const char* kBus =
    "interface bus(input logic clk, a);\n"
    "  typedef struct packed { logic f; logic g; } ps_t;\n"
    "  ps_t s;\n"
    "  logic x;\n"
    "  always_comb begin s.f = a; s.g = a; x = a; end\n"
    "  clocking cb @(posedge clk); input a; endclocking\n"
    "endinterface\n";

TEST(DefaultClockedMemberRun, DISABLED_AMemberReadThroughAnInterfacePort) {
  ExpectDefaultClocked(std::string(kBus) +
                           "module m(bus ip, input logic clk);\n" +
                           kPosedgeDefault,
                       {"ip.s.f"}, "assert property", "endmodule\n",
                       "  bus ub(clk, a);\n  m u1(ub, clk);\n");
}

TEST(DefaultClockedMemberRun, APlainOrClockingSignalReadThroughAPort) {
  ExpectDefaultClocked(std::string(kBus) +
                           "module m(bus ip, input logic clk);\n" +
                           kPosedgeDefault,
                       {"ip.x", "ip.cb.a"}, "assert property", "endmodule\n",
                       "  bus ub(clk, a);\n  m u1(ub, clk);\n");
}

TEST(DefaultClockedMemberRun, DISABLED_AClockingBlockInputAsTheWholeProperty) {
  ExpectDefaultClocked(
      ModuleHead(std::string(kPosedgeDefault) + kClockingBlock), {"cb.a"});
  ExpectDefaultClocked(
      ModuleHead(
          "  default clocking cb @(posedge clk); input a; endclocking\n"),
      {"cb.a"});
  ExpectDefaultClocked(
      ModuleHead(std::string(kClockingBlock) + "  default clocking cb;\n"),
      {"cb.a"});
  ExpectDefaultClocked(
      ModuleHead(std::string(kPosedgeDefault) +
                 "  logic v;\n  always_comb v = a;\n"
                 "  clocking cb @(posedge clk); inout v; endclocking\n"),
      {"cb.v"});
}

TEST(DefaultClockedMemberRun, AnExpressionOverAClockingBlockInput) {
  ExpectDefaultClocked(
      ModuleHead(std::string(kPosedgeDefault) + kClockingBlock),
      {"(cb.a)", "cb.a == 1'b1"});
}

TEST(DefaultClockedMemberRun, DISABLED_EachStatementKindOverAMemberOrInput) {
  std::string head =
      ModuleHead(std::string(kPosedgeDefault) + kMembers + kClockingBlock);
  ExpectDefaultClocked(head, {"s.f", "cb.a"}, "assume property");
  ExpectDefaultClocked(head, {"s.f", "cb.a"}, "cover property");
  ExpectDefaultClocked(head, {"s.f", "cb.a"}, "cover sequence");
}

TEST(DefaultClockedMemberRun,
     DISABLED_AnInterfaceOrProgramsDefaultOverAMemberOrInput) {
  std::string body = std::string(kPosedgeDefault) + kMembers + kClockingBlock;
  ExpectDefaultClocked("interface w(input logic a, b, clk);\n" + body,
                       {"s.f", "cb.a"}, "assert property", "endinterface\n",
                       "  w u1(a, b, clk);\n");
  ExpectDefaultClocked("program w(input logic a, b, clk);\n" + body,
                       {"s.f", "cb.a"}, "assert property", "endprogram\n",
                       "  w u1(a, b, clk);\n");
}

TEST(DefaultClockedMemberRun, DISABLED_AGenerateBlockUnderTheModulesDefault) {
  ExpectDefaultClocked(ModuleHead(std::string(kPosedgeDefault) + kMembers +
                                  kClockingBlock + "  if (1) begin : g\n"),
                       {"s.f", "cb.a"}, "assert property",
                       "  end\nendmodule\n");
}

TEST(DefaultClockedMemberRun, DISABLED_ACheckerInheritingTheModulesDefault) {
  ExpectDefaultClocked(ModuleHead(std::string(kPosedgeDefault) + kMembers +
                                  kClockingBlock + "  checker chk;\n"),
                       {"s.f", "cb.a"}, "assert property",
                       "  endchecker\n  chk uc();\nendmodule\n");
}

TEST(DefaultClockedMemberRun, AProceduresClockOverAMemberOrInput) {
  ExpectDefaultClocked(
      ModuleHead(std::string(kPosedgeDefault) + kMembers + kClockingBlock +
                 "  always @(posedge clk) begin\n"),
      {"s.f", "cb.a"}, "assert property", "  end\nendmodule\n");
}

}  // namespace
