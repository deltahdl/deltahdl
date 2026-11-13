#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

std::string InstanceBench(const std::string& outside,
                          const std::string& items) {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin #22 b = 1; #20 a = 0; #30 $finish; end\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

std::string Covered(const std::string& tag, const std::string& seq) {
  return "cover property (@(posedge clk) " + seq + ") $display(\"" + tag +
         " %0t\", $time);";
}

TEST(SequenceInstanceUse, AnInstanceStandsWhereverASequenceExprMay) {
  const std::string kSrc = InstanceBench(
      "",
      "sequence s; b ##1 a; endsequence\n"
      "  sequence t; s ##1 b; endsequence\n"
      "  property p; s ##1 b; endproperty\n  " +
          Covered("plain", "s") + "\n  " + Covered("delay", "s ##1 b") +
          "\n  " + Covered("and", "s and b") + "\n  " +
          Covered("or", "s or (a && !b)") + "\n  " +
          Covered("intersect", "s intersect (b ##1 b)") + "\n  " +
          Covered("throughout", "b throughout s") + "\n  " +
          Covered("within", "s within (a ##1 b ##1 1)") + "\n  " +
          Covered("repeat", "s [*1:2]") + "\n  " +
          Covered("first", "first_match(s)") + "\n  " + Covered("body", "t") +
          "\n  " +
          "cover property (@(posedge clk) p) $display(\"prop %0t\", "
          "$time);");
  ExpectLines(kSrc, "plain ", "35");
  ExpectLines(kSrc, "delay ", "45");
  ExpectLines(kSrc, "and ", "35");
  ExpectLines(kSrc, "or ", "5 15 35");
  ExpectLines(kSrc, "intersect ", "35");
  ExpectLines(kSrc, "throughout ", "35");
  ExpectLines(kSrc, "within ", "35 45");
  ExpectLines(kSrc, "repeat ", "35");
  ExpectLines(kSrc, "first ", "35");
  ExpectLines(kSrc, "body ", "45");
  ExpectLines(kSrc, "prop ", "45");
}

const char kForwardPair[] =
    "sequence t(p, q); u(p, q) ##1 p; endsequence\n"
    "  sequence u(p, q); p ##1 q; endsequence";

struct NamedPlace {
  std::string place;
  std::string outside;
  std::string items;
};

std::vector<NamedPlace> ForwardPlaces() {
  const std::string kPair = kForwardPair;
  const std::string kUse = Covered("fwd", "t(b, a)");
  return {{"module", "", kPair + "\n  " + kUse},
          {"interface", "interface ifc;\n  " + kPair + "\nendinterface\n",
           "ifc i();\n  " + Covered("fwd", "i.t(b, a)")},
          {"program",
           "program pg(input logic clk, a, b);\n  " + kPair + "\n  " + kUse +
               "\nendprogram\n",
           "pg g(clk, a, b);"},
          {"checker",
           "checker ck(logic clk, logic a, logic b);\n  " + kPair + "\n  " +
               kUse + "\nendchecker\n",
           "ck k(clk, a, b);"},
          {"package by name", "package pk;\n  " + kPair + "\nendpackage\n",
           Covered("fwd", "pk::t(b, a)")},
          {"package by import", "package pk;\n  " + kPair + "\nendpackage\n",
           "import pk::*;\n  " + kUse},
          {"generate", "",
           "if (1) begin : g\n    " + kPair + "\n    " + kUse + "\n  end"}};
}

TEST(SequenceInstanceUse, AnInstanceMayPrecedeItsDeclarationAnywhere) {
  for (const auto& placed : ForwardPlaces()) {
    SCOPED_TRACE(placed.place);
    ExpectLines(InstanceBench(placed.outside, placed.items), "fwd ", "45");
  }
}

std::string ClockingPair(const std::string& pair) {
  return InstanceBench("", "clocking cb @(posedge clk);\n    " + pair +
                               "\n  endclocking\n  " +
                               Covered("fwd", "cb.t(b, a)"));
}

TEST(SequenceInstanceUse, DISABLED_AClockingBlockInstanceMayPrecedeItsDecl) {
  ExpectLines(ClockingPair(kForwardPair), "fwd ", "45");
}

TEST(SequenceInstanceUse, DISABLED_AClockingBlockBodyInstantiatesASibling) {
  ExpectLines(ClockingPair("sequence u(p, q); p ##1 q; endsequence\n"
                           "    sequence t(p, q); u(p, q) ##1 p; endsequence"),
              "fwd ", "45");
}

TEST(SequenceInstanceUse, AClockingBlockBodyInstantiatesAModuleSequence) {
  ExpectLines(
      "module top;\n"
      "  logic clk = 0, a = 1, b = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #22 b = 1; #20 a = 0; #30 $finish; end\n"
      "  sequence u(p, q); p ##1 q; endsequence\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence t(p, q); u(p, q) ##1 p; endsequence\n"
      "  endclocking\n"
      "  cover property (@(posedge clk) cb.t(b, a)) $display(\"fwd %0t\", "
      "$time);\n"
      "endmodule\n",
      "fwd ", "45");
}

TEST(SequenceInstanceUse, DISABLED_AUnitInstanceMayPrecedeItsDeclaration) {
  ExpectLines(InstanceBench(std::string(kForwardPair) + "\n",
                            Covered("fwd", "t(b, a)")),
              "fwd ", "45");
}

struct InstanceName {
  std::string form;
  std::string outside;
  std::string items;
  std::string instance;
};

const char kClocked[] = "sequence s; @(posedge clk) b ##1 a; endsequence";

std::vector<InstanceName> InstanceNames() {
  const std::string kOwn = kClocked;
  const std::string kPackage =
      "package pk;\n"
      "  sequence s(c, x, y); @(posedge c) x ##1 y; endsequence\n"
      "endpackage\n";
  return {{"simple name", "", kOwn, "s"},
          {"the design element's name", "", kOwn, "top.s"},
          {"a generate block's name", "",
           "if (1) begin : g\n    " + kOwn + "\n  end", "g.s"},
          {"a path through a generate block", "",
           "if (1) begin : g\n    " + kOwn + "\n  end", "top.g.s"},
          {"a clocking block's name", "",
           "clocking cb @(posedge clk);\n    sequence s; b ##1 a; endsequence\n"
           "  endclocking",
           "cb.s"},
          {"an interface instance's name",
           "interface ifc(input logic clk);\n"
           "  sequence s(x, y); @(posedge clk) x ##1 y; endsequence\n"
           "endinterface\n",
           "ifc u(clk);", "u.s(b, a)"},
          {"a package scope", kPackage, "", "pk::s(clk, b, a)"}};
}

std::string EveryUse(const std::string& instance) {
  return Covered("cover", instance) + "\n  " + "initial begin wait (" +
         instance + ".triggered); $display(\"trig %0t\", $time); end\n  " +
         "cover property (@(negedge clk) " + instance +
         ".matched) $display(\"matched %0t\", $time);\n  " +
         "initial begin @(" + instance +
         "); $display(\"event %0t\", $time); end";
}

void ExpectEveryUse(const std::string& src) {
  ExpectLines(src, "cover ", "35");
  ExpectLines(src, "trig ", "35");
  ExpectLines(src, "matched ", "40");
  ExpectLines(src, "event ", "35");
}

std::string UsedThrough(const InstanceName& named) {
  return InstanceBench(named.outside,
                       named.items + "\n  " + EveryUse(named.instance));
}

TEST(SequenceInstanceUse, ASimpleNameServesEveryUse) {
  ExpectEveryUse(UsedThrough(InstanceNames().front()));
}

TEST(SequenceInstanceUse, DISABLED_EveryNameServesEveryUse) {
  for (const auto& named : InstanceNames()) {
    SCOPED_TRACE(named.form);
    ExpectEveryUse(UsedThrough(named));
  }
}

TEST(SequenceInstanceUse, AScopeOrInstanceNameStandsInAnAssertion) {
  for (const auto& named : InstanceNames()) {
    if (named.instance.find("::") == std::string::npos &&
        named.instance.rfind("cb.", 0) != 0 &&
        named.instance.rfind("u.", 0) != 0) {
      continue;
    }
    SCOPED_TRACE(named.form);
    ExpectLines(UsedThrough(named), "cover ", "35");
  }
}

TEST(SequenceInstanceUse, DISABLED_TheUnitScopeServesEveryUse) {
  ExpectEveryUse(
      InstanceBench("sequence s(c, x, y); @(posedge c) x ##1 y; endsequence\n",
                    EveryUse("$unit::s(clk, b, a)")));
}

}  // namespace
