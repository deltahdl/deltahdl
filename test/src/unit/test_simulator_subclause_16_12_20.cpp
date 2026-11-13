#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string ExamplesSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic clkev = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c, d, e, f;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  always @(posedge clk) clkev <= ~clkev;\n"
         "  assign a = tick inside {1, 2, 3, 6};\n"
         "  assign b = tick inside {1, 4, 6};\n"
         "  assign c = tick inside {2, 3, 7};\n"
         "  assign d = tick inside {2, 3, 5, 7};\n"
         "  assign e = tick inside {5, 8};\n"
         "  assign f = tick inside {3};\n"
         "  property rule1;\n"
         "    @(posedge clk) a |-> b ##1 c ##1 d;\n"
         "  endproperty\n"
         "  property rule2;\n"
         "    @(clkev) disable iff (e) a |-> not (b ##1 c ##1 d);\n"
         "  endproperty\n"
         "  property rule3;\n"
         "    @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));\n"
         "  endproperty\n"
         "  property rule4;\n"
         "    @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));\n"
         "  endproperty\n"
         "  property rule5;\n"
         "    @(posedge clk)\n"
         "    a ##1 (b || c)[->1] |->\n"
         "      if (b)\n"
         "        (##1 d |-> e)\n"
         "      else\n"
         "        f;\n"
         "  endproperty\n"
         "  property rule6(x, y);\n"
         "    ##1 x |-> y;\n"
         "  endproperty\n"
         "  property rule5a;\n"
         "    @(posedge clk)\n"
         "    a ##1 (b || c)[->1] |->\n"
         "      if (b)\n"
         "        rule6(d, e)\n"
         "      else\n"
         "        f;\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

std::pair<uint64_t, uint64_t> CountsOfExample(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(ExamplesSource("  p: assert property (" + spec +
                                              ") passes++; else fails++;\n"),
                               f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  return {passes->value.ToUint64(), fails->value.ToUint64()};
}

TEST(PropertyExamples, Rule1RequiresTheSequenceAfterA) {
  auto counts = CountsOfExample("rule1");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

TEST(PropertyExamples, Rule2NegatesTheConsequentUnderDisableIff) {
  auto counts = CountsOfExample("rule2");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(PropertyExamples, Rule3RequiresEitherConsequent) {
  auto counts = CountsOfExample("rule3");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(PropertyExamples, Rule4RequiresBothConsequents) {
  auto counts = CountsOfExample("rule4");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyExamples, Rule5SplitsTheConsequentByIfElse) {
  auto counts = CountsOfExample("rule5");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyExamples, Rule5aInstantiatesRule6AsAPropertyExpression) {
  auto counts = CountsOfExample("rule5a");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedExampleProperties =
    "  property rule6(x, y); ##1 x |-> y; endproperty\n";

const PlacedProperty kExampleShapesInPlace[] = {
    {"a |-> b ##1 c ##1 d", {3, 1}, 2},
    {"disable iff (b && c) a |-> not (b ##1 c)", {2, 1}, 2},
    {"d[*2] |-> ((##[1:3] c) or (a |=> b))", {4, 0}, 4},
    {"d[*2] |-> ((##[1:3] c) and (a |=> b))", {3, 1}, 3},
    {"a ##1 (b || c)[->1] |-> if (b) (##1 d |-> a) else d", {3, 1}, 3},
    {"a ##1 (b || c)[->1] |-> if (b) rule6(d, a) else d", {3, 1}, 3}};

TEST(PropertyExamples, EachExampleShapeCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kExampleShapesInPlace) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedExampleProperties);
    }
  }
}

TEST(PropertyExamples,
     DISABLED_EachExampleShapeCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kExampleShapesInPlace) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedExampleProperties);
  }
}

constexpr const char* kDeclaringModules =
    "interface ifc(input logic clk);\n"
    "  logic v = 1;\n"
    "  property pn; v; endproperty\n"
    "  property ps(x); x == v; endproperty\n"
    "endinterface\n"
    "checker chk(logic clk);\n"
    "  bit v = 1;\n"
    "  property pn; v; endproperty\n"
    "  property ps(x); x == v; endproperty\n"
    "endchecker\n"
    "module leaf(input logic clk);\n"
    "  logic v = 1;\n"
    "  property ps(x); x == v; endproperty\n"
    "endmodule\n";

std::string HierarchicalSource(const std::string& where,
                               const std::string& items) {
  std::string sub_items;
  std::string top_items;
  std::string extra;
  if (where == "child") {
    extra =
        "module kid(input logic clk);\n"
        "  logic a = 1;\n"
        "  logic v = 0;\n" +
        items + "endmodule\n";
    sub_items = "  kid k(clk);\n";
  } else if (where == "port") {
    extra =
        "module user(ifc p, input logic clk, a);\n"
        "  logic v = 0;\n" +
        items + "endmodule\n";
    top_items = "  user q(i0, clk, a);\n";
  } else if (where == "sub") {
    sub_items = "  logic a = 1;\n" + items;
  } else {
    top_items = items;
  }
  return std::string(kDeclaringModules) + extra +
         "module sub(input logic clk);\n"
         "  logic v = 1;\n"
         "  property pn; v; endproperty\n"
         "  property ps(x); x == v; endproperty\n"
         "  property pc; @(posedge clk) v; endproperty\n"
         "  property pa(x); @(posedge clk) x == v; endproperty\n"
         "  leaf w(clk);\n" +
         sub_items +
         "endmodule\n"
         "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 1;\n"
         "  logic v = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sub u(clk);\n"
         "  ifc i0(clk);\n"
         "  chk c0(clk);\n"
         "  for (genvar i = 0; i < 2; i++) begin : g\n"
         "    logic v = 1;\n"
         "    property ps(x); x == v; endproperty\n"
         "  end\n"
         "  if (1) begin : blk\n"
         "    logic v = 1;\n"
         "    property ps(x); x == v; endproperty\n"
         "  end\n" +
         top_items +
         "  initial #32 $finish;\n"
         "endmodule\n";
}

struct NamedForm {
  const char* where;
  const char* name;
};

void ExpectNamedFormHoldsInEachUse(const NamedForm& form) {
  const std::string kName = form.name;
  const std::string kRule =
      "  property r(y); y |-> " + kName + "; endproperty\n";
  struct Use {
    std::string spec;
    bool negated;
  };
  const Use kUses[] = {{"@(posedge clk) " + kName, false},
                       {"@(posedge clk) not " + kName, true},
                       {"@(posedge clk) a |-> " + kName, false},
                       {"@(posedge clk) " + kName + " and a", false},
                       {"@(posedge clk) r(a)", false}};
  for (const Use& use : kUses) {
    for (const char* directive : {"assert", "assume", "cover"}) {
      SCOPED_TRACE(std::string(form.where) + " " + directive + " " + use.spec);
      PlaceCounts expected{3, 0};
      if (use.negated) expected = {0, 3};
      if (std::string(directive) == "cover") expected.fails = 0;
      if (std::string(directive) == "cover" && use.negated) {
        expected.passes = 0;
      }
      EXPECT_EQ(CountThroughTheEnd(HierarchicalSource(
                    form.where, kRule + PlacedDirective(directive, use.spec))),
                expected);
    }
  }
}

TEST(HierarchicalPropertyInstance, ABareNameReadsItsOwnScopeInEachUse) {
  ExpectNamedFormHoldsInEachUse({"sub", "pn"});
  ExpectNamedFormHoldsInEachUse({"sub", "ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     AnInterfaceInstancePathReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"top", "i0.pn"});
  ExpectNamedFormHoldsInEachUse({"top", "i0.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AnInterfacePortPathReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"port", "p.pn"});
  ExpectNamedFormHoldsInEachUse({"port", "p.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AModuleInstancePathReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"top", "u.pn"});
  ExpectNamedFormHoldsInEachUse({"top", "u.ps(a)"});
  ExpectNamedFormHoldsInEachUse({"top", "u.w.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_APathFromTheRootOrTheTopNameReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"top", "$root.m.u.ps(a)"});
  ExpectNamedFormHoldsInEachUse({"top", "m.u.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AnUpwardNameReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"child", "u.pn"});
  ExpectNamedFormHoldsInEachUse({"child", "u.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AGenerateBlockPathReadsTheBlockInEachUse) {
  ExpectNamedFormHoldsInEachUse({"top", "g[1].ps(a)"});
  ExpectNamedFormHoldsInEachUse({"top", "blk.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_ACheckerInstancePathReadsTheInstanceInEachUse) {
  ExpectNamedFormHoldsInEachUse({"top", "c0.pn"});
  ExpectNamedFormHoldsInEachUse({"top", "c0.ps(a)"});
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AClockedPropertyNamedThroughAModulePathGivesItsClock) {
  for (const char* spec : {"u.pc", "u.pa(a)"}) {
    for (const char* directive : {"assert", "assume", "cover"}) {
      SCOPED_TRACE(std::string(directive) + " " + spec);
      EXPECT_EQ(CountThroughTheEnd(HierarchicalSource(
                    "top", PlacedDirective(directive, spec))),
                (PlaceCounts{3, 0}));
    }
  }
}

std::string RedeclaringSource(const std::string& outside,
                              const std::string& top_items) {
  return outside +
         "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 1;\n"
         "  always #5 clk = ~clk;\n" +
         top_items +
         "  initial #32 $finish;\n"
         "endmodule\n";
}

constexpr const char* kModuleProperties =
    "  logic v = 1;\n"
    "  property pn; v; endproperty\n"
    "  property ps(x); x == v; endproperty\n"
    "  property pq; pn; endproperty\n";

TEST(PropertyBodyNames, ABodysNamesResolveInItsOwnScope) {
  for (const char* spec : {"pn", "ps(a)", "pq"}) {
    for (const char* directive : {"assert", "assume", "cover"}) {
      SCOPED_TRACE(std::string(directive) + " " + spec);
      EXPECT_EQ(CountThroughTheEnd(RedeclaringSource(
                    "", std::string(kModuleProperties) +
                            PlacedDirective(directive, std::string("@(posedge "
                                                                   "clk) ") +
                                                           spec))),
                (PlaceCounts{3, 0}));
    }
  }
}

constexpr const char* kPackageProperties =
    "package pk;\n"
    "  bit v = 1;\n"
    "  property pn; v; endproperty\n"
    "  property ps(x); x == v; endproperty\n"
    "  property pq; pn; endproperty\n"
    "endpackage\n";

constexpr const char* kUnitProperties =
    "bit v = 1;\n"
    "property pn; v; endproperty\n"
    "property ps(x); x == v; endproperty\n"
    "property pq; pn; endproperty\n";

std::string RedeclaringUse(const std::string& where,
                           const std::string& directive,
                           const std::string& spec) {
  const std::string kClocked = "@(posedge clk) " + spec;
  if (where == "generate block") {
    return RedeclaringSource("", std::string(kModuleProperties) +
                                     "  if (1) begin : gb\n"
                                     "    logic v = 0;\n  " +
                                     PlacedDirective(directive, kClocked) +
                                     "  end\n");
  }
  if (where == "procedure") {
    return RedeclaringSource("", std::string(kModuleProperties) +
                                     "  always @(posedge clk) begin : nb\n"
                                     "    logic v;\n"
                                     "    v = 0;\n  " +
                                     PlacedDirective(directive, spec) +
                                     "  end\n");
  }
  if (where == "package") {
    return RedeclaringSource(kPackageProperties,
                             "  logic v = 0;\n"
                             "  import pk::pn, pk::ps, pk::pq;\n" +
                                 PlacedDirective(directive, kClocked));
  }
  if (where == "package scope") {
    return RedeclaringSource(
        kPackageProperties,
        "  logic v = 0;\n" +
            PlacedDirective(directive, "@(posedge clk) pk::" + spec));
  }
  return RedeclaringSource(
      kUnitProperties,
      "  logic v = 0;\n" + PlacedDirective(directive, kClocked));
}

void ExpectBodyNamesResolveWhereDeclared(const std::string& where) {
  for (const char* spec : {"pn", "ps(a)", "pq"}) {
    for (const char* directive : {"assert", "assume", "cover"}) {
      SCOPED_TRACE(where + ": " + directive + " " + spec);
      EXPECT_EQ(CountThroughTheEnd(RedeclaringUse(where, directive, spec)),
                (PlaceCounts{3, 0}));
    }
  }
}

TEST(PropertyBodyNames,
     ABodysNamesResolveWhereDeclaredUnderAProcedureOrImportedPackageUse) {
  ExpectBodyNamesResolveWhereDeclared("procedure");
  ExpectBodyNamesResolveWhereDeclared("package");
}

TEST(PropertyBodyNames,
     DISABLED_ABodysNamesResolveWhereDeclaredUnderAGenerateScopedOrUnitUse) {
  ExpectBodyNamesResolveWhereDeclared("generate block");
  ExpectBodyNamesResolveWhereDeclared("package scope");
  ExpectBodyNamesResolveWhereDeclared("compilation unit");
}

std::string GlobalClockSource(const std::string& sub_items,
                              const std::string& top_items) {
  return "module sub(input logic clk);\n"
         "  logic v = 1;\n"
         "  global clocking @(posedge clk); endclocking\n"
         "  property pg; @($global_clock) v; endproperty\n" +
         sub_items +
         "endmodule\n"
         "module m;\n"
         "  logic clk = 0;\n"
         "  logic slow = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 slow = ~slow;\n"
         "  global clocking @(posedge slow); endclocking\n"
         "  sub u(clk);\n" +
         top_items +
         "  initial #32 $finish;\n"
         "endmodule\n";
}

TEST(HierarchicalPropertyInstance,
     AGlobalClockPropertyRunsOnItsOwnScopesGlobalClocking) {
  for (const char* directive : {"assert", "assume", "cover"}) {
    SCOPED_TRACE(directive);
    EXPECT_EQ(CountThroughTheEnd(
                  GlobalClockSource(PlacedDirective(directive, "pg"), "")),
              (PlaceCounts{3, 0}));
  }
}

TEST(HierarchicalPropertyInstance,
     DISABLED_AGlobalClockPropertyNamedThroughAPathRunsOnTheUsersClocking) {
  for (const char* directive : {"assert", "assume", "cover"}) {
    SCOPED_TRACE(directive);
    EXPECT_EQ(CountThroughTheEnd(
                  GlobalClockSource("", PlacedDirective(directive, "u.pg"))),
              (PlaceCounts{2, 0}));
  }
}

}  // namespace
