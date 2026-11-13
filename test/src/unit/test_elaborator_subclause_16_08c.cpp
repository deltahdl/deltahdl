#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr char kExcess[] =
    "sequence instance provides more actual arguments than the sequence has "
    "formal arguments";

constexpr char kUnknown[] =
    "sequence instance names 'z', which is not a formal argument of the "
    "sequence";

constexpr char kTwice[] =
    "sequence instance binds the formal 'x' more than once";

const char kBindTaker[] =
    "sequence s(x, y = 1); @(posedge clk) x ##1 y; endsequence\n";

std::string BindSource(const std::string& use) {
  return "module m;\n"
         "  bit clk, a, b;\n"
         "  " +
         std::string(kBindTaker) + "  " + use + "\nendmodule\n";
}

void ExpectBindReported(const std::string& src, const std::string& use,
                        const char* message) {
  SCOPED_TRACE(use);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, use), "16.8"));
}

void ExpectBindAccepted(const std::string& src, const std::string& use) {
  SCOPED_TRACE(use);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, use)));
}

std::vector<std::string> InstanceSites(const std::string& actuals) {
  const std::string kInst = "s(" + actuals + ")";
  return {
      "initial @(" + kInst + ") $display(\"x\");",
      "assert property (" + kInst + ");",
      "assume property (" + kInst + ");",
      "cover property (" + kInst + ");",
      "cover sequence (" + kInst + ");",
      "always @(posedge clk) assert property (" + kInst + ");",
      "sequence t; " + kInst + "; endsequence",
      "property p; " + kInst + "; endproperty",
      "initial wait (" + kInst + ".triggered);",
      "sequence u; @(posedge clk) a ##1 " + kInst + ".matched; endsequence"};
}

TEST(SequenceActualBinding, AnExcessPositionalActualInAnEventControl) {
  const std::string kUse = "initial @(s(a, b, a)) $display(\"x\");";
  ExpectBindReported(BindSource(kUse), kUse, kExcess);
}

TEST(SequenceActualBinding, DISABLED_AnExcessPositionalActualElsewhere) {
  auto sites = InstanceSites("a, b, a");
  sites.erase(sites.begin());
  for (const auto& use : sites) {
    ExpectBindReported(BindSource(use), use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_AnEmptyTrailingSlotPastTheLastFormal) {
  for (const auto& use : InstanceSites("a, b, ")) {
    ExpectBindReported(BindSource(use), use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_ANamedActualNamingNoFormalIsReported) {
  for (const auto& use : InstanceSites(".x(a), .z(b)")) {
    ExpectBindReported(BindSource(use), use, kUnknown);
  }
}

TEST(SequenceActualBinding, DISABLED_AFormalNamedTwiceIsReported) {
  for (const auto& use : InstanceSites(".x(a), .x(b)")) {
    ExpectBindReported(BindSource(use), use, kTwice);
  }
}

TEST(SequenceActualBinding, DISABLED_AFormalBoundByPositionThenByName) {
  for (const auto& use : InstanceSites("a, .x(b)")) {
    ExpectBindReported(BindSource(use), use, kTwice);
  }
}

TEST(SequenceActualBinding, EveryFormalBoundOnceIsAccepted) {
  for (const char* actuals :
       {"a, b", "a", "a, ", ".x(a), .y(b)", ".y(b), .x(a)", ".x(a)", "a, .y(b)",
        ".x(a), .y()"}) {
    for (const auto& use : InstanceSites(actuals)) {
      ExpectBindAccepted(BindSource(use), use);
    }
  }
}

struct BindPlace {
  std::string place;
  std::string src;
  std::string use;
};

std::string Assertion(const std::string& name, const std::string& actuals) {
  return "assert property (@(posedge clk) " + name + "(" + actuals + "));";
}

std::vector<BindPlace> BindPlaces(const std::string& actuals) {
  const std::string kDecl = "sequence s(x, y = 1); x ##1 y; endsequence\n";
  const std::string kHere = Assertion("s", actuals);
  const std::string kModule = "module m;\n  bit clk, a, b;\n  ";
  return {
      {"package scope",
       "package pk;\n  " + kDecl + "endpackage\n" + kModule +
           Assertion("pk::s", actuals) + "\nendmodule\n",
       Assertion("pk::s", actuals)},
      {"package import",
       "package pk;\n  " + kDecl + "endpackage\n" + kModule +
           "import pk::*;\n  " + kHere + "\nendmodule\n",
       kHere},
      {"interface instance",
       "interface ifc;\n  " + kDecl + "endinterface\n" + kModule +
           "ifc i();\n  " + Assertion("i.s", actuals) + "\nendmodule\n",
       Assertion("i.s", actuals)},
      {"interface",
       "interface ifc;\n  bit clk, a, b;\n  " + kDecl + "  " + kHere +
           "\nendinterface\nmodule m;\n  ifc i();\nendmodule\n",
       kHere},
      {"program",
       "program pg;\n  bit clk, a, b;\n  " + kDecl + "  " + kHere +
           "\nendprogram\n",
       kHere},
      {"clocking block",
       kModule + "clocking cb @(posedge clk);\n    " + kDecl +
           "  endclocking\n  " + Assertion("cb.s", actuals) + "\nendmodule\n",
       Assertion("cb.s", actuals)},
      {"checker",
       "checker ck(bit clk, bit a, bit b);\n  " + kDecl + "  " + kHere +
           "\nendchecker\n" + kModule + "ck k(clk, a, b);\nendmodule\n",
       kHere},
      {"generate block",
       kModule + "if (1) begin : g\n    " + kDecl + "    " + kHere +
           "\n  end\nendmodule\n",
       kHere},
      {"compilation unit", kDecl + kModule + kHere + "\nendmodule\n", kHere}};
}

TEST(SequenceActualBinding, DISABLED_AnExcessPositionalActualInEveryScope) {
  for (const auto& placed : BindPlaces("a, b, a")) {
    SCOPED_TRACE(placed.place);
    ExpectBindReported(placed.src, placed.use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_ANamedActualNamingNoFormalInEveryScope) {
  for (const auto& placed : BindPlaces(".z(b)")) {
    SCOPED_TRACE(placed.place);
    ExpectBindReported(placed.src, placed.use, kUnknown);
  }
}

TEST(SequenceActualBinding, EveryFormalBoundOnceInEveryScopeIsAccepted) {
  for (const char* actuals : {"a, b", ".x(a), .y(b)", "a, .y(b)"}) {
    for (const auto& placed : BindPlaces(actuals)) {
      SCOPED_TRACE(placed.place);
      ExpectBindAccepted(placed.src, placed.use);
    }
  }
}

}  // namespace
