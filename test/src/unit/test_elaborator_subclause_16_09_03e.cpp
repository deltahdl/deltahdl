#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kExplicitOnly =
    "shall have its clocking event specified explicitly";
constexpr const char* kNoClock = "has no clocking event";

std::vector<Diagnostic> Elaborated(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return f.diag.Diagnostics();
}

void ExpectReported(const std::string& src, const char* report,
                    const std::string& at) {
  EXPECT_TRUE(
      ReportedError(Elaborated(src), report, LineHolding(src, at), "16.9.3"))
      << src;
}

void ExpectAccepted(const std::string& src) {
  EXPECT_TRUE(Elaborated(src).empty()) << src;
}

std::ptrdiff_t ReportsOn(const std::vector<Diagnostic>& diags,
                         const char* report, uint32_t line) {
  return std::ranges::count_if(diags, [&](const Diagnostic& d) {
    return d.loc.line == line && d.message.find(report) != std::string::npos;
  });
}

TEST(SampledValueClockReports,
     DISABLED_ADefaultDisableConditionIsReportedOnce) {
  for (int assertions : {0, 1, 2, 4}) {
    std::string src =
        "module m;\n  logic clk, rst, a;\n"
        "  default clocking @(posedge clk); endclocking\n"
        "  default disable iff $rose(rst);\n";
    for (int i = 0; i < assertions; ++i) {
      src += "  assert property (a);\n";
    }
    src += "endmodule\n";
    EXPECT_EQ(ReportsOn(Elaborated(src), kExplicitOnly, 4), 1) << src;
    std::string allowed = src;
    allowed.replace(allowed.find("$rose(rst)"), 10,
                    "$rose(rst, @(posedge clk))");
    ExpectAccepted(allowed);
  }
}

constexpr const char* kClockExpressionPlaces[] = {
    "  assert property (@(posedge %s) a);\n",
    "  sequence s;\n    @(posedge %s) a;\n  endsequence\n",
    "  property p;\n    @(posedge %s) a;\n  endproperty\n",
};

std::string InModule(const std::string& items) {
  return "module m;\n  logic clk, gclk, rst, a, b;\n" + items + "endmodule\n";
}

std::string Placed(const char* place, const std::string& call) {
  std::string items = place;
  return items.replace(items.find("%s"), 2, call);
}

TEST(SampledValueClockReports, AnUnclockedCallInAClockExpressionIsReported) {
  for (const char* place : kClockExpressionPlaces) {
    for (const char* call : {"$past(clk)", "$rose(clk)"}) {
      ExpectReported(InModule(Placed(place, call)), kExplicitOnly, call);
    }
    ExpectAccepted(
        InModule(Placed(place, "$past(clk, 1, 1, @(posedge gclk))")));
  }
}

std::string WithDefaultClocking(const std::string& items) {
  return InModule("  default clocking @(posedge clk); endclocking\n" + items);
}

void ExpectNoClockReported(const std::string& items, const std::string& at) {
  ExpectReported(InModule(items), kNoClock, at);
  ExpectAccepted(WithDefaultClocking(items));
}

TEST(SampledValueClockReports,
     DISABLED_AnUnclockedCallInAContinuousAssignment) {
  ExpectNoClockReported("  assign b = $rose(a);\n", "$rose");
  ExpectNoClockReported("  wire w = $changed(a);\n", "$changed");
}

TEST(SampledValueClockReports, AnUnclockedCallInAModuleFunctionOrAlwaysComb) {
  ExpectNoClockReported(
      "  function bit f();\n    return $fell(a);\n  endfunction\n", "$fell");
  ExpectNoClockReported("  logic y;\n  always_comb y = $past(a);\n", "$past");
}

TEST(SampledValueClockReports,
     DISABLED_AnUnclockedCallInAPackageFunctionOrAMethod) {
  ExpectReported(
      "package pk;\n  function bit f(logic x);\n    return $rose(x);\n"
      "  endfunction\nendpackage\n",
      kNoClock, "$rose");
  ExpectAccepted(
      "package pk;\n  function bit f(logic x, logic c);\n"
      "    return $rose(x, @(posedge c));\n  endfunction\nendpackage\n");
  ExpectReported(InModule("  class C;\n    function bit g();\n"
                          "      return $stable(a);\n    endfunction\n"
                          "  endclass\n"),
                 kNoClock, "$stable");
  ExpectAccepted(
      InModule("  class C;\n    function bit g();\n"
               "      return $stable(a, @(posedge clk));\n"
               "    endfunction\n  endclass\n"));
}

TEST(SampledValueClockReports, TheClausesProcedureWithASecondEventControl) {
  ExpectNoClockReported(
      "  logic clk2, x, y;\n  always @(posedge clk) begin\n"
      "    @(negedge clk2);\n    x = $past(y, 5);\n  end\n",
      "$past");
}

struct Container {
  const char* open;
  const char* close;
  const char* instance;
};

constexpr Container kContainers[] = {
    {"module c;\n", "endmodule\n", "  c u();\n"},
    {"interface c;\n", "endinterface\n", "  c u();\n"},
    {"program c;\n", "endprogram\n", "  c u();\n"},
};

TEST(SampledValueClockReports, EachReportInAnInterfaceProgramOrChecker) {
  for (const Container& c : kContainers) {
    auto in = [&](const std::string& items) {
      return std::string(c.open) + "  logic clk, rst, a, b;\n" + items +
             c.close + "module top;\n" + c.instance + "endmodule\n";
    };
    ExpectReported(
        in("  assert property (@(posedge clk) disable iff ($fell(rst)) a);\n"),
        kExplicitOnly, "$fell");
    ExpectAccepted(
        in("  assert property (@(posedge clk)\n"
           "    disable iff ($fell(rst, @(posedge clk))) a);\n"));
    ExpectReported(in("  assert property (@(posedge $past(clk)) a);\n"),
                   kExplicitOnly, "$past");
    ExpectAccepted(
        in("  assert property (@(posedge $past(clk, 1, 1, "
           "@(posedge rst))) a);\n"));
    ExpectReported(in("  initial b = $rose(a);\n"), kNoClock, "$rose");
    ExpectAccepted(
        in("  default clocking @(posedge clk); endclocking\n"
           "  initial b = $rose(a);\n"));
  }
  auto in_checker = [](const std::string& items) {
    return "checker ck(logic clk, logic rst, logic a);\n" + items +
           "endchecker\nmodule top;\n  logic clk, rst, a;\n"
           "  ck k(clk, rst, a);\nendmodule\n";
  };
  ExpectReported(
      in_checker(
          "  assert property (@(posedge clk) disable iff ($fell(rst)) a);\n"),
      kExplicitOnly, "$fell");
  ExpectAccepted(
      in_checker("  assert property (@(posedge clk)\n"
                 "    disable iff ($fell(rst, @(posedge clk))) a);\n"));
  ExpectReported(in_checker("  assert property (@(posedge $past(clk)) a);\n"),
                 kExplicitOnly, "$past");
  ExpectAccepted(in_checker(
      "  assert property (@(posedge $past(clk, 1, 1, @(posedge rst))) a);\n"));
  ExpectReported(
      in_checker("  function bit f();\n    return $rose(a);\n  endfunction\n"),
      kNoClock, "$rose");
  ExpectAccepted(
      in_checker("  default clocking @(posedge clk); endclocking\n"
                 "  function bit f();\n    return $rose(a);\n  endfunction\n"));
}

}  // namespace
