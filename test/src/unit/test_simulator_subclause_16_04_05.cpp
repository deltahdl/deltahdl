#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

const char kFail[] = "$display(\"%0t a1 %0d %0d\", $time, a, b)";
const char kExpected[] = "10 a1 1 0\n10 a1 2 0\n30 a1 3 2\n40 a1 1 2\n";

std::string Function(const std::string& qualifiers,
                     const std::string& assertion) {
  return "  " + qualifiers + "function bit f(input logic [1:0] a, b);\n" +
         "    a1: " + assertion + ";\n" + "    return a == b;\n" +
         "  endfunction\n";
}

std::string Scenario(const std::string& outside, const std::string& items,
                     const std::string& call,
                     const std::string& procedure = "always_comb") {
  return outside +
         "module t;\n"
         "  logic [1:0] x = 0, y = 0, z = 0, w = 0;\n"
         "  logic s1, s2;\n" +
         items + "  " + procedure + " begin : b1 s1 = " + call +
         "(x, y); end\n" + "  " +
         (procedure == "always_comb" ? procedure
                                     : std::string("always @(z or w)")) +
         " begin : b2 s2 = " + call +
         "(z, w); end\n"
         "  initial begin\n"
         "    #10 x = 1; z = 2;\n"
         "    #10 x = 2; #0 y = 2;\n"
         "    #10 x = 3; #0 w = 2;\n"
         "    #10 x = 0; z = 1; #0 y = 0;\n"
         "  end\n"
         "endmodule\n";
}

std::string SortedRun(const std::string& src, SimFixture& f) {
  std::istringstream in(RunCapture(src, f));
  EXPECT_FALSE(f.diag.HasErrors());
  std::vector<std::string> lines;
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  std::string out;
  for (const auto& line : lines) out += line + "\n";
  return out;
}

std::string SortedRun(const std::string& src) {
  SimFixture f;
  return SortedRun(src, f);
}

TEST(DeferredAssertionProcesses, EachCallingProcessReportsOnItsOwn) {
  EXPECT_EQ(
      SortedRun(Scenario(
          "", Function("", std::string("assert #0 (a == b) else ") + kFail),
          "f")),
      kExpected);
}

TEST(DeferredAssertionProcesses, EveryKindIsQueuedPerProcess) {
  for (const std::string& assertion :
       {std::string("assert final (a == b) else ") + kFail,
        std::string("assume #0 (a == b) else ") + kFail,
        std::string("assume final (a == b) else ") + kFail}) {
    EXPECT_EQ(SortedRun(Scenario("", Function("", assertion), "f")), kExpected)
        << assertion;
  }
}

TEST(DeferredAssertionProcesses, ACoverCountsEachProcessesUnflushedSuccess) {
  for (const char* kind : {"cover #0", "cover final"}) {
    SimFixture f;
    EXPECT_EQ(
        SortedRun(
            Scenario("", Function("", std::string(kind) + " (a != b) " + kFail),
                     "f"),
            f),
        kExpected)
        << kind;
    uint64_t succeeded = 0;
    for (const auto& r : f.ctx.ImmediateCovers().Results()) {
      succeeded += r.succeeded;
    }
    EXPECT_EQ(succeeded, 4u) << kind;
  }
}

TEST(DeferredAssertionProcesses, AFunctionOfAnotherScopeIsQueuedPerProcess) {
  const std::string kAssert = std::string("assert #0 (a == b) else ") + kFail;
  EXPECT_EQ(SortedRun(Scenario(
                "package pkg;\n" + Function("", kAssert) + "endpackage\n", "",
                "pkg::f")),
            kExpected);
  EXPECT_EQ(SortedRun(Scenario(
                "interface ifc;\n" + Function("", kAssert) + "endinterface\n",
                "  ifc i();\n", "i.f")),
            kExpected);
  EXPECT_EQ(SortedRun(Scenario(
                "class C;\n" + Function("static ", kAssert) + "endclass\n", "",
                "C::f")),
            kExpected);
}

TEST(DeferredAssertionProcesses, AnEventControlledProcedureIsQueuedPerProcess) {
  EXPECT_EQ(
      SortedRun(Scenario(
          "", Function("", std::string("assert #0 (a == b) else ") + kFail),
          "f", "always @(x or y)")),
      kExpected);
}

}  // namespace
