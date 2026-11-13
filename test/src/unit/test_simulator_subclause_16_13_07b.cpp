#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kInitSignals =
    "  logic clk = 0, clk1 = 0, clk2 = 0;\n"
    "  logic f = 1, e = 1, a = 0, b = 0, c = 0, d = 0, g = 0;\n"
    "  int v = 0;\n";

constexpr const char* kInitStimulus =
    "  always #5 clk = ~clk;\n"
    "  always @(negedge clk) v++;\n"
    "  initial begin\n"
    "    #18;\n"
    "    forever begin\n"
    "      clk1 = 1;\n"
    "      #10 clk1 = 0;\n"
    "      #10;\n"
    "    end\n"
    "  end\n"
    "  initial begin\n"
    "    #22;\n"
    "    forever begin\n"
    "      clk2 = 1;\n"
    "      #10 clk2 = 0;\n"
    "      #10;\n"
    "    end\n"
    "  end\n"
    "  initial begin\n"
    "    #10 f = 0; e = 0; g = 1;\n"
    "    #6 e = 1; a = 1; b = 1;\n"
    "    #4 e = 0; a = 0; b = 0; g = 0; c = 1;\n"
    "    #4 c = 0;\n"
    "    #76 $finish;\n"
    "  end\n";

constexpr const char* kInitPorts =
    "(input logic clk, clk1, clk2, f, e, a, b, c, d, g, input var int v)";

constexpr const char* kInitInstance =
    "  w u(clk, clk1, clk2, f, e, a, b, c, d, g, v);\n";

std::string InitTop(const std::string& items) {
  return "module t;\n" + std::string(kInitSignals) + kInitStimulus + items +
         "endmodule\n";
}

std::string InitAssertion(const std::string& body) {
  return "  assert property (@(posedge clk) " + body +
         ")\n"
         "    $display(\"PASS\");\n"
         "    else $display(\"FAIL %0t\", $time);\n";
}

std::string InitPlaceSource(const std::string& place,
                            const std::string& declarations,
                            const std::string& body) {
  std::string items = declarations + InitAssertion(body);
  if (place == "module") return InitTop(items);
  if (place == "generate") {
    return InitTop("  if (1) begin : g_init\n" + items + "  end\n");
  }
  if (place == "package") {
    return "package pk;\n" + declarations + "endpackage\n" +
           InitTop(InitAssertion(body));
  }
  if (place == "checker") {
    return "checker w(clk, clk1, clk2, f, e, a, b, c, d, g, v);\n" + items +
           "endchecker\n" + InitTop(kInitInstance);
  }
  return place + " w" + kInitPorts + ";\n" + items + "end" + place + "\n" +
         InitTop(kInitInstance);
}

struct Outcome {
  uint64_t passes;
  uint64_t fails;
  uint64_t failed_at;
  bool operator==(const Outcome&) const = default;
};

std::ostream& operator<<(std::ostream& os, const Outcome& outcome) {
  return os << outcome.passes << " passes, " << outcome.fails
            << " fails, the last at " << outcome.failed_at;
}

Outcome OutcomeIn(const std::string& place, const std::string& declarations,
                  const std::string& body) {
  SimFixture f;
  std::string out = RunCapture(InitPlaceSource(place, declarations, body), f);
  Outcome outcome{0, 0, 0};
  size_t at = 0;
  while (at < out.size()) {
    size_t end = out.find('\n', at);
    if (end == std::string::npos) end = out.size();
    std::string line = out.substr(at, end - at);
    if (line == "PASS") ++outcome.passes;
    if (line.starts_with("FAIL ")) {
      ++outcome.fails;
      outcome.failed_at = std::stoull(line.substr(5));
    }
    at = end + 1;
  }
  return outcome;
}

Outcome OutcomeOf(const std::string& locals, const std::string& body,
                  const std::string& implication = "|=>") {
  return OutcomeIn("module",
                   "  property p;\n" + locals + body + "  endproperty\n",
                   "f " + implication + " p");
}

TEST(LocalVariableInitialization,
     ACopyPerSemanticLeadingClockIsInitializedAtItsTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d == v);\n");
  EXPECT_EQ(p.passes, 10u);
  EXPECT_EQ(p.fails, 0u);
}

TEST(LocalVariableInitialization, TheSecondCopyReadsItsOwnClocksTick) {
  Outcome p = OutcomeOf("    logic v = e;\n",
                        "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
                        "    and\n"
                        "    (@(posedge clk2) c[*1:$] |-> d != v);\n");
  EXPECT_EQ(p.passes, 9u);
  EXPECT_EQ(p.fails, 1u);
  EXPECT_EQ(p.failed_at, 22u);
}

TEST(LocalVariableInitialization,
     ASingleLeadingClockInitializesAtItsFirstTick) {
  Outcome r = OutcomeOf("    logic u = e;\n",
                        "    @(posedge clk1) (a == u)[*1:$] |-> b;\n");
  EXPECT_EQ(r.passes, 10u);
  EXPECT_EQ(r.fails, 0u);
  Outcome r_ne = OutcomeOf("    logic u = e;\n",
                           "    @(posedge clk1) (a == u)[*1:$] |-> !b;\n");
  EXPECT_EQ(r_ne.fails, 1u);
  EXPECT_EQ(r_ne.failed_at, 18u);
}

TEST(LocalVariableInitialization,
     ASinglyClockedPropertyInitializesAtTheAttemptsBegin) {
  Outcome q =
      OutcomeOf("    logic w = e;\n", "    1'b1 ##1 (g == w);\n", "|->");
  EXPECT_EQ(q.passes, 10u);
  EXPECT_EQ(q.fails, 0u);
  Outcome q_ne =
      OutcomeOf("    logic w = e;\n", "    1'b1 ##1 (g != w);\n", "|->");
  EXPECT_EQ(q_ne.fails, 1u);
  EXPECT_EQ(q_ne.failed_at, 15u);
}

TEST(LocalVariableInitialization, ALaterLocalReadsTheCopyOfAnEarlierOne) {
  Outcome q = OutcomeOf("    logic w = e;\n    logic x = w;\n",
                        "    1'b1 ##1 (g == x);\n", "|->");
  EXPECT_EQ(q.passes, 10u);
  EXPECT_EQ(q.fails, 0u);
}

constexpr const char* kCountingDeclarations =
    "  property q; int w = v; 1 ##1 (v == w + 1); endproperty\n"
    "  sequence r; int w = v; 1 ##1 (v == w + 1); endsequence\n"
    "  sequence s; 1 ##1 r; endsequence\n"
    "  sequence rm; int w; (1, w = v) ##0 1 ##1 (v == w + 1); endsequence\n"
    "  sequence rx(y); int w = y; 1 ##1 (v == w + 1); endsequence\n"
    "  sequence ro; int w = v; 1 ##2 (v == w + 2); endsequence\n"
    "  sequence ri(local input int x); 1 ##1 (v == x + 1); endsequence\n"
    "  property qi(local input int x); 1 ##1 (v == x + 1); endproperty\n"
    "  sequence rio(local inout int x); 1 ##1 (v == x + 1); endsequence\n"
    "  property pio; int z; (1, z = v) ##0 rio(z); endproperty\n"
    "  sequence rf(local input int x); int w = x + 1; 1 ##1 (v == w); "
    "endsequence\n"
    "  sequence rule; @(posedge clk) 1 ##2 r; endsequence\n";

struct InitRow {
  const char* body;
  Outcome outcome;
};

constexpr InitRow kInitializedWithTheAttempt[] = {
    {"1 |=> q", {8, 0, 0}},
    {"1 |-> 1 ##1 1 |-> q", {8, 0, 0}},
    {"1 |-> nexttime q", {8, 0, 0}},
    {"1 |-> s_nexttime q", {8, 0, 0}},
    {"1 |-> r", {9, 0, 0}},
    {"1 |=> r", {8, 0, 0}},
    {"1 |-> 1 ##1 rm", {8, 0, 0}},
    {"1 |-> rx(v)", {9, 0, 0}},
    {"ro", {8, 0, 0}},
    {"1 |-> ri(v)", {9, 0, 0}},
    {"1 |-> 1 ##1 ri(v)", {8, 0, 0}},
    {"1 |=> ri(v)", {8, 0, 0}},
    {"1 |-> qi(v)", {9, 0, 0}},
    {"1 |=> qi(v)", {8, 0, 0}},
    {"pio", {9, 0, 0}}};

template <typename Rows>
void ExpectInitializedIn(const std::string& place, const Rows& rows) {
  for (const InitRow& row : rows) {
    SCOPED_TRACE(place + ": " + row.body);
    EXPECT_EQ(OutcomeIn(place, kCountingDeclarations, row.body), row.outcome);
  }
}

TEST(LocalVariableInitialization,
     EachInstanceInitializesItsLocalsWhenItsOwnAttemptBegins) {
  ExpectInitializedIn("module", kInitializedWithTheAttempt);
}

TEST(LocalVariableInitialization,
     DISABLED_ADeclaredLocalReadsTheValueOfALocalFormal) {
  EXPECT_EQ(OutcomeIn("module", kCountingDeclarations, "1 |-> rf(v)"),
            (Outcome{9, 0, 0}));
}

constexpr InitRow kInitializedAfterADelay[] = {
    {"1 |-> 1 ##1 r", {8, 0, 0}},
    {"1 |-> ##1 r", {8, 0, 0}},
    {"1 |-> 1[*2] ##0 r", {8, 0, 0}},
    {"1 |-> (1 ##1 r) or (0 ##1 1)", {8, 0, 0}},
    {"1 |-> (1 ##1 r) and (1 ##2 1)", {8, 0, 0}},
    {"1 |-> (1 ##1 r) intersect (1 ##2 1)", {8, 0, 0}},
    {"1 |-> s", {8, 0, 0}},
    {"rule.triggered", {7, 3, 25}},
    {"1 |-> 1 ##1 rx(v)", {8, 0, 0}}};

TEST(LocalVariableInitialization,
     DISABLED_ADeclaredLocalOfAnInstanceBegunAfterADelayTakesItsOwnTick) {
  ExpectInitializedIn("module", kInitializedAfterADelay);
}

constexpr const char* kInitPlaces[] = {"module",  "interface", "program",
                                       "checker", "package",   "generate"};

TEST(LocalVariableInitialization,
     DISABLED_AnInstanceBegunAfterADelayTakesItsOwnTickInEachPlace) {
  for (const char* place : kInitPlaces) {
    std::string body = std::string(place) == "package" ? "1 |-> 1 ##1 pk::rx(v)"
                                                       : "1 |-> 1 ##1 rx(v)";
    SCOPED_TRACE(place);
    EXPECT_EQ(OutcomeIn(place,
                        "  sequence rx(y); int w = y; 1 ##1 (v == w + 1); "
                        "endsequence\n",
                        body),
              (Outcome{8, 0, 0}));
  }
}

constexpr const char* kLeadingClockDeclarations =
    "  property por; logic v = e;\n"
    "    (@(posedge clk1) (a == v)[*1:$] |-> !b)\n"
    "    or\n"
    "    (@(posedge clk2) c[*1:$] |-> d == v);\n"
    "  endproperty\n"
    "  property pthree; int w = v;\n"
    "    (@(posedge clk1) 1 |-> w == 1)\n"
    "    and\n"
    "    (@(posedge clk2) 1 |-> w == 2)\n"
    "    and\n"
    "    (@(posedge clk) 1 |-> w == 1);\n"
    "  endproperty\n"
    "  property pat; int w = v;\n"
    "    @(posedge clk) 1 ##1 (w == 1) ##1 @(posedge clk1) 1;\n"
    "  endproperty\n"
    "  sequence sm; logic u = e; @(posedge clk1) (a == u) ##1 1; "
    "endsequence\n"
    "  property pformal(local input logic x);\n"
    "    (@(posedge clk1) (a == x)[*1:$] |-> b)\n"
    "    and\n"
    "    (@(posedge clk2) c[*1:$] |-> d == x);\n"
    "  endproperty\n"
    "  property pexplicit; logic v;\n"
    "    (@(posedge clk1) (1, v = e) ##0 (a == v)[*1:$] |-> b)\n"
    "    and\n"
    "    (@(posedge clk2) (1, v = e) ##0 c[*1:$] |-> d == v);\n"
    "  endproperty\n";

constexpr InitRow kLeadingClockCopies[] = {
    {"f |=> por", {10, 0, 0}},        {"f |=> pthree", {10, 0, 0}},
    {"f |=> pat", {10, 0, 0}},        {"f |=> sm", {10, 0, 0}},
    {"f |=> pformal(e)", {10, 0, 0}}, {"f |=> pexplicit", {10, 0, 0}}};

TEST(LocalVariableInitialization,
     EachSemanticLeadingClockInitializesItsCopyAtItsOwnTick) {
  for (const InitRow& row : kLeadingClockCopies) {
    SCOPED_TRACE(row.body);
    EXPECT_EQ(OutcomeIn("module", kLeadingClockDeclarations, row.body),
              row.outcome);
  }
}

constexpr const char* kFixedClockFormal =
    "  property p2(pa, pb, pc, pd, local input logic x);\n"
    "    (@(posedge clk1) (pa == x)[*1:$] |-> pb)\n"
    "    and\n"
    "    (@(posedge clk2) pc[*1:$] |-> pd == x);\n"
    "  endproperty\n";

TEST(LocalVariableInitialization,
     EachLeadingClocksCopyIsInitializedAtItsTickInEachPlace) {
  for (const char* place : kInitPlaces) {
    if (std::string(place) == "package") continue;
    SCOPED_TRACE(place);
    EXPECT_EQ(OutcomeIn(place, kFixedClockFormal, "f |=> p2(a, b, c, d, e)"),
              (Outcome{10, 0, 0}));
  }
}

constexpr const char* kTwoClockFormal =
    "  property p2(ck1, ck2, pa, pb, pc, pd, local input logic x);\n"
    "    (@(posedge ck1) (pa == x)[*1:$] |-> pb)\n"
    "    and\n"
    "    (@(posedge ck2) pc[*1:$] |-> pd == x);\n"
    "  endproperty\n";

TEST(LocalVariableInitialization,
     DISABLED_EachCopyIsInitializedAtTheTickOfAClockFormalInEachPlace) {
  for (const char* place : kInitPlaces) {
    std::string instance = std::string(place) == "package" ? "pk::p2" : "p2";
    SCOPED_TRACE(place);
    EXPECT_EQ(OutcomeIn(place, kTwoClockFormal,
                        "f |=> " + instance + "(clk1, clk2, a, b, c, d, e)"),
              (Outcome{10, 0, 0}));
  }
}

}  // namespace
