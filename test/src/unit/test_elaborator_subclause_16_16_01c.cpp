#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct Verdict {
  const char* statement;
  bool reported;
};

constexpr const char* kNoUniqueClock =
    "the property has no unique semantic leading clock";

constexpr const char* kModuleHead =
    "module m(input logic a, b, c, clk, clk2);\n"
    "  event e1, e2;\n"
    "  property pp(event ev); a and @(ev) b; endproperty\n"
    "  property pq(event c1, event c2); @(c1) a and @(c2) b; endproperty\n"
    "  clocking cb1 @(posedge clk); endclocking\n"
    "  clocking cb2 @(posedge clk2); endclocking\n";

uint32_t LinesIn(const std::string& text) {
  uint32_t lines = 0;
  for (char ch : text) {
    if (ch == '\n') ++lines;
  }
  return lines;
}

void ExpectVerdictsIn(const std::string& head, const std::string& tail,
                      std::initializer_list<Verdict> rows,
                      const char* message = kNoUniqueClock,
                      const char* subclause = "16.16.1") {
  std::string src = head;
  std::vector<uint32_t> lines;
  uint32_t line = LinesIn(head) + 1;
  for (const Verdict& row : rows) {
    src.append("    ").append(row.statement).append("\n");
    lines.push_back(line++);
  }
  src += tail;
  ElabFixture f;
  Elaborate(src, f);
  size_t i = 0;
  for (const Verdict& row : rows) {
    if (row.reported) {
      EXPECT_TRUE(
          ReportedError(f.diag.Diagnostics(), message, lines[i], subclause))
          << row.statement;
    } else {
      EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), lines[i]))
          << row.statement;
    }
    ++i;
  }
}

void ExpectVerdicts(std::initializer_list<Verdict> rows) {
  ExpectVerdictsIn(kModuleHead, "endmodule\n", rows);
}

TEST(UniqueLeadingClockElaboration, AndAndOrUnionTheirOperandsClocks) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) a and @(posedge clk2) b);", true},
      {"assert property (@(posedge clk) a or @(posedge clk2) b);", true},
      {"assert property (@(posedge clk) a and @(posedge clk) b);", false},
      {"assert property (@(posedge clk) a or @(posedge clk) b);", false},
  });
}

TEST(UniqueLeadingClockElaboration,
     AParenthesizedOrNegatedPropertyOverOneClockIsUnique) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) (a and @(posedge clk) b));", false},
      {"assert property (@(posedge clk) not (a and @(posedge clk) b));", false},
  });
}

TEST(UniqueLeadingClockElaboration,
     DISABLED_AParenthesizedOrNegatedPropertyKeepsItsSet) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) (a and @(posedge clk2) b));", true},
      {"assert property ((@(posedge clk) a and @(posedge clk2) b));", true},
      {"assert property (@(posedge clk) ((a and @(posedge clk2) b)));", true},
      {"assert property (@(posedge clk) not (a and @(posedge clk2) b));", true},
      {"assert property (@(posedge clk) not (a and (@(posedge clk2) b)));",
       true},
      {"assert property (@(posedge clk) not not (a and @(posedge clk2) b));",
       true},
      {"assert property (@(posedge clk) (not (a and @(posedge clk2) b)));",
       true},
      {"assert property (@(posedge clk) disable iff (c) "
       "(a and @(posedge clk2) b));",
       true},
      {"assert property (@(posedge clk) (pp(posedge clk2)));", true},
  });
}

TEST(UniqueLeadingClockElaboration, ADisableIffKeepsItsOperandsSet) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) disable iff (c) "
       "a and @(posedge clk2) b);",
       true},
      {"assert property (@(posedge clk) disable iff (c) "
       "a and @(posedge clk) b);",
       false},
  });
}
TEST(UniqueLeadingClockElaboration, AsynchronousAbortsKeepTheirOperandsSet) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) accept_on (c) "
       "a and @(posedge clk2) b);",
       true},
      {"assert property (@(posedge clk) reject_on (c) "
       "a and @(posedge clk2) b);",
       true},
      {"assert property (@(posedge clk) accept_on (c) "
       "a and @(posedge clk) b);",
       false},
      {"assert property (@(posedge clk) reject_on (c) "
       "a and @(posedge clk) b);",
       false},
  });
}

TEST(UniqueLeadingClockElaboration, AnImplicationTakesItsAntecedentsClock) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) a |-> @(posedge clk2) b);", false},
      {"assert property (@(posedge clk) a |=> @(posedge clk2) b);", false},
      {"assert property (@(posedge clk) @(posedge clk2) a |-> b);", false},
      {"assert property (@(posedge clk) (@(posedge clk2) a |-> b) and b);",
       true},
  });
}

TEST(UniqueLeadingClockElaboration, StrongAndWeakTakeTheSequencesClock) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) strong(@(posedge clk2) a ##1 b) "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) weak(@(posedge clk2) a ##1 b) "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) weak(@(posedge clk2) a) and b);", true},
      {"assert property (@(posedge clk) strong(@(posedge clk2) a) and b);",
       true},
  });
}

TEST(UniqueLeadingClockElaboration, ASequenceOperandHasItsLeadingClock) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) (@(posedge clk2) a ##1 b) "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) (@(posedge clk2) a ##0 b) "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) ((@(posedge clk2) a)) "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) (@(posedge clk2) a ##1 "
       "@(posedge clk) b) and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) (@(posedge clk2) a ##1 b) and b);",
       true},
  });
}

TEST(UniqueLeadingClockElaboration, OperatorsWhoseSetIsInheritedAreUnique) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) if (c) a and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) if (c) a and @(posedge clk2) b "
       "else b);",
       false},
      {"assert property (@(posedge clk) case (c) 1'b1: a and @(posedge clk2) "
       "b; default: b; endcase);",
       false},
      {"assert property (@(posedge clk) nexttime (a and @(posedge clk2) b));",
       false},
      {"assert property (@(posedge clk) always (a and @(posedge clk2) b));",
       false},
      {"assert property (@(posedge clk) s_eventually "
       "(a and @(posedge clk2) b));",
       false},
      {"assert property (@(posedge clk) (a and @(posedge clk2) b) until b);",
       false},
      {"assert property (@(posedge clk) (a and @(posedge clk2) b) "
       "until_with b);",
       false},
      {"assert property (@(posedge clk) sync_accept_on (c) "
       "a and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) sync_reject_on (c) "
       "a and @(posedge clk2) b);",
       false},
  });
}

TEST(UniqueLeadingClockElaboration, AClockOverAClockedSetLeavesItOut) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) @(posedge clk2) a "
       "and @(posedge clk2) b);",
       false},
      {"assert property (@(posedge clk) @(posedge clk2) a "
       "and @(posedge clk) b);",
       true},
  });
}

TEST(UniqueLeadingClockElaboration, AnInstanceWithTwoClocksAfterSubstitution) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) pp(posedge clk2));", true},
      {"assert property (pq(posedge clk, posedge clk2));", true},
      {"assert property (@(posedge clk) not pp(posedge clk2));", true},
  });
}

TEST(UniqueLeadingClockElaboration, DISABLED_AnInstanceMadeUniqueByItsActuals) {
  ExpectVerdicts({
      {"assert property (@(posedge clk) pp(posedge clk));", false},
      {"assert property (pq(posedge clk, posedge clk));", false},
  });
}

TEST(UniqueLeadingClockElaboration, IdenticalClocksAreTheSameEventExpression) {
  ExpectVerdicts({
      {"assert property (@e1 a and @e2 b);", true},
      {"assert property (@e1 a and @(e2) b);", true},
      {"assert property (@e1 a and @e1 b);", false},
      {"assert property (@(posedge clk iff c) a and @(posedge clk iff c) b);",
       false},
      {"assert property (@(posedge clk) a and @(edge clk) b);", true},
      {"assert property (@(clk) a and @(posedge clk) b);", true},
      {"assert property (@(posedge clk or negedge clk) a "
       "and @(posedge clk or negedge clk) b);",
       false},
      {"assert property (@(cb1) a and @(cb2) b);", true},
      {"assert property (@(cb1) a and @(cb1) b);", false},
  });
}

TEST(UniqueLeadingClockElaboration,
     DISABLED_AnIffGuardOnOneEventOnlyIsDistinct) {
  ExpectVerdicts({
      {"assert property (@(posedge clk iff c) a and @(posedge clk) b);", true},
  });
}

TEST(UniqueLeadingClockElaboration, EachStatementKindNeedsAUniqueClock) {
  ExpectVerdicts({
      {"assume property (@(posedge clk) a and @(posedge clk2) b);", true},
      {"cover property (@(posedge clk) a and @(posedge clk2) b);", true},
      {"restrict property (@(posedge clk) a and @(posedge clk) b);", false},
      {"cover sequence (@(posedge clk) a ##1 @(posedge clk2) b);", false},
  });
}

TEST(UniqueLeadingClockElaboration,
     DISABLED_EachStatementKindNeedsAUniqueClockWhenParenthesized) {
  ExpectVerdicts({
      {"assume property (@(posedge clk) (a and @(posedge clk2) b));", true},
      {"cover property (@(posedge clk) (a and @(posedge clk2) b));", true},
      {"restrict property (@(posedge clk) a and @(posedge clk2) b);", true},
  });
}

constexpr const char* kDefaultClockingHead =
    "module m(input logic a, b, c, clk, clk2);\n"
    "  default clocking dc @(posedge clk); endclocking\n"
    "  property q1; $rose(a) |-> ##[1:5] b; endproperty\n"
    "  property q5; @(negedge clk) b[*3] |=> !b; endproperty\n"
    "  property q6; q1 and q5; endproperty\n";

TEST(UniqueLeadingClockElaboration,
     UnderADefaultClockingTheDefaultIsInherited) {
  ExpectVerdictsIn(kDefaultClockingHead, "endmodule\n",
                   {
                       {"a5: assert property (q6);", true},
                       {"a6: assert property ($fell(c) |=> q6);", false},
                       {"assert property (a and @(posedge clk2) b);", true},
                       {"assert property ((a and @(posedge clk) b));", false},
                   });
}

TEST(UniqueLeadingClockElaboration,
     DISABLED_UnderADefaultClockingAParenthesizedSetIsKept) {
  ExpectVerdictsIn(
      kDefaultClockingHead, "endmodule\n",
      {
          {"assert property ((a and @(posedge clk2) b));", true},
          {"assert property (not (q1 and @(negedge clk) b));", true},
      });
}

constexpr const char* kInferredReport =
    "a multiclocked property may not take a contextually inferred "
    "leading clocking event";

constexpr const char* kInferringHead =
    "module m(input logic a, b, c, clk, clk2);\n"
    "  always @(posedge clk) begin\n";

TEST(UniqueLeadingClockElaboration, AnInferredClockIsInherited) {
  ExpectVerdictsIn(kInferringHead, "  end\nendmodule\n",
                   {
                       {"assert property (a and @(posedge clk2) b);", true},
                       {"assert property ((a and @(posedge clk) b));", false},
                   },
                   kInferredReport, "16.16");
}

TEST(UniqueLeadingClockElaboration,
     DISABLED_AnInferredClockIsInheritedThroughParentheses) {
  ExpectVerdictsIn(
      kInferringHead, "  end\nendmodule\n",
      {
          {"assert property ((a and @(posedge clk2) b));", true},
          {"assert property (not (a and @(posedge clk2) b));", true},
      },
      kInferredReport, "16.16");
}

constexpr const char* kTopOfPlaced =
    "module top;\n"
    "  logic a, b, c, clk, clk2;\n"
    "  w u(a, b, c, clk, clk2);\n"
    "endmodule\n";

struct Place {
  const char* head;
  std::string tail;
};

std::vector<Place> Places() {
  return {
      {"interface w(input logic a, b, c, clk, clk2);\n",
       std::string("endinterface\n") + kTopOfPlaced},
      {"program w(input logic a, b, c, clk, clk2);\n",
       std::string("endprogram\n") + kTopOfPlaced},
      {"checker w(logic a, b, c, clk, clk2);\n",
       std::string("endchecker\n") + kTopOfPlaced},
      {"module m(input logic a, b, c, clk, clk2);\n  if (1) begin : g\n",
       "  end\nendmodule\n"},
      {"module m(input logic a, b, c, clk, clk2);\n  initial begin\n",
       "  end\nendmodule\n"},
      {"module m(input logic a, b, c, clk, clk2);\n"
       "  always @(posedge clk) begin\n",
       "  end\nendmodule\n"},
  };
}

TEST(UniqueLeadingClockElaboration, EachPlaceNeedsAUniqueClock) {
  for (const Place& place : Places()) {
    ExpectVerdictsIn(
        place.head, place.tail,
        {
            {"assert property (@(posedge clk) a and @(posedge clk2) b);", true},
            {"assert property (@(posedge clk) a and @(posedge clk) b);", false},
        });
  }
}

TEST(UniqueLeadingClockElaboration, DISABLED_EachPlaceKeepsAParenthesizedSet) {
  for (const Place& place : Places()) {
    ExpectVerdictsIn(
        place.head, place.tail,
        {
            {"assert property (@(posedge clk) (a and @(posedge clk2) b));",
             true},
        });
  }
}

TEST(UniqueLeadingClockElaboration, ACheckersEventFormalsAreDistinctClocks) {
  ExpectVerdictsIn("checker w(event e1, event e2, logic a, b);\n",
                   "endchecker\n"
                   "module top;\n"
                   "  logic a, b, clk, clk2;\n"
                   "  w u(posedge clk, posedge clk2, a, b);\n"
                   "endmodule\n",
                   {
                       {"assert property (@e1 a and @e2 b);", true},
                       {"assert property (@e1 a and @e1 b);", false},
                   });
}

}  // namespace
