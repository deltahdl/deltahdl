#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct CheckerText {
  std::string formal;
  std::string body;
};

CheckerText Untyped(const std::string& body) { return {"x", body}; }

std::string Declaration(const CheckerText& checker) {
  return "checker ck(" + checker.formal +
         ", logic clk, logic d);\n  logic [1:0] v;\n  " + checker.body +
         "\nendchecker\n";
}

struct InstancePlace {
  std::string before;
  std::string after;
};

std::vector<InstancePlace> Places() {
  std::string signals = "  logic clk, b;\n  logic [1:0] a;\n";
  std::string top = "module m;\n" + signals;
  return {
      {top, "endmodule\n"},
      {"interface sub;\n" + signals,
       "endinterface\nmodule m;\n  sub s();\nendmodule\n"},
      {"program sub;\n" + signals,
       "endprogram\nmodule m;\n  sub s();\nendmodule\n"},
      {top + "  if (1) begin : g\n", "  end\nendmodule\n"},
      {top + "  always @(posedge clk) begin\n", "  end\nendmodule\n"},
      {"checker outer(logic [1:0] a, logic b, logic clk);\n",
       "endchecker\n" + top + "  outer o(a, b, clk);\nendmodule\n"},
  };
}

std::vector<std::string> Connections(const std::string& actual) {
  return {actual + ", clk, b", ".x(" + actual + "), .clk(clk), .d(b)"};
}

uint32_t LineAfter(const std::string& text) {
  return static_cast<uint32_t>(std::count(text.begin(), text.end(), '\n')) + 1;
}

const char* Message() {
  return "the actual of 'x' makes the flattened checker 'ck' illegal";
}

struct Source {
  std::string text;
  uint32_t line = 0;
};

std::vector<Source> Sources(const CheckerText& checker,
                            const std::string& actual) {
  std::vector<Source> sources;
  for (const InstancePlace& place : Places()) {
    std::string before = Declaration(checker);
    before += place.before;
    for (const std::string& connection : Connections(actual)) {
      std::string text = before;
      text += "  ck u(";
      text += connection;
      text += ");\n";
      text += place.after;
      sources.push_back({text, LineAfter(before)});
    }
  }
  return sources;
}

void ExpectLegal(const CheckerText& checker, const std::string& actual) {
  for (const Source& source : Sources(checker, actual)) {
    EXPECT_TRUE(ElabOk(source.text)) << source.text;
  }
}

void ExpectIllegal(const CheckerText& checker, const std::string& actual) {
  for (const Source& source : Sources(checker, actual)) {
    ElabFixture f;
    Elaborate(source.text, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), Message(), source.line, "17.3"))
        << source.text;
  }
}

void ExpectOnlyASignalIsLegal(const std::string& body,
                              const std::string& actual) {
  ExpectLegal(Untyped(body), "a");
  ExpectIllegal(Untyped(body), actual);
}

std::string Sequence() { return "a ##1 b"; }

std::string Property() { return "a |-> b"; }

std::vector<std::string> Events() {
  return {"posedge clk", "a or b", "posedge clk iff b"};
}

TEST(FlattenedChecker, ASequenceActualStandsInAPropertyExpression) {
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x |-> 1);"),
              Sequence());
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) 1 |-> x);"),
              Sequence());
}

TEST(FlattenedChecker, AnEventActualStandsInAClockingEvent) {
  for (const std::string& event : Events()) {
    ExpectLegal(Untyped("a1: assert property (@(x) d);"), event);
  }
}

TEST(FlattenedChecker, APropertyActualStandsAsTheAssertedProperty) {
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x);"), Property());
}

TEST(FlattenedChecker, APlainSignalIsLegalInAProcedure) {
  ExpectLegal(Untyped("always_ff @(posedge clk) v <= x;"), "a");
  ExpectLegal(Untyped("always_comb v = x;"), "a");
  ExpectLegal(Untyped("always_latch if (d) v <= x;"), "a");
  ExpectLegal(Untyped("initial assert #0 (x);"), "a");
}

TEST(FlattenedChecker, APlainSignalIsLegalInAContinuousAssignment) {
  ExpectLegal(Untyped("assign v = x;"), "a");
}

TEST(FlattenedChecker, APlainSignalIsLegalAsAnOperand) {
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x == 1);"), "a");
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x + 1);"), "a");
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x[0]);"), "a");
  ExpectLegal(Untyped("a1: assert property (@(posedge clk) x ##1 d);"), "a");
}

TEST(FlattenedChecker, DISABLED_ASequenceActualInAlwaysFfIsIllegal) {
  ExpectOnlyASignalIsLegal("always_ff @(posedge clk) v <= x;", Sequence());
}

TEST(FlattenedChecker, DISABLED_ASequenceActualInAlwaysCombIsIllegal) {
  ExpectOnlyASignalIsLegal("always_comb v = x;", Sequence());
}

TEST(FlattenedChecker, DISABLED_ASequenceActualInAlwaysLatchIsIllegal) {
  ExpectOnlyASignalIsLegal("always_latch if (d) v <= x;", Sequence());
}

TEST(FlattenedChecker, DISABLED_ASequenceActualInAnInitialProcedureIsIllegal) {
  ExpectOnlyASignalIsLegal("initial assert #0 (x);", Sequence());
}

TEST(FlattenedChecker,
     DISABLED_ASequenceActualInAContinuousAssignmentIsIllegal) {
  ExpectOnlyASignalIsLegal("assign v = x;", Sequence());
}

TEST(FlattenedChecker, DISABLED_ASequenceActualAsAnOperandIsIllegal) {
  ExpectOnlyASignalIsLegal("a1: assert property (@(posedge clk) x == 1);",
                           Sequence());
  ExpectOnlyASignalIsLegal("a1: assert property (@(posedge clk) x + 1);",
                           Sequence());
}

TEST(FlattenedChecker, DISABLED_ASelectedSequenceActualIsIllegal) {
  ExpectOnlyASignalIsLegal("a1: assert property (@(posedge clk) x[0]);",
                           Sequence());
}

TEST(FlattenedChecker, DISABLED_AnEventActualAsAnOperandIsIllegal) {
  for (const std::string& event : Events()) {
    ExpectIllegal(Untyped("a1: assert property (@(posedge clk) x == 1);"),
                  event);
  }
}

TEST(FlattenedChecker, DISABLED_AnEventActualInAnAssignmentIsIllegal) {
  for (const std::string& event : Events()) {
    ExpectIllegal(Untyped("always_ff @(posedge clk) v <= x;"), event);
    ExpectIllegal(Untyped("assign v = x;"), event);
  }
}

TEST(FlattenedChecker, DISABLED_APropertyActualInASequenceIsIllegal) {
  ExpectOnlyASignalIsLegal("a1: assert property (@(posedge clk) x ##1 d);",
                           Property());
}

TEST(FlattenedChecker, DISABLED_APropertyActualInAnAssignmentIsIllegal) {
  ExpectOnlyASignalIsLegal("always_ff @(posedge clk) v <= x;", Property());
  ExpectOnlyASignalIsLegal("assign v = x;", Property());
}

TEST(FlattenedChecker, ASequenceFormalStandsInAPropertyExpression) {
  ExpectLegal({"sequence x", "a1: assert property (@(posedge clk) x |-> 1);"},
              Sequence());
}

TEST(FlattenedChecker, APropertyFormalStandsAsTheAssertedProperty) {
  ExpectLegal({"property x", "a1: assert property (@(posedge clk) x);"},
              Property());
}

TEST(FlattenedChecker, DISABLED_AnAssignedSequenceFormalIsIllegal) {
  ExpectIllegal({"sequence x", "always_ff @(posedge clk) v <= x;"}, Sequence());
  ExpectIllegal({"sequence x", "assign v = x;"}, Sequence());
}

TEST(FlattenedChecker, DISABLED_AnAssignedPropertyFormalIsIllegal) {
  ExpectIllegal({"property x", "always_ff @(posedge clk) v <= x;"}, Property());
  ExpectIllegal({"property x", "assign v = x;"}, Property());
}

std::string PassedDown(const std::string& body, const std::string& actual) {
  return "checker outer(x, logic clk, logic d); ck u(x, clk, d); endchecker "
         "module m; logic clk, b; logic [1:0] a; outer o(" +
         actual + ", clk, b); endmodule\n" + Declaration(Untyped(body));
}

TEST(FlattenedChecker, ASequenceActualPassedDownToAnAntecedentIsLegal) {
  EXPECT_TRUE(ElabOk(
      PassedDown("a1: assert property (@(posedge clk) x |-> 1);", Sequence())));
}

TEST(FlattenedChecker, ASignalPassedDownToAProcedureIsLegal) {
  EXPECT_TRUE(ElabOk(PassedDown("always_ff @(posedge clk) v <= x;", "a")));
}

TEST(FlattenedChecker,
     DISABLED_ASequenceActualPassedDownToAProcedureIsIllegal) {
  ElabFixture f;
  Elaborate(PassedDown("always_ff @(posedge clk) v <= x;", Sequence()), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), Message(), 1, "17.3"));
}

}  // namespace
