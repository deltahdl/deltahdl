#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "elaborator/concurrent_assert_action.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssertActionBlock, RejectsConcurrentAssertionStatements) {
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssert));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssume));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentCover));
}

TEST(AssertActionBlock, AllowsImmediateAssertions) {
  EXPECT_TRUE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kImmediateAssertion));
}

TEST(AssertActionBlock, AllowsOrdinaryStatements) {
  EXPECT_TRUE(
      ConcurrentAssertActionBlockAllows(ActionBlockStatementForm::kOther));
}

TEST(AssertActionBlock, AProceduralAssertsNestedAssertIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a1: assert property (a) else assert property (b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the action block of a concurrent assert or assume "
                            "statement may not include a concurrent assert, "
                            "assume, or cover statement",
                            4, "16.14.1"));
}

TEST(AssertActionBlock, AProceduralAssumesNestedCoverIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a2: assume property (a) cover property (b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the action block of a concurrent assert or assume "
                            "statement may not include a concurrent assert, "
                            "assume, or cover statement",
                            4, "16.14.1"));
}

TEST(AssertActionBlock, AnImmediateAssertionInTheActionBlockIsAllowed) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a1: assert property (a) else assert (b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kNestingReport =
    "the action block of a concurrent assert or assume statement may not "
    "include a concurrent assert, assume, or cover statement";

constexpr const char* kPlacementReport = "always or an initial procedure";

constexpr const char* kNestedConcurrent[] = {
    "assert property (@(posedge clk) b);",
    "assume property (@(posedge clk) b);", "cover property (@(posedge clk) b);",
    "cover sequence (@(posedge clk) b);"};

constexpr const char* kNestedImmediate[] = {
    "assert (b);",       "assume (b);",       "cover (b);",
    "assert #0 (b);",    "assume #0 (b);",    "cover #0 (b);",
    "assert final (b);", "assume final (b);", "cover final (b);"};

constexpr const char* kDirectives[] = {"assert", "assume"};

constexpr const char* kPositions[] = {"", "else "};

std::string Outer(const std::string& directive, const std::string& position,
                  const std::string& nested) {
  return "x1: " + directive + " property (@(posedge clk) a) " + position +
         nested;
}

std::string ProcedureIn(const std::string& place) {
  if (place == "program") return "initial ";
  if (place == "checker") return "always_ff @(posedge clk) ";
  return "always @(posedge clk) ";
}

std::string NestingSource(const std::string& place, const std::string& item) {
  std::string line = "  " + item + "\n";
  std::string top_signals = "  logic clk, a, b;\n";
  if (place == "module")
    return "module t;\n" + top_signals + line + "endmodule\n";
  if (place == "if generate") {
    return "module t;\n" + top_signals + "  if (1) begin : g\n" + line +
           "  end\nendmodule\n";
  }
  if (place == "for generate") {
    return "module t;\n" + top_signals +
           "  for (genvar i = 0; i < 2; i++) begin : gl\n" + line +
           "  end\nendmodule\n";
  }
  std::string header = place == "checker"
                           ? "checker w(clk, a, b);\n"
                           : place + " w(input logic clk, a, b);\n";
  return header + line + "end" + place + "\nmodule t;\n" + top_signals +
         "  w u(clk, a, b);\nendmodule\n";
}

::testing::AssertionResult NestingReportedAlone(const std::string& src) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  const auto& diags = f.diag.Diagnostics();
  for (const auto& diag : diags) {
    if (diag.message.find(kPlacementReport) != std::string::npos) {
      return ::testing::AssertionFailure()
             << "the placement rule was reported beside the nesting rule:\n"
             << src;
    }
  }
  ::testing::AssertionResult reported =
      ReportedError(diags, kNestingReport, LineHolding(src, "x1:"), "16.14.1");
  if (!reported) reported << "\nin\n" << src;
  return reported;
}

::testing::AssertionResult Accepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  if (f.has_errors) {
    return ::testing::AssertionFailure() << "a report met\n" << src;
  }
  return ::testing::AssertionSuccess();
}

template <size_t N>
std::vector<std::string> OuterForms(const char* const (&nested_list)[N]) {
  std::vector<std::string> forms;
  for (const char* directive : kDirectives) {
    for (const char* position : kPositions) {
      for (const char* nested : nested_list) {
        forms.push_back(Outer(directive, position, nested));
      }
    }
  }
  return forms;
}

TEST(AssertActionBlock,
     EachConcurrentStatementInAProceduralPassOrFailStatementIsReported) {
  for (const std::string& form : OuterForms(kNestedConcurrent)) {
    EXPECT_TRUE(NestingReportedAlone(
        NestingSource("module", ProcedureIn("module") + form)));
  }
}

constexpr const char* kDepths[] = {"begin % end",
                                   "if (b) %",
                                   "for (int i = 0; i < 2; i++) %",
                                   "fork % join",
                                   "case (b) 1'b1: % endcase",
                                   "assert (b) else %",
                                   "assert (b) %"};

constexpr const char* kModuleProcedures[] = {
    "always @(posedge clk) ", "initial ", "always_ff @(posedge clk) ",
    "always_comb ", "always_latch "};

std::string Wrapped(const std::string& depth, const std::string& nested) {
  std::string out = depth;
  out.replace(out.find('%'), 1, nested);
  return out;
}

std::vector<std::string> DepthForms() {
  std::vector<std::string> forms;
  for (const char* depth : kDepths) {
    for (const char* position : kPositions) {
      forms.push_back(
          Outer("assert", position, Wrapped(depth, kNestedConcurrent[0])));
      forms.push_back(
          Outer("assume", position, Wrapped(depth, kNestedConcurrent[3])));
    }
  }
  return forms;
}

TEST(AssertActionBlock, ANestedStatementAtAnyDepthInEachProcedureIsReported) {
  std::vector<std::string> forms = DepthForms();
  for (const char* procedure : kModuleProcedures) {
    for (const std::string& form : forms) {
      EXPECT_TRUE(
          NestingReportedAlone(NestingSource("module", procedure + form)));
    }
  }
}

template <size_t N>
void ExpectProceduralNestingReportedIn(const char* const (&places)[N]) {
  std::vector<std::string> forms = OuterForms(kNestedConcurrent);
  for (const char* place : places) {
    for (const std::string& form : forms) {
      EXPECT_TRUE(NestingReportedAlone(
          NestingSource(place, ProcedureIn(place) + form)));
    }
  }
}

constexpr const char* kDesignUnits[] = {"interface", "program", "checker"};

TEST(AssertActionBlock,
     AProceduralNestingIsReportedInAnInterfaceAProgramAndAChecker) {
  ExpectProceduralNestingReportedIn(kDesignUnits);
}

constexpr const char* kGenerateBlocks[] = {"if generate", "for generate"};

TEST(AssertActionBlock, DISABLED_AProceduralNestingIsReportedInAGenerateBlock) {
  ExpectProceduralNestingReportedIn(kGenerateBlocks);
}

constexpr const char* kEveryPlace[] = {
    "module", "interface", "program", "checker", "if generate", "for generate"};

TEST(AssertActionBlock,
     DISABLED_AModuleLevelNestingIsReportedUnderItsOwnRuleInEachPlace) {
  std::vector<std::string> forms = OuterForms(kNestedConcurrent);
  for (const char* place : kEveryPlace) {
    for (const std::string& form : forms) {
      EXPECT_TRUE(NestingReportedAlone(NestingSource(place, form)));
    }
  }
}

TEST(AssertActionBlock,
     EachImmediateAssertionInAnActionBlockIsAcceptedInEachPlace) {
  std::vector<std::string> forms = OuterForms(kNestedImmediate);
  for (const char* place : kEveryPlace) {
    for (const std::string& form : forms) {
      EXPECT_TRUE(Accepted(NestingSource(place, ProcedureIn(place) + form)));
      EXPECT_TRUE(Accepted(NestingSource(place, form)));
    }
  }
}

}  // namespace
