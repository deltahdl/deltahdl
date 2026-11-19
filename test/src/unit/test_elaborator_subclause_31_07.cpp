#include <gtest/gtest.h>

#include <array>
#include <string>
#include <utility>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConditionedTimingCheckElaboration, TimingCheckConditionBareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

constexpr std::array<const char*, 10> kTwoEventChecks = {
    "$setup({D}, {R}, 5);",        "$hold({R}, {D}, 5);",
    "$setuphold({R}, {D}, 5, 5);", "$recovery({R}, {D}, 5);",
    "$removal({R}, {D}, 5);",      "$recrem({R}, {D}, 5, 5);",
    "$skew({R}, {D}, 5);",         "$timeskew({R}, {D}, 5);",
    "$fullskew({R}, {D}, 5, 5);",  "$nochange({R}, {D}, 0, 0);",
};

constexpr std::array<const char*, 2> kOneEventChecks = {
    "$period({R}, 5);",
    "$width({R}, 5);",
};

void Substitute(std::string& text, const std::string& slot,
                const std::string& value) {
  const auto kAt = text.find(slot);
  if (kAt != std::string::npos) text.replace(kAt, slot.size(), value);
}

std::vector<std::string> ChecksConditionedBy(const std::string& condition) {
  std::vector<std::string> checks;
  for (const char* text : kTwoEventChecks) {
    std::string check = text;
    std::string on_reference = check;
    Substitute(on_reference, "{R}", "posedge clk &&& " + condition);
    Substitute(on_reference, "{D}", "d");
    checks.push_back(on_reference);
    Substitute(check, "{R}", "posedge clk");
    Substitute(check, "{D}", "d &&& " + condition);
    checks.push_back(check);
  }
  for (const char* text : kOneEventChecks) {
    std::string check = text;
    Substitute(check, "{R}", "posedge clk &&& " + condition);
    checks.push_back(check);
  }
  return checks;
}

std::string ModuleWithCheck(const std::string& decls,
                            const std::string& check) {
  return "module m(input d, input clk, input en, input a, input b);\n"
         "  " +
         decls +
         "\n"
         "  specify\n"
         "    " +
         check +
         "\n"
         "  endspecify\n"
         "endmodule\n";
}

TEST(ConditionedTimingCheckElaboration,
     SingleSignalConditionsAcceptedInEveryCheck) {
  for (const char* condition :
       {"en", "(en)", "~en", "(~en)", "en == 1'b0", "en === 1'b1", "en != 0",
        "en !== 1", "(en == 'b1)"}) {
    for (const std::string& check : ChecksConditionedBy(condition)) {
      ElabFixture f;
      ElaborateSrc(ModuleWithCheck("", check), f);
      EXPECT_FALSE(f.has_errors) << check;
    }
  }
}

TEST(ConditionedTimingCheckElaboration,
     DISABLED_ConditionCombiningSignalsRejectedInEveryCheck) {
  for (const char* condition :
       {"(a & b)", "(a && b)", "(a | b)", "(a || b)", "~(a & b)", "(a ^ b)",
        "(en == a)", "(en != a)", "(en === a)", "(en !== a)"}) {
    for (const std::string& check : ChecksConditionedBy(condition)) {
      ElabFixture f;
      ElaborateSrc(ModuleWithCheck("", check), f);
      EXPECT_TRUE(ReportedError(
          f.diag.Diagnostics(),
          "timing check condition combines more than one signal", 4, "31.7"))
          << check;
    }
  }
}

TEST(ConditionedTimingCheckElaboration, NetConditioningSignalsAccepted) {
  for (const auto& [decls, condition] :
       std::vector<std::pair<std::string, std::string>>{
           {"wire w;", "w"},
           {"tri w;", "w"},
           {"wire w;", "~w"},
           {"wire w;", "w == 1'b1"},
           {"wire [1:0] w;", "w"},
           {"", "en"},
       }) {
    ElabFixture f;
    ElaborateSrc(ModuleWithCheck(
                     decls, "$setup(d, posedge clk &&& " + condition + ", 5);"),
                 f);
    EXPECT_FALSE(f.has_errors) << decls << " " << condition;
  }
}

TEST(ConditionedTimingCheckElaboration,
     DISABLED_VariableConditioningSignalsRejected) {
  for (const auto& [decls, condition] :
       std::vector<std::pair<std::string, std::string>>{
           {"logic v;", "v"},
           {"reg v;", "v"},
           {"bit v;", "v"},
           {"logic v;", "~v"},
           {"logic v;", "v == 1'b1"},
           {"logic v;", "v === 1'b0"},
           {"logic [1:0] v;", "v"},
       }) {
    ElabFixture f;
    ElaborateSrc(ModuleWithCheck(
                     decls, "$setup(d, posedge clk &&& " + condition + ", 5);"),
                 f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "timing check conditioning signal 'v' is a variable, not a net", 4,
        "31.7"))
        << decls << " " << condition;
  }
}

}  // namespace
