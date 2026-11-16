#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_constraint_item_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct GuardChecks {
  const char* first;
  const char* second;
};

constexpr GuardChecks kTenChecks = {"x + y == 10", "!(x < y) || x + y == 10"};

const char* const kUnconditional = "32 1 1\n";
const char* const kConditional = "32 0 1\n";
const char* const kEliminated = "32 0 0\n";
const char* const kFailed = "0 1 1\n";

std::string Qualified(const std::string& text, const std::string& prefix) {
  std::string out;
  for (std::size_t i = 0; i < text.size(); ++i) {
    const char kC = text[i];
    const bool kStarts =
        (kC == 'x' || kC == 'y' || kC == 'a' || kC == 'b' || kC == 'h') &&
        (i == 0 || (!std::isalnum(static_cast<unsigned char>(text[i - 1])) &&
                    text[i - 1] != '.' && text[i - 1] != '_')) &&
        (i + 1 == text.size() ||
         (!std::isalnum(static_cast<unsigned char>(text[i + 1])) &&
          text[i + 1] != '_'));
    if (kStarts) out += prefix;
    out += kC;
  }
  return out;
}

std::string Tally(const std::string& call, const GuardChecks& checks,
                  const std::string& prefix) {
  return "    for (n = 0; n < 32; n++)\n"
         "      if (" +
         call +
         ") begin\n"
         "        ok++;\n"
         "        if (" +
         Qualified(checks.first, prefix) +
         ") first++;\n"
         "        if (" +
         Qualified(checks.second, prefix) +
         ") second++;\n"
         "      end\n"
         "    $display(\"%0d %0d %0d\", ok, first == ok, second == ok);\n"
         "  end\n"
         "endmodule\n";
}

const char* const kCounters = "  int n, ok = 0, first = 0, second = 0;\n";

std::string GuardSource(ItemPlace place, const std::string& item,
                        const std::string& setup, const GuardChecks& checks) {
  const std::string kHandle = "class D; int x; endclass\n";
  if (place == ItemPlace::kScope) {
    return kHandle +
           "module t;\n"
           "  bit [3:0] x, y;\n"
           "  D a, b;\n"
           "  D h[2];\n" +
           kCounters + "  initial begin\n" + setup +
           Tally("std::randomize(x, y) with { " + item + " }", checks, "");
  }
  std::string head = kHandle +
                     "class C;\n"
                     "  rand bit [3:0] x, y;\n"
                     "  D a, b;\n"
                     "  D h[2];\n";
  std::string call = "o.randomize()";
  if (place == ItemPlace::kClassBlock) {
    head += "  constraint c1 { " + item + " }\nendclass\n";
  } else if (place == ItemPlace::kOutOfBlock) {
    head += "  constraint c1;\nendclass\nconstraint C::c1 { " + item + " }\n";
  } else {
    head += "endclass\n";
    call = "o.randomize() with { " + item + " }";
  }
  return head + "module t;\n" + kCounters +
         "  initial begin\n"
         "    static C o = new;\n" +
         Qualified(setup, "o.") + Tally(call, checks, "o.");
}

std::string GuardRun(ItemPlace place, const std::string& item,
                     const std::string& setup,
                     const GuardChecks& checks = kTenChecks) {
  SimFixture f;
  return RunCapture(GuardSource(place, item, setup, checks), f);
}

const char* const kGuardError = "a constraint guard evaluates to an error";

void ExpectGuardErrorReported(ItemPlace place, const std::string& item,
                              const std::string& setup) {
  SimFixture f;
  const std::string kSrc = GuardSource(place, item, setup, kTenChecks);
  EXPECT_EQ(RunCapture(kSrc, f), kFailed) << ItemPlaceName(place);
  const std::string kHead = kSrc.substr(0, kSrc.find(item));
  const auto kLine =
      static_cast<uint32_t>(std::count(kHead.begin(), kHead.end(), '\n') + 1);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kGuardError, kLine, "18.5.12"))
      << ItemPlaceName(place) << ": " << item;
}

const char* const kAnyDisjunct =
    "(x < y || a.x > b.x || a.x == 5) -> x + y == 10;";
const char* const kEveryConjunct =
    "(x < y && a.x > b.x && a.x == 5) -> x + y == 10;";
const char* const kNested =
    "(x < y && (a.x > b.x || a.x == 5)) -> x + y == 10;";
const char* const kNegated = "!(a.x == 5) -> x + y == 10;";
const char* const kIfElse = "if (a.x == 5) x + y == 10; else x + y == 3;";
constexpr GuardChecks kBranchChecks = {"x + y == 10", "x + y == 3"};

const char* const kOnlyA = "    a = new;\n    a.x = ";
std::string OnlyA(int ax) {
  return std::string(kOnlyA) + std::to_string(ax) + ";\n";
}
std::string Both(int ax, int bx) {
  return OnlyA(ax) + "    b = new;\n    b.x = " + std::to_string(bx) + ";\n";
}

TEST(ConstraintGuardCases, EveryDisjunctFalseGivesTheConditionalConstraint) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kAnyDisjunct, Both(10, 20)), kConditional)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, ATrueDisjunctGivesTheUnconditionalConstraint) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kAnyDisjunct, OnlyA(5)), kUnconditional)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, ANullHandleInAnyFormOfGuardFailsTheCall) {
  for (ItemPlace place : kEveryItemPlace) {
    for (const char* item :
         {kAnyDisjunct, kEveryConjunct, kNested, kNegated, kIfElse}) {
      EXPECT_EQ(GuardRun(place, item, ""), kFailed)
          << ItemPlaceName(place) << ": " << item;
    }
  }
}

TEST(ConstraintGuardCases, AFalseConjunctEliminatesTheConstraint) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kEveryConjunct, OnlyA(6)), kEliminated)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, EveryConjunctTrueGivesTheConditionalConstraint) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kEveryConjunct, Both(5, 2)), kConditional)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AnErrorOrTrueOperandIsSiftedToTrue) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kNested, OnlyA(5)), kConditional)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, kNested, Both(5, 2)), kConditional)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AnErrorOrFalseOperandFailsTheCall) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kNested, OnlyA(8)), kFailed)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, TheNegationOfFalseOrTrueSwapsTheOutcome) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kNegated, OnlyA(4)), kUnconditional)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, kNegated, OnlyA(5)), kEliminated)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AnIfElseGuardSelectsItsBranch) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kIfElse, OnlyA(5), kBranchChecks), "32 1 0\n")
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, kIfElse, OnlyA(4), kBranchChecks), "32 0 1\n")
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, DISABLED_AnErrorGuardReportsAnError) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectGuardErrorReported(place, kAnyDisjunct, "");
    ExpectGuardErrorReported(place, kEveryConjunct, "");
    ExpectGuardErrorReported(place, kNested, OnlyA(8));
    ExpectGuardErrorReported(place, kNegated, "");
    ExpectGuardErrorReported(place, kIfElse, "");
  }
}

const char* const kElementGuard = "foreach (h[i]) (h[i].x == 1) -> x == 2;";
constexpr GuardChecks kTwoChecks = {"x == 2", "x == 2"};

TEST(ConstraintGuardCases, DISABLED_AForeachGuardReadingANullElementFails) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kElementGuard,
                       "    h[0] = new;\n    h[0].x = 1;\n", kTwoChecks),
              kFailed)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AForeachGuardOverPresentElementsHolds) {
  for (ItemPlace place :
       {ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline}) {
    EXPECT_EQ(GuardRun(place, kElementGuard,
                       "    h[0] = new;\n    h[0].x = 0;\n"
                       "    h[1] = new;\n    h[1].x = 1;\n",
                       kTwoChecks),
              "32 1 1\n")
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases,
     DISABLED_AForeachGuardOverPresentElementsHoldsInScopeRandomize) {
  EXPECT_EQ(GuardRun(ItemPlace::kScope, kElementGuard,
                     "    h[0] = new;\n    h[0].x = 0;\n"
                     "    h[1] = new;\n    h[1].x = 1;\n",
                     kTwoChecks),
            "32 1 1\n");
}

TEST(ConstraintGuardCases, TwoHandlesComparedDecideTheGuard) {
  const std::string kSame = "    a = new;\n    b = a;\n";
  const std::string kDistinct = "    a = new;\n    b = new;\n";
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, "(a == b) -> x + y == 10;", kSame),
              kUnconditional)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, "(a == b) -> x + y == 10;", kDistinct),
              kEliminated)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, "(a != b) -> x + y == 10;", kDistinct),
              kUnconditional)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, "(a != b) -> x + y == 10;", kSame), kEliminated)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AConstantGuardImposesOrEliminates) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, "1 -> x + y == 10;", ""), kUnconditional)
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, "0 -> x + y == 10;", ""), kEliminated)
        << ItemPlaceName(place);
  }
}

TEST(ConstraintGuardCases, AnIfElseOverANullHandleTakesEitherBranch) {
  constexpr GuardChecks kValueChecks = {"x == 3", "x == 7"};
  const char* const kItem = "if (a != null) x == a.x; else x == 7;";
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(GuardRun(place, kItem, "", kValueChecks), "32 0 1\n")
        << ItemPlaceName(place);
    EXPECT_EQ(GuardRun(place, kItem, OnlyA(3), kValueChecks), "32 1 0\n")
        << ItemPlaceName(place);
  }
}

}  // namespace
