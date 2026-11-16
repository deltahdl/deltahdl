#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_constraint_item_places.h"
#include "helpers_constraint_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kBody =
    "  rand bit [3:0] x, y, z;\n"
    "  rand bit [3:0] A[2];\n"
    "  function int id(int v); return v; endfunction\n"
    "  function int dbl(int v); return 2 * v; endfunction\n";

const char* const kScopeDecls =
    "  bit [3:0] x, y, z;\n"
    "  function automatic int id(int v); return v; endfunction\n"
    "  function automatic int dbl(int v); return 2 * v; endfunction\n";

std::string WithoutObject(std::string check) {
  for (std::size_t at = check.find("o."); at != std::string::npos;
       at = check.find("o.", at)) {
    check.erase(at, 2);
  }
  return check;
}

std::string HeldAt(ItemPlace place, const std::string& items,
                   const std::string& check) {
  switch (place) {
    case ItemPlace::kOutOfBlock:
      return CountHeld(Tally("", std::string(kBody) + "  constraint k;\n",
                             "constraint C::k { " + items + " }\n",
                             "o.randomize()", check));
    case ItemPlace::kInline:
      return HeldWith(kBody, items, check);
    case ItemPlace::kScope:
      return HeldInScopeOf(kScopeDecls,
                           "std::randomize(x, y, z) with { " + items + " }",
                           WithoutObject(check));
    default:
      return Held(std::string(kBody) + "  constraint k { " + items + " }\n",
                  check);
  }
}

TEST(FunctionsInConstraintCases, AResultFixesItsConsumerInEveryPlace) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(HeldAt(place, "y == 3; x == dbl(y);", "o.x == 6"), "16\n")
        << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases, APackageFunctionsResultFixesItsConsumer) {
  EXPECT_EQ(CountHeld("package p;\n"
                      "  function automatic int dbl(int v); return 2 * v; "
                      "endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  bit [3:0] x, y;\n"
                      "  int n, held = 0;\n"
                      "  initial begin\n"
                      "    for (n = 0; n < 16; n++)\n"
                      "      if (std::randomize(x, y) with { y == 3; x == "
                      "p::dbl(y); } && x == 6) held++;\n"
                      "    $display(\"%0d\", held);\n"
                      "  end\n"
                      "endmodule\n"),
            "16\n");
}

TEST(FunctionsInConstraintCases, AResultSelectsTheBranchOfAnIf) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(HeldAt(place, "y == 3; if (dbl(y) == 6) x == 1; else x == 2;",
                     "o.x == 1"),
              "16\n")
        << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases, AResultDecidesAnImplicationAntecedent) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(HeldAt(place,
                     "y == 3; dbl(y) == 6 -> x == 1; dbl(y) != 6 -> "
                     "x == 2;",
                     "o.x == 1"),
              "16\n")
        << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases, AResultFixesEachElementInAForeachBody) {
  for (ItemPlace place :
       {ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline}) {
    EXPECT_EQ(HeldAt(place, "y == 3; foreach (A[i]) A[i] == dbl(y) + i;",
                     "o.A[0] == 6 && o.A[1] == 7"),
              "16\n")
        << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases, AResultFixesTheValueOfASoftConstraint) {
  for (ItemPlace place :
       {ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline}) {
    EXPECT_EQ(HeldAt(place, "y == 3; soft x == dbl(y);", "o.x == 6"), "16\n")
        << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases,
     DISABLED_AResultFixesTheValueOfASoftConstraintInScopeRandomize) {
  EXPECT_EQ(HeldAt(ItemPlace::kScope, "y == 3; soft x == dbl(y);", "o.x == 6"),
            "16\n");
}

TEST(FunctionsInConstraintCases,
     DISABLED_ALowerSetFailingAfterTheHigherSetFailsTheCall) {
  for (ItemPlace place : kEveryItemPlace) {
    const std::string kOut = HeldAt(place, "x == id(y); x > 14;", "1");
    EXPECT_LT(std::stoi(kOut), 8) << ItemPlaceName(place);
  }
}

TEST(FunctionsInConstraintCases, TheArgumentIsSolvedFirstInEveryPlace) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(HeldAt(place, "y inside {2, 4, 8}; x <= id(y);",
                     "o.x <= o.y && o.y inside {2, 4, 8}"),
              "16\n")
        << ItemPlaceName(place);
  }
}

const char* const kCycle =
    "circular dependency in the implicit variable ordering of function "
    "arguments";
const char* const kPair =
    "  rand bit [3:0] a, b, c;\n"
    "  function int id(int v); return v; endfunction\n";

std::string CycleRun(const std::string& body, const std::string& after,
                     const std::string& call) {
  return "class C;\n" + body + "endclass\n" + after +
         "module t;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    $display(\"%0d\", " +
         call +
         ");\n"
         "  end\n"
         "endmodule\n";
}

void ExpectCycleReported(const std::string& src, const std::string& call) {
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), "0\n") << src;
  const std::string kHead = src.substr(0, src.find(call));
  const auto kLine =
      static_cast<uint32_t>(std::count(kHead.begin(), kHead.end(), '\n') + 1);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCycle, kLine, "18.5.11"))
      << src;
}

TEST(FunctionsInConstraintCases, DISABLED_ATwoVariableCycleIsAnError) {
  ExpectCycleReported(CycleRun(std::string(kPair) +
                                   "  constraint k { a < id(b); b < id(a); }\n",
                               "", "o.randomize()"),
                      "o.randomize()");
}

TEST(FunctionsInConstraintCases, DISABLED_AThreeVariableCycleIsAnError) {
  ExpectCycleReported(
      CycleRun(std::string(kPair) +
                   "  constraint k { a < id(b); b < id(c); c < id(a); }\n",
               "", "o.randomize()"),
      "o.randomize()");
}

TEST(FunctionsInConstraintCases, DISABLED_ACycleAcrossTwoBlocksIsAnError) {
  ExpectCycleReported(
      CycleRun(std::string(kPair) + "  constraint k1 { a < id(b); }\n"
                                    "  constraint k2 { b < id(a); }\n",
               "", "o.randomize()"),
      "o.randomize()");
  ExpectCycleReported(
      CycleRun(std::string(kPair) + "  constraint k1 { a < id(b); }\n"
                                    "  constraint k2;\n",
               "constraint C::k2 { b < id(a); }\n", "o.randomize()"),
      "o.randomize()");
}

TEST(FunctionsInConstraintCases, DISABLED_ACycleCompletedInlineIsAnError) {
  ExpectCycleReported(
      CycleRun(std::string(kPair) + "  constraint k1 { a < id(b); }\n", "",
               "o.randomize() with { b < id(a); }"),
      "o.randomize() with { b < id(a); }");
}

TEST(FunctionsInConstraintCases, DISABLED_ACycleInScopeRandomizeIsAnError) {
  const std::string kCall =
      "std::randomize(a, b) with { a < id(b); b < id(a); }";
  ExpectCycleReported(
      "module t;\n"
      "  bit [3:0] a, b;\n"
      "  function automatic int id(int v); return v; "
      "endfunction\n"
      "  initial $display(\"%0d\", " +
          kCall +
          ");\n"
          "endmodule\n",
      kCall);
}

TEST(FunctionsInConstraintCases, AnAcyclicChainIsSolvedWithoutAReport) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Tally("",
                             std::string(kPair) +
                                 "  constraint k { a <= id(b); b <= id(c); }\n",
                             "", "o.randomize()", "o.a <= o.b && o.b <= o.c"),
                       f),
            "16\n");
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("circular"), std::string::npos) << d.message;
  }
}

}  // namespace
