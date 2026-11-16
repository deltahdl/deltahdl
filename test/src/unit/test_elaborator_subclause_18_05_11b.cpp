#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_constraint_item_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kMethods =
    "rand bit [3:0] x, y; rand bit [3:0] A[2]; int cnt; "
    "constraint x_c { x >= 0; } "
    "function int fo(output bit [3:0] a); a = 1; return 1; endfunction "
    "function int fi(inout bit [3:0] a); return a; endfunction "
    "function int fr(ref bit [3:0] a); return a; endfunction "
    "function int fc(const ref bit [3:0] a); return a; endfunction "
    "function int fv(bit [3:0] a); return a; endfunction "
    "function int fm(bit [3:0] a); this.rand_mode(0); return a; endfunction "
    "function int fk(bit [3:0] a); x_c.constraint_mode(0); return a; "
    "endfunction "
    "function int fs(bit [3:0] a); cnt = cnt + 1; return a; endfunction "
    "function int fp(bit [3:0] a); int t; t = a + cnt; return t; endfunction "
    "function int fn(bit [3:0] a); return fs(a); endfunction "
    "function int fl(bit [3:0] a); static int s = 0; s++; return a + s; "
    "endfunction";

const char* const kScopeFunctions =
    "bit [3:0] x, y; int cnt; H h = new; "
    "function automatic int fo(output bit [3:0] a); a = 1; return 1; "
    "endfunction "
    "function automatic int fi(inout bit [3:0] a); return a; endfunction "
    "function automatic int fr(ref bit [3:0] a); return a; endfunction "
    "function automatic int fc(const ref bit [3:0] a); return a; endfunction "
    "function automatic int fv(bit [3:0] a); return a; endfunction "
    "function automatic int fm(bit [3:0] a); h.rand_mode(0); return a; "
    "endfunction "
    "function automatic int fk(bit [3:0] a); h.k.constraint_mode(0); return a; "
    "endfunction "
    "function automatic int fs(bit [3:0] a); cnt = cnt + 1; return a; "
    "endfunction "
    "function automatic int fp(bit [3:0] a); int t; t = a + cnt; return t; "
    "endfunction "
    "function int fl(bit [3:0] a); static int s = 0; s++; return a + s; "
    "endfunction "
    "function int fq(bit [3:0] a); int t; t = a; return t; endfunction";

const char* const kHandleClass =
    "class H; rand int v; constraint k { v > 0; } endclass";

constexpr ItemPlace kClassPlaces[] = {ItemPlace::kClassBlock,
                                      ItemPlace::kOutOfBlock};
constexpr ItemPlace kObjectPlaces[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline};

std::string CallIn(ItemPlace place, const std::string& item) {
  if (place == ItemPlace::kScope) {
    return ScopeItemIn(kScopeFunctions, "x, y", item, kHandleClass);
  }
  return ItemIn(place, kMethods, item, kHandleClass);
}

std::string Direction(const std::string& name) {
  return "function '" + name +
         "' is called in a constraint, so each of its arguments must be an "
         "input or a const ref";
}

std::string Mode(const std::string& name) {
  return "function '" + name +
         "' used in a constraint cannot modify the constraints by calling "
         "rand_mode or constraint_mode";
}

std::string SideEffect(const std::string& name) {
  return "function '" + name +
         "' used in a constraint shall have no side effect and keep no state "
         "from one call to the next";
}

void ExpectCallReport(ItemPlace place, const std::string& item,
                      const std::string& message, const char* subclause) {
  ElabFixture f;
  ElabOk(CallIn(place, item), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 6, subclause))
      << ItemPlaceName(place) << ": " << item;
}

void ExpectCallReport(ItemPlace place, const std::string& item,
                      const std::string& message) {
  ExpectCallReport(place, item, message, "18.5.11");
}

void ExpectCallAccepted(ItemPlace place, const std::string& item) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(CallIn(place, item), f))
      << ItemPlaceName(place) << ": " << item;
}

std::string Use(const std::string& form, const std::string& call) {
  std::string text = form;
  text.replace(text.find('@'), 1, call);
  return text;
}

const char* const kConstructs[] = {"x == @;",
                                   "if (@ > 0) x == 1;",
                                   "if (y > 0) x == @; else x == 0;",
                                   "if (y > 0) x == 0; else x == @;",
                                   "@ > 0 -> x == 1;",
                                   "y > 0 -> x == @;",
                                   "foreach (A[i]) A[i] == @;",
                                   "x inside {@, 3};",
                                   "soft x == @;"};

const char* const kScopeConstructs[] = {"x == @;", "if (@ > 0) x == 1;",
                                        "y > 0 -> x == @;", "x inside {@, 3};",
                                        "soft x == @;"};

TEST(FunctionsInConstraintCases,
     AnOutputInoutOrRefFormalIsRejectedInEveryConstructOfAClassConstraint) {
  for (ItemPlace place : kClassPlaces) {
    for (const char* form : kConstructs) {
      ExpectCallReport(place, Use(form, "fo(y)"), Direction("fo"));
      ExpectCallReport(place, Use(form, "fi(y)"), Direction("fi"));
      ExpectCallReport(place, Use(form, "fr(y)"), Direction("fr"));
    }
  }
}

TEST(FunctionsInConstraintCases, AnInputOrConstRefFormalIsAcceptedEverywhere) {
  for (ItemPlace place : kObjectPlaces) {
    for (const char* form : kConstructs) {
      ExpectCallAccepted(place, Use(form, "fv(y)"));
      ExpectCallAccepted(place, Use(form, "fc(y)"));
    }
    ExpectCallAccepted(place, "x dist {fv(y) := 1, fc(y) :/ 2};");
  }
  for (const char* form : kScopeConstructs) {
    ExpectCallAccepted(ItemPlace::kScope, Use(form, "fv(y)"));
    ExpectCallAccepted(ItemPlace::kScope, Use(form, "fc(y)"));
  }
  ExpectCallAccepted(ItemPlace::kScope, "x dist {fv(y) := 1, fc(y) :/ 2};");
}

TEST(FunctionsInConstraintCases, DISABLED_AnOutputFormalIsRejectedInADistItem) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectCallReport(place, "x dist {fo(y) := 1};", Direction("fo"));
    ExpectCallReport(place, "x dist {3 := 1, fr(y) :/ 2};", Direction("fr"));
  }
}

TEST(FunctionsInConstraintCases,
     DISABLED_AnOutputInoutOrRefFormalIsRejectedInRandomizeWith) {
  for (const char* form : kConstructs) {
    ExpectCallReport(ItemPlace::kInline, Use(form, "fo(y)"), Direction("fo"));
    ExpectCallReport(ItemPlace::kInline, Use(form, "fi(y)"), Direction("fi"));
    ExpectCallReport(ItemPlace::kInline, Use(form, "fr(y)"), Direction("fr"));
  }
}

TEST(FunctionsInConstraintCases,
     DISABLED_AnOutputInoutOrRefFormalIsRejectedInScopeRandomize) {
  for (const char* form : kScopeConstructs) {
    ExpectCallReport(ItemPlace::kScope, Use(form, "fo(y)"), Direction("fo"));
    ExpectCallReport(ItemPlace::kScope, Use(form, "fi(y)"), Direction("fi"));
    ExpectCallReport(ItemPlace::kScope, Use(form, "fr(y)"), Direction("fr"));
  }
}

TEST(FunctionsInConstraintCases, AFunctionCallIsNoUniquenessMember) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectCallReport(
        place, "unique {x, fv(y)};",
        "a uniqueness constraint member shall denote a singular or array "
        "variable",
        "18.5.4");
  }
}

const char* const kModeConstructs[] = {
    "x == @;", "if (@ > 0) x == 1;", "@ > 0 -> x == 1;",
    "foreach (A[i]) A[i] == @;", "soft x == @;"};

TEST(FunctionsInConstraintCases,
     AModeCallIsRejectedInEveryConstructOfAClassConstraint) {
  for (ItemPlace place : kClassPlaces) {
    for (const char* form : kModeConstructs) {
      ExpectCallReport(place, Use(form, "fm(y)"), Mode("fm"));
      ExpectCallReport(place, Use(form, "fk(y)"), Mode("fk"));
    }
  }
}

TEST(FunctionsInConstraintCases, DISABLED_AModeCallIsRejectedInADistItem) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectCallReport(place, "x dist {fm(y) := 1};", Mode("fm"));
    ExpectCallReport(place, "x dist {3 := 1, fk(y) :/ 2};", Mode("fk"));
  }
}

TEST(FunctionsInConstraintCases, DISABLED_AModeCallIsRejectedInRandomizeWith) {
  for (const char* form : kModeConstructs) {
    ExpectCallReport(ItemPlace::kInline, Use(form, "fm(y)"), Mode("fm"));
    ExpectCallReport(ItemPlace::kInline, Use(form, "fk(y)"), Mode("fk"));
  }
}

TEST(FunctionsInConstraintCases,
     DISABLED_AModeCallOnAHandleIsRejectedInScopeRandomize) {
  ExpectCallReport(ItemPlace::kScope, "x == fm(y);", Mode("fm"));
  ExpectCallReport(ItemPlace::kScope, "x == fk(y);", Mode("fk"));
  ExpectCallReport(ItemPlace::kScope, "if (fk(y) > 0) x == 1;", Mode("fk"));
}

TEST(FunctionsInConstraintCases,
     DISABLED_AMethodWritingAPropertyIsRejectedFromAnObject) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectCallReport(place, "x == fs(y);", SideEffect("fs"));
  }
}

TEST(FunctionsInConstraintCases,
     AFunctionReadingStateAndWritingItsLocalsIsAccepted) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectCallAccepted(place, "x == fp(y);");
  }
}

TEST(FunctionsInConstraintCases,
     DISABLED_AFunctionWritingAModuleVariableIsRejectedInScopeRandomize) {
  ExpectCallReport(ItemPlace::kScope, "x == fs(y);", SideEffect("fs"));
}

TEST(FunctionsInConstraintCases, DISABLED_AStaticLocalCarryingStateIsRejected) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectCallReport(place, "x == fl(y);", SideEffect("fl"));
  }
}

TEST(FunctionsInConstraintCases,
     AStaticLifetimeFunctionKeepingNoStateIsAccepted) {
  ExpectCallAccepted(ItemPlace::kScope, "x == fq(y);");
}

TEST(FunctionsInConstraintCases,
     DISABLED_ACallOfAFunctionWithASideEffectIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectCallReport(place, "x == fn(y);", SideEffect("fn"));
  }
}

}  // namespace
