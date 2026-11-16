#include <gtest/gtest.h>

#include <string>

#include "helpers_constraint_item_places.h"
#include "helpers_soft_places.h"

namespace {

constexpr ItemPlace kClassPlaces[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline};

struct SoftForm {
  const char* honored;
  const char* discarded;
};

constexpr SoftForm kDirect = {"soft a == 3;", "a != 3; soft a == 3;"};
constexpr SoftForm kIfBranch = {"if (g) soft a == 3;",
                                "a != 3; if (g) soft a == 3;"};
constexpr SoftForm kElseBranch = {"if (!g) b == 0; else soft a == 3;",
                                  "a != 3; if (!g) b == 0; else soft a == 3;"};
constexpr SoftForm kConsequent = {"g -> soft a == 3;",
                                  "a != 3; g -> soft a == 3;"};
constexpr SoftForm kForeachOther = {"foreach (u[i]) soft a == 3;",
                                    "a != 3; foreach (u[i]) soft a == 3;"};

void ExpectHonoredAndDiscarded(ItemPlace place, const SoftForm& form) {
  EXPECT_EQ(SoftAt(place, form.honored, "o.a == 3"), "32\n")
      << ItemPlaceName(place) << ": " << form.honored;
  EXPECT_EQ(SoftAt(place, form.discarded, "o.a != 3"), "32\n")
      << ItemPlaceName(place) << ": " << form.discarded;
}

TEST(SoftConstraintCases, ADirectSoftRelationIsHonoredAndDiscarded) {
  for (ItemPlace place : kClassPlaces) {
    ExpectHonoredAndDiscarded(place, kDirect);
  }
}

TEST(SoftConstraintCases, ASoftConsequentIsHonoredAndDiscarded) {
  for (ItemPlace place : kClassPlaces) {
    ExpectHonoredAndDiscarded(place, kConsequent);
  }
}

TEST(SoftConstraintCases, DISABLED_ASoftRelationIsHonoredInScopeRandomize) {
  ExpectHonoredAndDiscarded(ItemPlace::kScope, kDirect);
  ExpectHonoredAndDiscarded(ItemPlace::kScope, kConsequent);
}

TEST(SoftConstraintCases, DISABLED_ASoftIfBranchIsHonoredAndDiscarded) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectHonoredAndDiscarded(place, kIfBranch);
  }
}

TEST(SoftConstraintCases, DISABLED_ASoftElseBranchIsHonoredAndDiscarded) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectHonoredAndDiscarded(place, kElseBranch);
  }
}

TEST(SoftConstraintCases, DISABLED_ASoftForeachBodyOnAnotherVariableIsHonored) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectHonoredAndDiscarded(place, kForeachOther);
  }
}

TEST(SoftConstraintCases, DISABLED_ASoftForeachBodyOnTheElementsIsHonored) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(
        SoftAt(place, "foreach (u[i]) soft u[i] == i;",
               "o.u[0] == 0 && o.u[1] == 1 && o.u[2] == 2 && o.u[3] == 3"),
        "32\n")
        << ItemPlaceName(place);
    EXPECT_EQ(SoftAt(place, "u[1] != 1; foreach (u[i]) soft u[i] == i;",
                     "o.u[1] != 1 && o.u[2] == 2"),
              "32\n")
        << ItemPlaceName(place);
  }
}

TEST(SoftConstraintCases, AnInlineSoftYieldsToTheClassesHardConstraints) {
  const std::string kBody =
      std::string(kSoftVars) + "  constraint k { a < 8; }\n";
  EXPECT_EQ(SoftCount("", kBody, "", "o.randomize() with { soft a == 3; }",
                      "o.a == 3"),
            "32\n");
  EXPECT_EQ(SoftCount("", kBody, "", "o.randomize() with { soft a == 9; }",
                      "o.a < 8"),
            "32\n");
}

}  // namespace
