#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_constraint_item_places.h"
#include "helpers_soft_places.h"

namespace {

constexpr ItemPlace kClassPlaces[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline};

const char* const kSoftThree = "soft a == 3; a inside {3, 4}; ";
const char* const kEarlierBlock =
    "  constraint k0 { soft a == 3; a inside {3, 4}; soft u[2] == 1; "
    "u[2] inside {1, 2}; }\n";

std::string DisableAt(ItemPlace place, const std::string& directive,
                      const std::string& check) {
  const std::string kBody = std::string(kSoftVars) + kEarlierBlock;
  switch (place) {
    case ItemPlace::kClassBlock:
      return SoftCount("", kBody + "  constraint k { " + directive + " }\n", "",
                       "o.randomize()", check);
    case ItemPlace::kOutOfBlock:
      return SoftCount("", kBody + "  constraint k;\n",
                       "constraint C::k { " + directive + " }\n",
                       "o.randomize()", check);
    case ItemPlace::kInline:
      return SoftCount("", kBody, "",
                       "o.randomize() with { " + directive + " }", check);
    default: {
      const std::string kElements =
          directive.find("u[i]") == std::string::npos
              ? ""
              : "soft u[2] == 1; u[2] inside {1, 2}; ";
      return SoftAt(place, kSoftThree + kElements + directive, check);
    }
  }
}

std::string DisabledBy(ItemPlace place, const std::string& directive) {
  return DisableAt(place, directive, "o.a == 3");
}

TEST(DisableSoftCases, DISABLED_ADirectiveDiscardsAnEarlierSoftOfItsOwnBlock) {
  for (ItemPlace place :
       {ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline}) {
    EXPECT_TRUE(BothValuesDrawn(
        SoftAt(place, std::string(kSoftThree) + "disable soft a;", "o.a == 3")))
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, ADirectiveDiscardsTheSoftItNames) {
  for (ItemPlace place : kClassPlaces) {
    EXPECT_TRUE(BothValuesDrawn(DisabledBy(place, "disable soft a;")))
        << ItemPlaceName(place);
    EXPECT_EQ(DisabledBy(place, "disable soft b;"), "32\n")
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, DISABLED_ADirectiveDiscardsInScopeRandomize) {
  for (const char* directive :
       {"disable soft a;", "g -> disable soft a;", "if (g) disable soft a;",
        "foreach (u[i]) disable soft a;"}) {
    EXPECT_TRUE(BothValuesDrawn(DisabledBy(ItemPlace::kScope, directive)))
        << directive;
  }
  EXPECT_EQ(DisabledBy(ItemPlace::kScope, "disable soft b;"), "32\n");
}

TEST(DisableSoftCases, ADirectiveInATrueConsequentDiscards) {
  for (ItemPlace place : kClassPlaces) {
    EXPECT_TRUE(BothValuesDrawn(DisabledBy(place, "g -> disable soft a;")))
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, DISABLED_ADirectiveInAFalseConsequentKeepsTheSoft) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(DisabledBy(place, "!g -> disable soft a;"), "32\n")
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, ADirectiveInATrueIfBranchDiscards) {
  for (ItemPlace place : kClassPlaces) {
    EXPECT_TRUE(BothValuesDrawn(DisabledBy(place, "if (g) disable soft a;")))
        << ItemPlaceName(place);
    EXPECT_TRUE(BothValuesDrawn(
        DisabledBy(place, "if (!g) b == 0; else disable soft a;")))
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, DISABLED_ADirectiveInAFalseIfBranchKeepsTheSoft) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(DisabledBy(place, "if (!g) disable soft a;"), "32\n")
        << ItemPlaceName(place);
    EXPECT_EQ(DisabledBy(place, "if (g) b == 0; else disable soft a;"), "32\n")
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, ADirectiveInAForeachBodyDiscards) {
  for (ItemPlace place : kClassPlaces) {
    EXPECT_TRUE(
        BothValuesDrawn(DisabledBy(place, "foreach (u[i]) disable soft a;")))
        << ItemPlaceName(place);
  }
}

TEST(DisableSoftCases, DISABLED_ADirectiveOnTheIteratedElementsDiscards) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_TRUE(BothValuesDrawn(
        DisableAt(place, "foreach (u[i]) disable soft u[i];", "o.u[2] == 1")))
        << ItemPlaceName(place);
  }
}

std::string Derived(const std::string& base_item, const std::string& item) {
  SimFixture f;
  return RunCapture(
      "class B;\n"
      "  rand bit [3:0] a;\n"
      "  constraint k { a inside {3, 4}; " +
          base_item +
          " }\n"
          "endclass\n"
          "class C extends B;\n"
          "  constraint d { " +
          item +
          " }\n"
          "endclass\n"
          "module t;\n"
          "  int n, held = 0;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    for (n = 0; n < 32; n++)\n"
          "      if (o.randomize() && o.a == 3) held++;\n"
          "    $display(\"%0d\", held);\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(DisableSoftCases, ADerivedDirectiveDiscardsTheBasesSoft) {
  EXPECT_TRUE(BothValuesDrawn(Derived("soft a == 3;", "disable soft a;")));
}

TEST(DisableSoftCases, ABaseDirectiveKeepsTheDerivedSoft) {
  EXPECT_EQ(Derived("disable soft a;", "soft a == 3;"), "32\n");
}

TEST(DisableSoftCases, DISABLED_AContainerDirectiveDiscardsTheContainedSoft) {
  const std::string kHeld =
      "class D;\n"
      "  rand bit [3:0] v;\n"
      "  constraint k { soft v == 3; }\n"
      "endclass\n";
  const std::string kBody =
      "  rand D h;\n"
      "  function new(); h = new; endfunction\n";
  EXPECT_TRUE(BothValuesDrawn(SoftCount(
      kHeld,
      kBody + "  constraint c { disable soft h.v; h.v inside {3, 4}; }\n", "",
      "o.randomize()", "o.h.v == 3")));
  EXPECT_EQ(SoftCount(kHeld, kBody + "  constraint c { h.v inside {3, 4}; }\n",
                      "", "o.randomize()", "o.h.v == 3"),
            "32\n");
}

}  // namespace
