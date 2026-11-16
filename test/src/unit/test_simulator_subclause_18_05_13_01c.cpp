#include <gtest/gtest.h>

#include <string>

#include "helpers_constraint_item_places.h"
#include "helpers_soft_places.h"

namespace {

constexpr ItemPlace kClassPlaces[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline};

TEST(SoftPriorityCases, TheLaterSoftInOneBlockWins) {
  for (ItemPlace place : kClassPlaces) {
    EXPECT_EQ(SoftAt(place, "soft a == 2; soft a == 5;", "o.a == 5"), "32\n")
        << ItemPlaceName(place);
  }
}

TEST(SoftPriorityCases, DISABLED_TheLaterSoftWinsInScopeRandomize) {
  EXPECT_EQ(SoftAt(ItemPlace::kScope, "soft a == 2; soft a == 5;", "o.a == 5"),
            "32\n");
}

TEST(SoftPriorityCases, DISABLED_TheLaterIterationOfAFixedArrayWins) {
  for (ItemPlace place : kEveryItemPlace) {
    EXPECT_EQ(SoftAt(place, "foreach (u[i]) soft a == i + 4;", "o.a == 7"),
              "32\n")
        << ItemPlaceName(place);
  }
}

TEST(SoftPriorityCases, DISABLED_TheLaterIterationOfADynamicArrayOrQueueWins) {
  const std::string kBody =
      "  rand bit [3:0] a;\n"
      "  int d[];\n"
      "  int q[$];\n"
      "  function new();\n"
      "    d = new[3];\n"
      "    q = {0, 1, 2};\n"
      "  endfunction\n";
  EXPECT_EQ(
      SoftCount("",
                kBody + "  constraint k { foreach (d[i]) soft a == i + 4; }\n",
                "", "o.randomize()", "o.a == 6"),
      "32\n");
  EXPECT_EQ(
      SoftCount("",
                kBody + "  constraint k { foreach (q[i]) soft a == i + 4; }\n",
                "", "o.randomize()", "o.a == 6"),
      "32\n");
}

TEST(SoftPriorityCases, DISABLED_TheHighestIndexOfAnAssociativeArrayWins) {
  EXPECT_EQ(SoftCount("",
                      "  rand bit [3:0] a;\n"
                      "  int m[int];\n"
                      "  function new();\n"
                      "    m[9] = 0;\n"
                      "    m[2] = 0;\n"
                      "    m[5] = 0;\n"
                      "  endfunction\n"
                      "  constraint k { foreach (m[i]) soft a == i; }\n",
                      "", "o.randomize()", "o.a == 9"),
            "32\n");
}

TEST(SoftPriorityCases, AnInClassBlockOutranksAnEarlierPrototype) {
  EXPECT_EQ(SoftCount("",
                      "  rand bit [3:0] a;\n"
                      "  constraint e;\n"
                      "  constraint k { soft a == 2; }\n",
                      "constraint C::e { soft a == 7; }\n", "o.randomize()",
                      "o.a == 2"),
            "32\n");
  EXPECT_EQ(SoftCount("",
                      "  rand bit [3:0] a;\n"
                      "  constraint k { soft a == 2; }\n"
                      "  constraint e;\n",
                      "constraint C::e { soft a == 7; }\n", "o.randomize()",
                      "o.a == 7"),
            "32\n");
}

const char* const kHeld =
    "class D;\n"
    "  rand bit [3:0] x;\n"
    "  int v;\n"
    "  constraint k { soft x == v; }\n"
    "endclass\n";

TEST(SoftPriorityCases, AnObjectUnderTwoHandlesTakesTheLaterHandlesPlace) {
  const std::string kBody =
      "  rand D p1, p2, p3;\n"
      "  constraint c { p1.x == p2.x; }\n"
      "  function new();\n"
      "    p1 = new;\n"
      "    p2 = new;\n"
      "    p1.v = 9;\n"
      "    p2.v = 5;\n";
  EXPECT_EQ(SoftCount(kHeld, kBody + "    p3 = p1;\n  endfunction\n", "",
                      "o.randomize()", "o.p1.x == 9"),
            "32\n");
  EXPECT_EQ(SoftCount(kHeld, kBody + "    p3 = new;\n  endfunction\n", "",
                      "o.randomize()", "o.p1.x == 5"),
            "32\n");
}

}  // namespace
