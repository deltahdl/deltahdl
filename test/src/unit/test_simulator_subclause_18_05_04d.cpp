#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string Tries(const std::string& decls, const std::string& randomize,
                  const std::string& holds) {
  return "class C;\n" + decls +
         "endclass\n"
         "module t;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 16; i++)\n"
         "      if (" +
         randomize + " && " + holds +
         ") held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

TEST(UniquenessCases, AOneElementArrayIsUnconstrained) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] one[1];\n"
                         "  constraint c { one[0] == 3; unique {one}; }\n",
                         "o.randomize()", "o.one[0] == 3")),
            "16\n");
}

TEST(UniquenessCases, DISABLED_AnEmptyDynamicArrayIsUnconstrained) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] e[];\n"
                         "  rand bit [1:0] x;\n"
                         "  constraint c { e.size() == 0; x == 2; unique {e}; "
                         "}\n",
                         "o.randomize()", "o.x == 2")),
            "16\n");
}

TEST(UniquenessCases, AOneElementSliceIsUnconstrained) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] s[4];\n"
                         "  constraint c { s[2] == 3; unique {s[2:2]}; }\n",
                         "o.randomize()", "o.s[2] == 3")),
            "16\n");
}

TEST(UniquenessCases, AOneMemberGroupInAnInlineBlockIsUnconstrained) {
  EXPECT_EQ(
      RunSrc(Tries("  rand bit [1:0] x;\n",
                   "o.randomize() with { x == 1; unique {x}; }", "o.x == 1")),
      "16\n");
}

TEST(UniquenessCases, AOneMemberGroupInAScopeRandomizeIsUnconstrained) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  bit [1:0] x;\n"
                   "  int i, held = 0;\n"
                   "  initial begin\n"
                   "    for (i = 0; i < 16; i++)\n"
                   "      if (std::randomize(x) with { x == 1; unique {x}; } "
                   "&& x == 1) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "16\n");
}

TEST(UniquenessCases, AOneElementArrayBesideAPinnedMemberFails) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [1:0] one[1];\n"
                   "  rand bit [1:0] x;\n"
                   "  constraint c { one[0] == 3; x == 3; unique {one, x}; }\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    $display(\"%0d\", o.randomize());\n"
                   "  end\n"
                   "endmodule\n"),
            "0\n");
}

const char* const kDistinct4 =
    "o.v[0] != o.v[1] && o.v[0] != o.v[2] && o.v[0] != o.v[3] && "
    "o.v[1] != o.v[2] && o.v[1] != o.v[3] && o.v[2] != o.v[3]";

TEST(UniquenessCases, TheLeavesOfATwoDimensionalArrayDiffer) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] m[2][2];\n"
                         "  constraint c { unique {m}; }\n",
                         "o.randomize()",
                         "o.m[0][0] != o.m[0][1] && o.m[0][0] != o.m[1][0] "
                         "&& o.m[0][0] != o.m[1][1] && o.m[0][1] != o.m[1][0] "
                         "&& o.m[0][1] != o.m[1][1] && o.m[1][0] != "
                         "o.m[1][1]")),
            "16\n");
}

TEST(UniquenessCases, DISABLED_ADynamicArraySizedByAConstraintDiffers) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] v[];\n"
                         "  constraint c { v.size() == 4; unique {v}; }\n",
                         "o.randomize()", kDistinct4)),
            "16\n");
}

TEST(UniquenessCases, ADynamicArraySizedByNewDiffers) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] v[];\n"
                         "  constraint c { unique {v}; }\n"
                         "  function new();\n"
                         "    v = new[4];\n"
                         "  endfunction\n",
                         "o.randomize()", kDistinct4)),
            "16\n");
}

TEST(UniquenessCases, DISABLED_AQueueSizedByAConstraintDiffers) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] v[$];\n"
                         "  constraint c { v.size() == 4; unique {v}; }\n",
                         "o.randomize()", kDistinct4)),
            "16\n");
}

TEST(UniquenessCases, AnAssociativeArraysElementsDiffer) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] v[int];\n"
                         "  constraint c { unique {v}; }\n"
                         "  function new();\n"
                         "    v[0] = 0; v[1] = 0; v[2] = 0; v[3] = 0;\n"
                         "  endfunction\n",
                         "o.randomize()", kDistinct4)),
            "16\n");
}

TEST(UniquenessCases, AnOutOfBlockGroupDiffers) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [1:0] v[4];\n"
                   "  constraint c;\n"
                   "endclass\n"
                   "constraint C::c { unique {v}; }\n"
                   "module t;\n"
                   "  int i, held = 0;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    for (i = 0; i < 16; i++)\n"
                   "      if (o.randomize() && " +
                   std::string(kDistinct4) +
                   ") held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "16\n");
}

TEST(UniquenessCases, AnInlineGroupDiffers) {
  EXPECT_EQ(RunSrc(Tries("  rand bit [1:0] v[4];\n",
                         "o.randomize() with { unique {v}; }", kDistinct4)),
            "16\n");
}

TEST(UniquenessCases, DISABLED_AScopeRandomizeGroupDiffers) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  bit [1:0] a, b, c, d;\n"
                   "  int i, held = 0;\n"
                   "  initial begin\n"
                   "    for (i = 0; i < 16; i++)\n"
                   "      if (std::randomize(a, b, c, d) with { unique {a, b, "
                   "c, d}; } && a != b && a != c && a != d && b != c && b "
                   "!= d && c != d) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "16\n");
}

}  // namespace
