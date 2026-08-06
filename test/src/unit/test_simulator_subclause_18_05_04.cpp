#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the uniqueness constraint (18.5.4) end to end: each source
// program declares a class with a "unique { range_list }" constraint, calls
// randomize() from an initial block, and copies results out to module variables
// the harness reads. The parser captures the range_list group and the simulator
// builds it into a kUnique solver constraint, so the behavior observed here is
// that of real elaborated source, not a hand-built solver state. The uniqueness
// property is observed by drawing many samples in a source loop and checking no
// two members ever coincide; the illegal-group and no-effect rules are observed
// from a single deterministic randomize() call.

// 18.5.4: a unique constraint requires that no two members of the group hold
// the same value after randomization. With three members confined to a domain
// that barely fits three distinct values, every solve yields three different
// values, so no pair is ever equal across many draws.
TEST(ConstraintUnique, MembersGetDistinctValues) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  rand int c;\n"
      "  constraint u {\n"
      "    a >= 0; a <= 2;\n"
      "    b >= 0; b <= 2;\n"
      "    c >= 0; c <= 2;\n"
      "    unique {a, b, c};\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int alldiff;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    alldiff = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.a == o.b || o.a == o.c || o.b == o.c) alldiff = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "alldiff"), 1u);
}

// 18.5.4: when the domain is too small to give every member a distinct value,
// the uniqueness constraint cannot be satisfied and randomization fails. Three
// members over a two-value domain have no distinct assignment.
TEST(ConstraintUnique, OverConstrainedGroupFails) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  rand int c;\n"
      "  constraint u {\n"
      "    a >= 0; a <= 1;\n"
      "    b >= 0; b <= 1;\n"
      "    c >= 0; c <= 1;\n"
      "    unique {a, b, c};\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.4: if the group of variables contains fewer than two members the
// constraint shall have no effect and shall not cause a contradiction. A single
// member alongside an equality that pins it still solves, and the pinned value
// is produced.
TEST(ConstraintUnique, SingleMemberHasNoEffect) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  constraint u { a == 4; unique {a}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int ra;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    ra = o.a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 4u);
}

// 18.5.4: no randc variable shall appear in the group. A group that names a
// randc member (18.4.2) is illegal and makes randomization fail.
TEST(ConstraintUnique, RandcMemberFails) {
  const char* src =
      "class C;\n"
      "  rand byte a;\n"
      "  randc byte b;\n"
      "  constraint u { unique {a, b}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.4: all members of the group shall be of equivalent type. A byte and an
// int differ in width and so are not of equivalent type; the group is illegal
// and randomization fails.
TEST(ConstraintUnique, InequivalentTypeMembersFail) {
  const char* src =
      "class C;\n"
      "  rand byte a;\n"
      "  rand int b;\n"
      "  constraint u { unique {a, b}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

}  // namespace
