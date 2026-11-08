#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
      "    static C o = new;\n"
      "    alldiff = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.a == o.b || o.a == o.c || o.b == o.c) alldiff = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "alldiff"), 1u);
}

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
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

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
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    ra = o.a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 4u);
}

TEST(ConstraintUnique, InlineRandGroupThroughMethodHandleSolves) {
  const char* src =
      "class C;\n"
      "  rand byte a;\n"
      "  rand byte b;\n"
      "endclass\n"
      "class H;\n"
      "  function int go();\n"
      "    C x;\n"
      "    x = new;\n"
      "    return x.randomize() with { unique {a, b}; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static H h = new;\n"
      "    ok = h.go();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
}

TEST(ConstraintUnique, InequivalentTypeMembersFail) {
  const char* src =
      "typedef int int_t;\n"
      "class C;\n"
      "  rand byte a;\n"
      "  rand int_t b;\n"
      "  constraint u { unique {a, b}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

}  // namespace
