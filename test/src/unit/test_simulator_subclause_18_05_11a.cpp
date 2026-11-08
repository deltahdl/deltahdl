#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionsInConstraints, FunctionResultUsedAsStateVariable) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int dbl(int a); return 2 * a; endfunction\n"
      "  constraint cy { y == 3; }\n"
      "  constraint cx { x == dbl(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 6u);
}

TEST(FunctionsInConstraints, ArgumentSolvedFirstGivesUniformArgument) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint c { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int y0;\n"
      "  int bad;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    y0 = 0;\n"
      "    bad = 0;\n"
      "    for (int i = 0; i < 800; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.y == 0) y0 = y0 + 1;\n"
      "      if (o.x > 2 * o.y) bad = bad + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto y0 = RunAndGet(src, "y0");
  EXPECT_GE(y0, 140u);
  EXPECT_LE(y0, 260u);
  EXPECT_EQ(RunAndGet(src, "bad"), 0u);
}

TEST(FunctionsInConstraints, MultipleArgumentsSolvedBeforeConsumer) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [3:0] z;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cy { y == 2; }\n"
      "  constraint cz { z == 3; }\n"
      "  constraint cx { x == f(y) + f(z); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 5u);
}

TEST(FunctionsInConstraints, CircularArgumentOrderingFailsRandomize) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  function int id(int v); return v; endfunction\n"
      "  constraint c { a < id(b); b < id(a); }\n"
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

TEST(FunctionsInConstraints, NoFunctionCallLeavesFlatSolveUnchanged) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] y;\n"
      "  constraint c { x == y; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int eq;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    eq = (o.x == o.y);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
}

TEST(FunctionsInConstraints, RandcCyclesWhileArgumentPriorityActive) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] c;\n"
      "  rand bit [1:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cx { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int seen;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    seen = 0;\n"
      "    for (int i = 0; i < 4; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      seen = seen | (1 << o.c);\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "seen"), 15u);
}

TEST(FunctionsInConstraints, FunctionOfStateVariableArgumentDrivesSolve) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int k;\n"
      "  function int inc(int a); return a + 1; endfunction\n"
      "  function new(); k = 5; endfunction\n"
      "  constraint cx { x == inc(k); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 6u);
}

TEST(FunctionsInConstraints, SetConstrainedArgumentFeedsConsumer) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [7:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cy { y inside {2, 4, 8}; }\n"
      "  constraint cx { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int bad;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    bad = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (!(o.y == 2 || o.y == 4 || o.y == 8)) bad = bad + 1;\n"
      "      if (o.x > 2 * o.y) bad = bad + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "bad"), 0u);
}

TEST(FunctionsInConstraints, IndirectCircularArgumentOrderingFailsRandomize) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  rand bit [3:0] c;\n"
      "  function int id(int v); return v; endfunction\n"
      "  constraint cyc { a < id(b); b < id(c); c < id(a); }\n"
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

TEST(FunctionsInConstraints,
     FunctionReadingOwnStateWithoutArgumentsDrivesSolve) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int k;\n"
      "  function int get(); return k + 2; endfunction\n"
      "  function new(); k = 5; endfunction\n"
      "  constraint cx { x == get(); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize());\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "xv"), 7u);
}

}  // namespace
