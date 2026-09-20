#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §27.5 (printed page 824) makes a generate block a scope of its own and
// §23.9 (printed 761) has a name declared in the block stand over the
// enclosing scope's, so g's `typedef struct { int a, b; } pair_t;` hides the
// module's one-member pair_t for the formal of g's function (§6.18, printed
// 118; §13.3, printed 337), and `g.f(tagged A '{3, 4})` reads §7.2.1's 34.
// The module's pass over the generate blocks resolved the member to the
// module's pair_t first, and the block's own pass, finding the member
// resolved, kept it, so the body read 3 * 10 from a and nothing from b.
TEST(TaskSim, GenerateBlockFunctionFormalReadsTheBlocksTypedefOverTheModules) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

// The module's own function beside the block still names the module's pair_t
// (§23.9, printed page 761): its formal's A holds the one member a, so
// `f(tagged A '{7})` reads 7, and g's reads 34 from the block's two-member
// pair_t, 734 in all; a pass that took the block's names out of the module's
// own table would have left the module's formal a scalar reading 0, 34.
TEST(TaskSim, ModuleFunctionBesideAShadowingBlockReadsTheModulesOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "    return a.A.a;\n"
                      "  endfunction\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = f(tagged A '{7}) * 100"
                      " + g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            734u);
}

// The same one level down (§27.5, printed page 824): h, a block of g's,
// declares a three-member pair_t over g's two-member one, which in turn
// stands over the module's, so `g.h.f(tagged A '{1, 2, 3})` reads 123 and
// `g.f(tagged A '{5, 6})` 56, 123056 in all; the module's pass reaching both
// blocks with the module's table sized each formal by the one-member pair_t
// and neither body read its second member.
TEST(TaskSim,
     NestedGenerateBlockFunctionFormalReadsItsOwnTypedefOverTheOuters) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b, c; } pair_t;\n"
                      "      function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "      endfunction\n"
                      "    end\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f(tagged A '{1, 2, 3}) * 1000"
                      " + g.f(tagged A '{5, 6});\n"
                      "endmodule\n",
                      "y"),
            123056u);
}

}  // namespace
