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

// §6.18 (printed page 118) introduces a forward typedef's name in the scope
// it stands in, the definition following in that same scope, and §27.5
// (printed 824) makes g a scope of its own, so g's `typedef struct pair_t;`
// stands over the module's one-member pair_t for the formal of g's function
// between it and g's two-member definition, and `g.f(tagged A '{3, 4})` reads
// §7.2.1's 34. The forward typedef reserved its name without displacing the
// module's entry, the block's function was resolved at its item to the
// module's pair_t and kept, and the body read 3 * 10 and nothing from b, 30.
TEST(TaskSim, GenerateBlockForwardTypedefStandsOverTheModulesTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

// §6.18 (printed page 118) admits a forward typedef after the final
// definition in the same scope, so g's `typedef struct pair_t;` below g's
// two-member definition leaves that definition standing for the function
// below it, over the module's one-member pair_t, and `g.f(tagged A '{3, 4})`,
// whose body swaps the members, reads 43; a forward typedef that displaced
// whatever entry it met would have put its placeholder over g's own
// definition and left the formal a scalar reading 0.
TEST(TaskSim, GenerateBlockForwardTypedefBelowItsDefinitionKeepsTheDefinition) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.b * 10 + a.A.a;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            43u);
}

// §27.5 (printed page 824) makes h, a block of g's, a scope of its own, and
// §23.9 (printed 761) has h's two-member pair_t stand over g's three-member
// one within h alone, so g's function written below h names g's pair_t, reads
// §7.2.1's 123 from `'{1, 2, 3}`, and h's `g.h.f2(tagged A '{1, 2})` reads
// 12, 12123 in all. h's definition stayed in the table after h's items, so
// g's function was resolved at its item to h's two-member pair_t, its c a
// member of nothing reading 0, and the sum was 12120.
TEST(TaskSim, GenerateBlockFunctionBelowANestedBlockReadsItsOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b, c; } pair_t;\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b; } pair_t;\n"
                      "      function int f2(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 10 + a.A.b;\n"
                      "      endfunction\n"
                      "    end\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f2(tagged A '{1, 2}) * 1000"
                      " + g.f(tagged A '{1, 2, 3});\n"
                      "endmodule\n",
                      "y"),
            12123u);
}

}  // namespace
