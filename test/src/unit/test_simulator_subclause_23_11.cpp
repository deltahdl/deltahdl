#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §23.11 (printed page 773): "All identifiers in the bind instantiation are
// referenced from the bind target's point of view", and the standard's example
// binds `i_mycheck(.*, ...)`, so the ports `.*` reaches connect to the target's
// signals of their names (§23.3.2.4). A bound instance built its connections
// from the named and ordered ones alone, and v1 read x and v2 0.
TEST(BindInstantiation, WildcardConnectsPortsToTargetSignals) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module targetmod;\n"
                 "  logic v1 = 1;\n"
                 "  int v2 = 7;\n"
                 "  int v3 = 3;\n"
                 "endmodule\n"
                 "module mycheck #(parameter param1 = 1, param2 = 2)\n"
                 "    (input v1, input var int v2, input var int p);\n"
                 "  initial #1 $display(\"p1 %0d p2 %0d v1 %0d v2 %0d\",\n"
                 "      param1, param2, v1, v2 + p - 3);\n"
                 "endmodule\n"
                 "module top;\n"
                 "  targetmod t();\n"
                 "  bind targetmod mycheck #(.param1(4), .param2(8'h44))\n"
                 "      i_mycheck(.*, .p(v3));\n"
                 "endmodule\n",
                 f),
      "p1 4 p2 68 v1 1 v2 7\n");
}

// Each instance of the target gives `.*` its own signals, a target's port among
// them, and a port the target has no name for takes its default value.
TEST(BindInstantiation, WildcardReadsEachTargetInstanceAndPortDefaults) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module unit(input var int a);\n"
                       "  int b;\n"
                       "  initial b = a * 10;\n"
                       "endmodule\n"
                       "module probe(input var int a, input var int b,\n"
                       "             input var int c = 5);\n"
                       "  initial #1 $display(\"%0d %0d %0d\", a, b, c);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  unit c1(.a(2));\n"
                       "  unit c2(.a(3));\n"
                       "  bind unit probe pr(.*);\n"
                       "endmodule\n",
                       f),
            "2 20 5\n3 30 5\n");
}

// §23.11 with §23.6: a hierarchical name from top reads the variables of the
// instance a bind puts in each sub, s1.c.pass reading s1's 3 and s2.c.pass
// s2's 4. The reference was reported unresolved and nothing ran.
TEST(BindInstantiation, HierarchicalNameReadsABoundInstancesVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m2(input var int a);\n"
                       "  int pass;\n"
                       "  initial pass = a + 1;\n"
                       "endmodule\n"
                       "module sub(input var int x);\n"
                       "endmodule\n"
                       "bind sub m2 c(.a(x));\n"
                       "module top;\n"
                       "  sub s1(2);\n"
                       "  sub s2(3);\n"
                       "  initial #1 $display(\"%0d %0d\", s1.c.pass, "
                       "s2.c.pass);\n"
                       "endmodule\n",
                       f),
            "3 4\n");
}

// §23.11: `bind sub: s2` written in top inserts the instance into top's s2
// alone, so only s2's prints, 4; bound into both, s1's would print 3 as well.
// Nothing was bound and nothing printed.
TEST(BindInstantiation, TargetInstanceListBindsTheListedInstanceAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m2(input var int a);\n"
                       "  initial $display(\"%0d\", a + 1);\n"
                       "endmodule\n"
                       "module sub(input var int x);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sub s1(2);\n"
                       "  sub s2(3);\n"
                       "  bind sub: s2 m2 c(.a(x));\n"
                       "endmodule\n",
                       f),
            "4\n");
}

}  // namespace
