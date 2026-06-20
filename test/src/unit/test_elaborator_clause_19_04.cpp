#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §19.4: an embedded covergroup is instantiated by assigning the result of
// new() to its identifier inside the enclosing class's new() method. Doing so
// there is the sanctioned instantiation site and shall elaborate cleanly.
TEST(EmbeddedCovergroup, AssignInNewMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: the covergroup variable shall not be assigned outside the new()
// method of its parent class. An assignment from any other method is an error.
TEST(EmbeddedCovergroup, AssignOutsideNewMethodError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function void build();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: the prohibition covers any assignment, not just a new() construction,
// and applies even when the assignment is nested inside control flow within a
// non-constructor method.
TEST(EmbeddedCovergroup, NestedAssignOutsideNewMethodError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  bit en;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function void reconfig();\n"
             "    if (en) cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: leaving the covergroup uninstantiated (no assignment anywhere) is
// legal; the standard simply says no data will be sampled in that case.
TEST(EmbeddedCovergroup, NoInstantiationOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: the restriction to the new() method holds even when the class does
// have a constructor that legally instantiates the covergroup. A second method
// that reassigns the same covergroup variable is still an error; the presence
// of a valid instantiation site does not license assignments elsewhere.
TEST(EmbeddedCovergroup, AssignInSecondMethodAlongsideNewError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "  function void reconfig();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: an assignment to the covergroup variable is forbidden outside new()
// wherever it appears, including buried inside a loop body of another method.
TEST(EmbeddedCovergroup, AssignInLoopOutsideNewMethodError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function void setup();\n"
             "    for (int i = 0; i < 2; i = i + 1) cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: an embedded covergroup may build a coverage model over protected and
// local class properties without weakening data encapsulation, and class
// members may appear both in coverpoint expressions and as conditional guards.
// Naming a local property in a coverpoint and a protected property in an iff
// guard must elaborate cleanly rather than be rejected as an access violation.
TEST(EmbeddedCovergroup, CoversLocalAndProtectedPropertiesOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local int x;\n"
             "  protected bit en;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x iff (en);\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
