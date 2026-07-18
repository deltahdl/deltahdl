#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.7.1's local:: scope-resolution rule end to end. Each
// program elaborates a real class, calls randomize() with an inline `with { ...
// }` block written in source, and copies the solved value to a module variable
// the harness reads -- so the behavior observed is that of parse/elaborate/run
// resolving a local::-qualified name, not a hand-built resolution table.
//
// The rule under test: inside an unrestricted inline constraint block an
// unqualified name is looked up in the randomized object's class scope first,
// but a name written as local::x bypasses that class scope and binds to the
// scope containing the randomize() method call. Every program below
// deliberately names something in BOTH scopes so a wrong resolution would
// produce a different value; the value asserted is only reachable when local::
// bound to the calling scope. Before the local:: prefix was honored the
// qualified name resolved to nothing (an unknown), pinning the object to 0
// instead.

// 18.7.1: the clause's own example binds a subroutine argument. The object's
// class and the enclosing function both declare `x`; the unqualified `x` on the
// left of the relation binds to the object's random member (hiding the
// argument), while `local::x` on the right binds to the function argument. The
// object's x is therefore pinned to the argument's value, 30 -- a value the
// free random x would almost never independently hold, so it is the visible
// proof local:: reached the calling scope rather than the object.
TEST(InlineConstraintLocalScope, LocalQualifierBindsToSubroutineArgument) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function automatic int pin(bit [7:0] x);\n"
      "    C obj;\n"
      "    int ok;\n"
      "    obj = new;\n"
      "    ok = obj.randomize() with { x == local::x; };\n"
      "    return obj.x;\n"
      "  endfunction\n"
      "  initial rx = pin(30);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 30u);
}

// 18.7.1: the calling scope's name need not be a subroutine argument -- a
// variable local to the block that contains the randomize() call is resolved
// the same way. Here the initial block declares its own `x`, distinct from the
// object's random `x`; `local::x` binds to that block-local variable (77), so
// the object comes back pinned to 77.
TEST(InlineConstraintLocalScope, LocalQualifierBindsToCallerLocalVariable) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    C c1;\n"
      "    bit [7:0] x;\n"
      "    int ok;\n"
      "    c1 = new;\n"
      "    x = 77;\n"
      "    ok = c1.randomize() with { x == local::x; };\n"
      "    rx = c1.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 77u);
}

// 18.7.1: local:: works with the relational operators the clause's example uses
// (`<`), and it can name declarations that exist ONLY in the calling scope.
// Here the object has no `lo`/`hi`; both are function arguments reached through
// local::, bounding the object's random x from below and above. x > 10 and
// x < 12 leave exactly 11, so a result of 11 proves both local:: bounds were
// read from the calling scope.
TEST(InlineConstraintLocalScope, LocalQualifierBoundsFromCallerNames) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function automatic int pin_range(int lo, int hi);\n"
      "    C obj;\n"
      "    int ok;\n"
      "    obj = new;\n"
      "    ok = obj.randomize() with { x > local::lo; x < local::hi; };\n"
      "    return obj.x;\n"
      "  endfunction\n"
      "  initial rx = pin_range(10, 12);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 11u);
}

// 18.7.1: as it pertains to wildcard package imports, a name written local::a
// resolves the same declaration an unqualified a would in the calling scope.
// Here §26.3's `import pkg::*` makes the package parameter LIMIT visible
// unqualified in the module; the with-block then reaches it through local::,
// which -- like a bare LIMIT -- binds to that wildcard-imported declaration.
// The object's x is pinned to 88, so the value is proof local:: resolved in the
// importing (local) scope, not into the randomized object's class. The input is
// built from the dependency's real import syntax and driven through the full
// pipeline; had local:: failed to reach the imported name the solve would have
// pinned x to 0 instead.
TEST(InlineConstraintLocalScope, LocalQualifierResolvesWildcardImportedName) {
  const char* src =
      "package pkg;\n"
      "  parameter int LIMIT = 88;\n"
      "endpackage\n"
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    C c1;\n"
      "    int ok;\n"
      "    c1 = new;\n"
      "    ok = c1.randomize() with { x == local::LIMIT; };\n"
      "    rx = c1.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 88u);
}

}  // namespace
