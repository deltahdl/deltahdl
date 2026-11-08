#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
