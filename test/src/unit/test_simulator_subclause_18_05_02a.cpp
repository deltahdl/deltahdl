#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstraintInheritanceSim, DerivedConstraintHonoredThroughBaseHandle) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  constraint dc { x == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    ok = b.randomize();\n"
      "    rx = d.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ConstraintInheritanceSim, InheritedAndAdditionalConstraintsBothHonored) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bc { x == 10; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand bit [7:0] y;\n"
      "  constraint dc { y == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    ok = b.randomize();\n"
      "    rx = d.x;\n"
      "    ry = d.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 10u);
  EXPECT_EQ(RunAndGet(src, "ry"), 42u);
}

TEST(ConstraintInheritanceSim, SameNameDerivedConstraintReplacesInherited) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 10; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  constraint c { x == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    ok = d.randomize();\n"
      "    rx = d.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ConstraintInheritanceSim, SameObjectSameResultRegardlessOfHandleType) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bc { x == 7; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    ok = d.randomize();\n"
      "    rx = d.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 7u);
}

TEST(ConstraintInheritanceSim, DerivedPrototypeExternalBlockReplacesInherited) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 10; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  constraint c;\n"
      "endclass\n"
      "constraint Derived::c { x == 42; }\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    ok = d.randomize();\n"
      "    rx = d.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

}  // namespace
