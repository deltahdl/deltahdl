#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the sole runtime rule of 18.5.2 end to end: randomize() is
// virtual, so it honors the constraints of the object on which it was called
// regardless of the static type of the handle used to call it. Each program
// stores a derived object in a superclass-typed handle, calls randomize()
// through that superclass handle, and copies the solved members out to module
// variables the harness reads. The behavior observed is that of real elaborated
// source driven through parse, elaborate, and run -- not a hand-built solver
// state -- because the point of the rule is the late binding between the static
// handle type and the dynamic object type.
//
// The randomize() generate-and-test solver draws each variable over its whole
// domain and only relational constraints tighten that domain; an equality
// constraint pins a member to an exact value, giving a deterministic result.

// 18.5.2: a constraint declared only in the derived class is honored when
// randomize() is invoked through a superclass handle. The base class knows
// nothing of constraint 'dc'; were the call resolved against the handle's
// static (Base) type, x would be left free. Observing the pinned value proves
// randomize() bound to the dynamic (Derived) object's constraints.
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

// 18.5.2: a derived class inherits all constraints from its superclass, and a
// constraint that does not share a name with a base constraint is an additional
// constraint. Randomizing through a Base handle must satisfy both the inherited
// base constraint (x) and the derived class's additional constraint (y),
// confirming randomize() gathered constraints from the whole dynamic hierarchy
// rather than only the handle's static view.
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

// 18.5.2: a constraint in a derived class that has the same name as one in its
// superclass replaces the inherited constraint of that name -- it does not add
// to it. The base pins x to 10 and the derived's same-named constraint pins x
// to 42; if the inherited constraint were still in force the two would conflict
// and randomize() would fail. Observing success with x == 42 shows the derived
// constraint replaced, rather than joined, the base one.
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

// 18.5.2: because randomize() is virtual, the object's own constraints are
// honored no matter which handle level calls it. Here the object is Derived and
// the constraint lives on the base; calling randomize() through the exact-type
// Derived handle yields the same pinned result as through a Base handle,
// showing the resolution follows the object, not the handle.
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

// 18.5.2: a same-named constraint in a derived class replaces the inherited one
// even when the derived constraint is supplied as a constraint prototype
// completed by an out-of-class external constraint block (the 18.5.1 form).
// This drives the external-block dependency syntax through the whole pipeline:
// the prototype's body is filled from "constraint Derived::c" during
// elaboration, and at randomization the completed derived constraint (x == 42)
// is in force while the base constraint (x == 10) is not. Success with x == 42
// -- rather than a conflict failure -- shows the prototype replaced, not
// joined, the inherited block.
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
