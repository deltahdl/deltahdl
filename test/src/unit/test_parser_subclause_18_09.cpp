#include "fixture_parser.h"

using namespace delta;

namespace {

// 18.9: the void form object[.constraint_identifier].constraint_mode(on_off)
// takes a single bit argument.
TEST(ConstraintModeCall, VoidFormParses) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  rand integer source_value;\n"
              "  constraint filter1 { source_value > 2; }\n"
              "endclass\n"
              "function void toggle(Packet p);\n"
              "  p.filter1.constraint_mode(0);\n"
              "endfunction\n"));
}

// 18.9: the nonvoid form is called without an argument to query the current
// active state of the named constraint.
TEST(ConstraintModeCall, NonvoidQueryFormParses) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  rand integer source_value;\n"
              "  constraint filter1 { source_value > 2; }\n"
              "endclass\n"
              "function integer query(Packet p);\n"
              "  return p.filter1.constraint_mode();\n"
              "endfunction\n"));
}

// 18.9: when called as a void function with no constraint name, the operation
// applies to all constraints within the object.
TEST(ConstraintModeCall, UnnamedVoidFormParses) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  rand integer source_value;\n"
              "  constraint filter1 { source_value > 2; }\n"
              "endclass\n"
              "function void disable_all(Packet p);\n"
              "  p.constraint_mode(0);\n"
              "endfunction\n"));
}

}  // namespace
