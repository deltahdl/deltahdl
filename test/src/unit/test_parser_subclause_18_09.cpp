#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

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
