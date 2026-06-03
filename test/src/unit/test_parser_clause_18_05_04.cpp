#include "fixture_parser.h"

using namespace delta;

namespace {

// 18.5.4 / Syntax 18-4: a uniqueness_constraint ("unique { range_list }") is a
// valid constraint_expression. A group of singular variables parses cleanly.
TEST(ConstraintUniqueParsing, SingularVariableGroupAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand byte a;\n"
      "  rand byte b;\n"
      "  rand byte excluded;\n"
      "  constraint u { unique {a, b, excluded}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.4: the range_list of a uniqueness_constraint may name an array slice
// alongside singular variables, as in the unique {b, a[2:3], excluded} example.
TEST(ConstraintUniqueParsing, ArraySliceMemberAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand byte a[5];\n"
      "  rand byte b;\n"
      "  rand byte excluded;\n"
      "  constraint u { unique {b, a[2:3], excluded}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}
