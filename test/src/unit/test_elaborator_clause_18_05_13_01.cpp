#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.13.1: soft constraints can only be specified on random variables. A soft
// preference on an ordinary rand variable is within that rule and elaborates.
TEST(SoftConstraintVariable, SoftOnRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { soft x == 3; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: a soft constraint may not be specified for a randc variable.
// Preferring a value for a randc member is therefore an error.
TEST(SoftConstraintVariable, SoftOnRandcVariableRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { soft x == 3; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: the prohibition holds however the randc variable is named within
// the soft expression — here inside a set-membership preference rather than a
// plain equality.
TEST(SoftConstraintVariable, SoftOnRandcInSetMembershipRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft x inside {[1:2]}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: the restriction applies only to soft constraints. A randc variable
// is free to appear in an ordinary (hard) constraint, so a class whose only
// soft constraint is on a rand variable elaborates even though it references a
// randc member in a hard constraint.
TEST(SoftConstraintVariable, RandcInHardConstraintNotFlagged) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { x < y; soft y == 3; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: the restriction is confined to the soft constraint's own
// expression. A hard constraint that follows a soft constraint in the same
// block may freely reference a randc variable; the soft scan ends at the soft
// expression's ';', so the randc named only in the later hard constraint is not
// flagged and the class elaborates.
TEST(SoftConstraintVariable, RandcInHardConstraintAfterSoftNotFlagged) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft y == 3; x < y; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: the prohibition is enforced across every soft constraint in the
// block, not just the first. With two soft constraints — one on a rand variable
// and a later one on a randc variable — the randc soft constraint is still
// rejected.
TEST(SoftConstraintVariable, RandcInLaterSoftConstraintRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft y == 1; soft x == 2; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.13.1: the soft variable is resolved against the class and its base
// chain, so a soft constraint on a randc variable inherited from a superclass
// is likewise rejected.
TEST(SoftConstraintVariable, SoftOnInheritedRandcRejected) {
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc bit [3:0] cy;\n"
             "endclass\n"
             "class D extends B;\n"
             "  rand int r;\n"
             "  constraint c { soft cy < r; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
