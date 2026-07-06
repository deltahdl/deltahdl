#include "fixture_elaborator.h"

using namespace delta;

namespace {

// These tests observe the elaborator rule of 18.5.3 that governs a real-valued
// range within a distribution: such a range shall use the :/ operator and shall
// specify a weight. The rule is type-directed, so it lives at the elaborator
// stage, which alone knows that the distributed variable is real; the parser
// accepts the syntax regardless. Each program is built from real class source
// so the check runs over the elaborated distribution, not a hand-built state.

// 18.5.3: a real-valued range that uses :/ with a weight is well formed and
// elaborates.
TEST(RealDistRange, DivideOperatorWithWeightAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0] :/ 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.3: a real-valued range shall not use the := operator (which spreads a
// weight per element — meaningful only for an integral range), so a := range on
// a real variable is rejected.
TEST(RealDistRange, AssignOperatorRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.3: a real-valued range shall specify a weight; a bare range (which
// defaults to := 1) omits the required weight and is rejected.
TEST(RealDistRange, MissingWeightRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0]}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.3: the rule is confined to real-valued ranges. An integral range may use
// the := operator, so the same shape on an integral variable elaborates.
TEST(RealDistRange, IntegralRangeWithAssignAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x dist {[1:3] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.3: the distributed variable may be an inherited real property; the
// target is resolved through the base-class chain, so a := range on it is still
// rejected.
TEST(RealDistRange, InheritedRealTargetChecked) {
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  rand real a;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { a dist {[1.0:3.0] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
