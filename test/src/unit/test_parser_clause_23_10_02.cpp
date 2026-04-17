#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment, MixedOrderedThenNamedRejected) {
  auto r = Parse("module m; sub #(8, .B(4)) u0(a); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstanceParameterAssignment, MixedNamedThenOrderedRejected) {
  auto r = Parse("module m; sub #(.A(1), 2) u0(a); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstanceParameterAssignment, MixedThreeWayWithOrderedTailRejected) {
  auto r = Parse("module m; sub #(.A(1), .B(2), 3) u0(a); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
