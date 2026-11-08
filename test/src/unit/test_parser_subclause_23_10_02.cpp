#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterValueAssignment, OrderedFollowedByNamedIsRejected) {
  auto r = Parse("module top; child #(8, .B(4)) u0(); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named parameter value assignments cannot be mixed",
      1, "23.3.2"));
}

TEST(ModuleInstanceParameterValueAssignment, NamedFollowedByOrderedIsRejected) {
  auto r = Parse("module top; child #(.A(8), 4) u0(); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named parameter value assignments cannot be mixed",
      1, "23.3.2"));
}

TEST(ModuleInstanceParameterValueAssignment, MixingDetectedBeyondFirstEntry) {
  auto r = Parse("module top; child #(.A(1), .B(2), 3) u0(); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named parameter value assignments cannot be mixed",
      1, "23.3.2"));
}

TEST(ModuleInstanceParameterValueAssignment, EntirelyByOrderIsAccepted) {
  auto r = Parse("module top; child #(8, 4) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstanceParameterValueAssignment, EntirelyByNameIsAccepted) {
  auto r = Parse("module top; child #(.A(8), .B(4)) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedTypeValueTakesEveryPackedDimension) {
  auto r = Parse("module top; child #(.T(logic [3:0][7:0])) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstanceParameterValueAssignment,
     OrderedTypeValueTakesEveryPackedDimension) {
  auto r = Parse("module top; child #(logic [3:0][7:0]) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedTypeValueTakesOnePackedDimension) {
  auto r = Parse("module top; child #(.T(logic [15:0])) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
