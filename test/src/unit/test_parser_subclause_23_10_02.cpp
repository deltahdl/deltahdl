#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.10.2: a module instance parameter value assignment uses one of two forms,
// assignment by ordered list or assignment by name. The two forms shall not be
// mixed; the assignments for a particular instance shall be entirely by order
// or entirely by name. The parser enforces this while reading the #(...) list,
// and src/parser/parser_inst.cpp:146 files that report under §23.3.2 rather
// than under this file's own subclause.

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
  // The inconsistency surfaces only at the final entry: a by-name list ending
  // with a positional value is still a prohibited mixture, so the parser must
  // scan the whole list rather than just the first pair.
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

}  // namespace
