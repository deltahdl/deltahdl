#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.10.2: a module instance parameter value assignment uses one of two forms,
// assignment by ordered list or assignment by name. The two forms shall not be
// mixed; the assignments for a particular instance shall be entirely by order
// or entirely by name. The parser enforces this while reading the #(...) list,
// and Parser::ParseParamValueAssignment in src/parser/parser_inst.cpp files
// that report under §23.3.2 rather than under this file's own subclause.

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

// §23.10.2 makes the value of a parameter value assignment an expression, and
// §6.20.3 makes the value of a type parameter a data type. §7.4.1 (printed page
// 153) allows more than one packed dimension on a vector type, declaring
// `bit [0:3] [7:0] packedArray;` as its example, so `logic [3:0][7:0]` is a
// data type a type parameter may be given. The parser used to take the first
// bracketed range after a type keyword and leave the second, which reported a
// missing right parenthesis at a position the source is correct at.
TEST(ModuleInstanceParameterValueAssignment,
     NamedTypeValueTakesEveryPackedDimension) {
  auto r = Parse("module top; child #(.T(logic [3:0][7:0])) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// The same value written by order, which Parser::ParseParamValueEntry in
// src/parser/parser_inst.cpp parses through a different line than the named
// form.
TEST(ModuleInstanceParameterValueAssignment,
     OrderedTypeValueTakesEveryPackedDimension) {
  auto r = Parse("module top; child #(logic [3:0][7:0]) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// One packed dimension is the form that parsed before the loop above existed,
// so it is pinned here against a fix that reroutes it.
TEST(ModuleInstanceParameterValueAssignment,
     NamedTypeValueTakesOnePackedDimension) {
  auto r = Parse("module top; child #(.T(logic [15:0])) u0(); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
