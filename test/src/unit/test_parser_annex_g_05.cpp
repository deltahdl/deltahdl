// IEEE 1800-2023 Annex G.5 (Std package -- Randomize).
//
// Section G.5 gives the form of a call of std::randomize as the randomize_call
// of A.8.2 applicable to it:
//
//   randomize { attribute_instance } [ ( [ variable_identifier_list ] ) ]
//       [ with constraint_block ]
//
// The list is a variable_identifier_list, narrower than the property list
// 18.11 gives the class method randomize(), which admits a member access and a
// select. These tests observe the parser accepting the forms the summary
// allows and rejecting, at the argument and under G.5, an argument to
// std::randomize that is no variable identifier -- an expression, a literal, a
// member access and a select -- where the class method's list admits the last
// two.

#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// G.5: an empty list, a list of variables and a with block each parse.
TEST(RandomizeStdPackageParser, TheFormsOfTheSummaryParse) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  int b;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = std::randomize();\n"
      "    ok = std::randomize(a);\n"
      "    ok = std::randomize(a, b);\n"
      "    ok = std::randomize(a, b) with { a < b; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// G.5: an argument to std::randomize that is no variable identifier is
// rejected at the argument under G.5 -- an expression, a literal, a member
// access and a select alike -- while a variable beside them is not.
TEST(RandomizeStdPackageParser, AnArgumentShallBeAVariableIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ok = std::randomize(a, b + 1);\n"
      "    ok = std::randomize(1);\n"
      "    ok = std::randomize(c.d);\n"
      "    ok = std::randomize(arr[0]);\n"
      "    ok = std::randomize(a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 3,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 4,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 5,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 6,
      "G.5"));
  for (const auto& d : r.diags) {
    EXPECT_NE(d.loc.line, 7u);
  }
}

// 18.11 with A.8.2: the class method randomize() takes the names of the
// object's properties, which A.8.2 writes as the variable_identifier_list
// G.5 gives std::randomize, so a member access and a select are rejected at
// the argument there too (#8060).
TEST(RandomizeStdPackageParser, TheClassMethodTakesVariableIdentifiersToo) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ok = obj.randomize(c.d);\n"
      "    ok = obj.randomize(arr[0]);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "randomize() arguments shall be object property names, not expressions";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "18.11"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "18.11"));
}

}  // namespace
