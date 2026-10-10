#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.5, §7.9, §7.10.2 and §7.12: an array has §7.12's manipulation methods and
// the methods its kind lists, and no others. A member select written on an
// array as though it held a handle names no method either.
TEST(ArrayMethodValidation, NameNoMethodOfTheArraysKindIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int fx[3];\n"
      "  int dy[];\n"
      "  int aa[string];\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial begin\n"
      "    q.foo();\n"
      "    dy.push_back(1);\n"
      "    aa.pop_front();\n"
      "    n = fx.size();\n"
      "    q.h.run();\n"
      "    q.push_back(1);\n"
      "    dy.delete();\n"
      "    n = aa.exists(\"a\");\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the queue 'q'", 8, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'push_back' is not a built-in method of the dynamic array 'dy'",
      9, "7.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'pop_front' is not a built-in method of the associative array 'aa'", 10,
      "7.9"));
  EXPECT_TRUE(ReportedError(
      diags, "'size' is not a built-in method of the fixed-size array 'fx'", 11,
      "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the queue 'q'", 12, "7.10.2"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 13 && d.loc.line <= 15)
        << d.loc.line << ": " << d.message;
  }
}

// §7.12, §7.12.1 and §7.12.5: an iterator argument without a with clause, a
// find locator without one and map without one are each reported as the
// design is elaborated, whether or not the call ever runs.
TEST(ArrayMethodValidation, MissingWithClauseReportedAtElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int r[$];\n"
      "  bit go = 0;\n"
      "  initial if (go) begin\n"
      "    r = q.find(x);\n"
      "    r = q.find_index;\n"
      "    r = q.map();\n"
      "    q.sort(x);\n"
      "    r = q.find with (item > 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 6,
                            "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "array locator method 'find_index' requires a 'with' clause", 7,
      "7.12.1"));
  EXPECT_TRUE(ReportedError(
      diags, "array method 'map' requires a 'with' clause", 8, "7.12.5"));
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 9,
                            "7.12"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 10u) << d.message;
}

}  // namespace
