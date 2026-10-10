#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.12.1 has find, find_first, find_last, min, max and unique return a queue
// of the array's element type, so over an array of an enumeration a queue of
// that enumeration, which a queue of the enumeration takes without a cast.
TEST(Elaboration, EnumArrayLocatorResultAssignedToEnumQueueAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  e_t ea[2];\n"
      "  e_t eq[$];\n"
      "  initial begin\n"
      "    eq = ea.min;\n"
      "    eq = ea.max();\n"
      "    eq = ea.unique;\n"
      "    eq = ea.find with (item == A);\n"
      "    eq = ea.find_first with (item == B);\n"
      "    eq = ea.find_last(x) with (x != A);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The element locators of an array of int return a queue of int, and the index
// locators a queue of int whatever the elements are; neither is a value of the
// enumeration, so each needs the cast.
TEST(Elaboration, IntQueueFromLocatorAssignedToEnumQueueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  e_t ea[2];\n"
      "  int ia[2];\n"
      "  e_t eq[$];\n"
      "  initial begin\n"
      "    eq = ia.min;\n"
      "    eq = ea.find_index with (item == A);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 7,
                            "6.19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 8,
                            "6.19.3"));
}

// §7.12.1 has an index locator over an associative array return a queue of the
// index type, so over one indexed by an enumeration a queue of that
// enumeration, at module scope or in a block; over an array indexed by int, or
// over any other kind of array, a queue of int, which needs the cast.
TEST(Elaboration, EnumKeyedIndexLocatorResultAssignedToEnumQueue) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  int aa[e_t];\n"
      "  int ka[int];\n"
      "  e_t eq[$];\n"
      "  initial begin\n"
      "    int la[e_t];\n"
      "    eq = aa.find_index with (item > 0);\n"
      "    eq = la.unique_index;\n"
      "    eq = ka.find_first_index with (item > 0);\n"
      "    eq = aa.min;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast",
                            10, "6.19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast",
                            11, "6.19.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "integer assigned to enum variable without cast",
                             8, "6.19.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "integer assigned to enum variable without cast",
                             9, "6.19.3"));
}

}  // namespace
