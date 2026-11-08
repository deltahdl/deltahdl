#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
