#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

struct EnumAssignPlace {
  const char* src;
  const char* at;
  const char* cast_from;
  const char* cast_to;
};

constexpr EnumAssignPlace kIntegerToEnumPlaces[] = {
    {"typedef enum {A, B} e_t;\n"
     "class K;\n"
     "  e_t v;\n"
     "  function void f(); v = 1; endfunction\n"
     "endclass\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"package p;\n"
     "  typedef enum {A, B} e_t;\n"
     "  e_t v = 1;\n"
     "endpackage\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "e_t v = 1;\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "interface ifc;\n"
     "  e_t v;\n"
     "  initial v = 1;\n"
     "endinterface\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "checker ck;\n"
     "  e_t v = 1;\n"
     "endchecker\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "module t;\n"
     "  if (1) begin : g\n"
     "    e_t v;\n"
     "    initial v = 1;\n"
     "  end\n"
     "endmodule\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "module t;\n"
     "  e_t v;\n"
     "  assign v = 1;\n"
     "endmodule\n",
     "v = 1", "v = 1", "v = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "module t;\n"
     "  e_t v;\n"
     "  task automatic tk(output int o); o = 1; endtask\n"
     "  initial tk(v);\n"
     "endmodule\n",
     "tk(v)", "output int o); o = 1", "output e_t o); o = B"},
    {"typedef enum {A, B} e_t;\n"
     "module t;\n"
     "  function automatic void f(e_t a = 1); endfunction\n"
     "endmodule\n",
     "a = 1", "a = 1", "a = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "typedef struct {e_t e; int n;} s_t;\n"
     "module t;\n"
     "  s_t s;\n"
     "  initial s.e = 1;\n"
     "endmodule\n",
     "s.e = 1", "s.e = 1", "s.e = e_t'(1)"},
    {"typedef enum {A, B} e_t;\n"
     "module t;\n"
     "  e_t arr [2];\n"
     "  initial arr[0] = 1;\n"
     "endmodule\n",
     "arr[0] = 1", "arr[0] = 1", "arr[0] = B"},
};

TEST(Elaboration, DISABLED_IntegerAssignedToAnEnumIsReportedInEveryPlace) {
  for (const auto& place : kIntegerToEnumPlaces) {
    SCOPED_TRACE(place.src);
    ElabFixture f;
    ElaborateSrc(place.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "without cast",
                              LineHolding(place.src, place.at), "6.19.3"));
  }
}

TEST(Elaboration, CastToTheEnumTypeIsAcceptedInEveryPlace) {
  for (const auto& place : kIntegerToEnumPlaces) {
    std::string src = place.src;
    std::string_view from = place.cast_from;
    src.replace(src.find(from), from.size(), place.cast_to);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
