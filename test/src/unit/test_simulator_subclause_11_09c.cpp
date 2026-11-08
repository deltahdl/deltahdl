#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kUnionDecl =
    "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n";
constexpr const char* kStructDecl = "  typedef struct { u_t u; int c; } s_t;\n";

void ElaborateAndRun(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

void ExpectTagLandedAtTheEvent(SimFixture& f, uint32_t before) {
  EXPECT_EQ(ValueOf(f, "w"), 1u);
  EXPECT_EQ(ValueOf(f, "y"), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", before,
                             "11.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", before + 1,
                             "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            before + 2, "11.9"));
}

void ExpectMemberTagLanded(SimFixture& f, uint32_t before, uint32_t after) {
  EXPECT_EQ(ValueOf(f, "y"), 5u);
  EXPECT_EQ(ValueOf(f, "z"), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "assigning member 'Other'",
                             before, "11.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assigning member 'Other' of tagged union 's.u' which currently has "
      "tag 'Valid'",
      after, "11.9"));
}

TEST(TaggedUnionEval, EventControlledNbaLandsTheTagAtTheEvent) {
  SimFixture f;
  ElaborateAndRun(std::string("module t;\n") + kUnionDecl +
                      "  u_t u;\n"
                      "  event e;\n"
                      "  int w, y, z;\n"
                      "  initial begin\n"
                      "    u = tagged Other 1;\n"
                      "    u <= @(e) tagged Valid 5;\n"
                      "    #1 w = u.Other;\n"
                      "    #2 y = u.Valid;\n"
                      "    z = u.Other;\n"
                      "  end\n"
                      "  initial #2 -> e;\n"
                      "endmodule\n",
                  f);
  ExpectTagLandedAtTheEvent(f, 9);
}

TEST(TaggedUnionEval, EventControlledNbaCallResultLandsTheReturnedTag) {
  SimFixture f;
  ElaborateAndRun(std::string("module t;\n") + kUnionDecl +
                      "  u_t u;\n"
                      "  event e;\n"
                      "  int w, y, z;\n"
                      "  function u_t g();\n"
                      "    return tagged Valid 5;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    u = tagged Other 1;\n"
                      "    u <= @(e) g();\n"
                      "    #1 w = u.Other;\n"
                      "    #2 y = u.Valid;\n"
                      "    z = u.Other;\n"
                      "  end\n"
                      "  initial #2 -> e;\n"
                      "endmodule\n",
                  f);
  ExpectTagLandedAtTheEvent(f, 12);
}

TEST(TaggedUnionEval, NonblockingTaggedAssignmentToAMemberLandsTheTag) {
  SimFixture f;
  ElaborateAndRun(std::string("module t;\n") + kUnionDecl + kStructDecl +
                      "  s_t s;\n"
                      "  int y, z;\n"
                      "  initial begin\n"
                      "    s.u = tagged Other 1;\n"
                      "    s.u <= tagged Valid 5;\n"
                      "    s.u.Other = 2;\n"
                      "    #1 y = s.u.Valid;\n"
                      "    s.u.Other = 3;\n"
                      "    z = s.u.Valid;\n"
                      "  end\n"
                      "endmodule\n",
                  f);
  ExpectMemberTagLanded(f, 9, 11);
}

TEST(TaggedUnionEval, NonblockingCallResultToAMemberLandsTheReturnedTag) {
  SimFixture f;
  ElaborateAndRun(std::string("module t;\n") + kUnionDecl + kStructDecl +
                      "  s_t s;\n"
                      "  int y, z;\n"
                      "  function u_t g();\n"
                      "    return tagged Valid 5;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    s.u = tagged Other 1;\n"
                      "    s.u <= g();\n"
                      "    s.u.Other = 2;\n"
                      "    #1 y = s.u.Valid;\n"
                      "    s.u.Other = 3;\n"
                      "    z = s.u.Valid;\n"
                      "  end\n"
                      "endmodule\n",
                  f);
  ExpectMemberTagLanded(f, 12, 14);
}

TEST(TaggedUnionSim, AssignmentCarriesTheTagOfTheValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
                 "  VInt a, b, c, d;\n"
                 "  bit e = 1;\n"
                 "  initial begin\n"
                 "    a = tagged Valid 5;\n"
                 "    b = tagged Invalid;\n"
                 "    b = a;\n"
                 "    c = e ? tagged Valid 7 : tagged Invalid;\n"
                 "    d = !e ? tagged Invalid : tagged Valid 9;\n"
                 "    $display(\"%0d %0d %0d\", b.Valid, c.Valid, d.Valid);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5 7 9\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
