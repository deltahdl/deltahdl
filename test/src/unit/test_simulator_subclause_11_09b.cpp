#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

void ExpectMemberTagKeptAndOtherWriteReported(RtlirDesign* design,
                                              SimFixture& f, int write_line) {
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.ToUint64(), 9u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assigning member 'Other' of tagged union 's.u' which currently has "
      "tag 'Valid'",
      write_line, "11.9"));
}

TEST(TaggedUnionEval, AssignedCallResultCarriesTheReturnedTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid (-7);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = g();\n"
      "    y = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 10, "11.9"));
}

TEST(TaggedUnionEval, AssignedCallResultTagIsCheckedAgainstAnotherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid (-7);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = g();\n"
      "    y = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            10, "11.9"));
}

TEST(TaggedUnionEval, TaggedAssignmentToTheFunctionNameReachesTheFormal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int x, y;\n"
      "  function u_t k();\n"
      "    k = tagged Valid 3;\n"
      "  endfunction\n"
      "  function u_t h();\n"
      "    h = tagged Invalid;\n"
      "  endfunction\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f(k());\n"
      "    y = f(h());\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 11, "11.9"));
}

TEST(TaggedUnionEval, ReturnedVariableCarriesItsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u, v;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    v = tagged Valid (-7);\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = tagged Other 1;\n"
      "    u = g();\n"
      "    y = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 12, "11.9"));
}

TEST(TaggedUnionEval, ReturnedVariableTagIsCheckedAgainstAnotherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u, v;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    v = tagged Valid (-7);\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = tagged Other 1;\n"
      "    u = g();\n"
      "    y = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            12, "11.9"));
}

TEST(TaggedUnionEval, NonblockingTaggedAssignmentLandsTheTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y, z;\n"
      "  initial begin\n"
      "    u = tagged Other 1;\n"
      "    u <= tagged Valid 5;\n"
      "    #1 y = u.Valid;\n"
      "    z = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            9, "11.9"));
}

TEST(TaggedUnionEval, NonblockingCallResultLandsTheReturnedTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y, z;\n"
      "  function u_t g();\n"
      "    return tagged Valid 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = tagged Other 1;\n"
      "    u <= g();\n"
      "    #1 y = u.Valid;\n"
      "    z = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 11, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            12, "11.9"));
}

TEST(TaggedUnionEval, TaggedAssignmentToAMemberSetsTheMembersTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  int y, z;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    y = s.u.Valid;\n"
      "    s.u.Other = 3;\n"
      "    z = s.u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectMemberTagKeptAndOtherWriteReported(design, f, 9);
}

TEST(TaggedUnionEval, CallResultAssignedToAMemberSetsTheMembersTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  int y, z;\n"
      "  function u_t g();\n"
      "    return tagged Valid 9;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    s.u = g();\n"
      "    y = s.u.Valid;\n"
      "    s.u.Other = 3;\n"
      "    z = s.u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectMemberTagKeptAndOtherWriteReported(design, f, 12);
}

TEST(TaggedUnionEval, LocalDeclarationInitializerTagIsReturnedWithTheLocal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y, z;\n"
      "  function u_t g();\n"
      "    static u_t v = tagged Valid (-7);\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = tagged Other 1;\n"
      "    u = g();\n"
      "    y = u.Valid;\n"
      "    z = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 12, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            13, "11.9"));
}

TEST(TaggedUnionEval, LocalTaggedUnionIsReadInTheBodyAgainstItsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  int y, z;\n"
      "  function int g();\n"
      "    static u_t v = tagged Valid (-7);\n"
      "    z = v.Other;\n"
      "    return v.Valid;\n"
      "  endfunction\n"
      "  initial y = g();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'v' which currently has tag 'Valid'",
                            6, "11.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 7, "11.9"));
}

std::string PairUnionLocalSrc(const std::string& rest) {
  return "module t;\n"
         "  typedef struct { int a, b; } pair_t;\n"
         "  typedef union tagged { void None; pair_t Add; int One; } u_t;\n"
         "  int y;\n" +
         rest + "endmodule\n";
}

TEST(TaggedUnionEval, LocalTaggedPatternInitializerIsPlacedByTheMember) {
  EXPECT_EQ(
      RunAndGet(PairUnionLocalSrc("  function int g();\n"
                                  "    static u_t v = tagged Add '{3, 8'd4};\n"
                                  "    return v.Add.a * 10 + v.Add.b;\n"
                                  "  endfunction\n"
                                  "  initial y = g();\n"),
                "y"),
      34u);
}

TEST(TaggedUnionEval, LocalTaggedPatternInitializerReachesTheCallerPlaced) {
  EXPECT_EQ(
      RunAndGet(PairUnionLocalSrc("  u_t u;\n"
                                  "  function u_t g();\n"
                                  "    static u_t v = tagged Add '{3, 8'd4};\n"
                                  "    return v;\n"
                                  "  endfunction\n"
                                  "  initial begin\n"
                                  "    u = g();\n"
                                  "    y = u.Add.a * 10 + u.Add.b;\n"
                                  "  end\n"),
                "y"),
      34u);
}

TEST(TaggedUnionEval, LocalKeyedTaggedPatternInitializerIsPlacedByName) {
  EXPECT_EQ(RunAndGet(PairUnionLocalSrc(
                          "  function int g();\n"
                          "    static u_t v = tagged Add '{b: 4, a: 3};\n"
                          "    return v.Add.a * 10 + v.Add.b;\n"
                          "  endfunction\n"
                          "  initial y = g();\n"),
                      "y"),
            34u);
}

}  // namespace
