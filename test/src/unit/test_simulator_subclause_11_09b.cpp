#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Runs a design whose initial block writes `s.u = tagged Valid 9` (or the
// call returning it), reads y from s.u.Valid, writes s.u.Other = 3 at
// `write_line`, and reads z from s.u.Valid: y and z both read 9, the
// declined write leaving the 9, and the write is reported against Valid.
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

// §7.3.2 (printed page 151): a tagged union value carries its tag beside the
// member's bits, and §13.4.1 (printed 342) gives the implicit variable of a
// call the return type, so `u = g()` with g returning `tagged Valid -7`
// assigns u a value tagged Valid, which §11.9 (printed 304) has `u.Valid`
// read consistently with. The store copied the bits alone, reading a tag off
// a `tagged` right-hand side and a call being none, so u was read against no
// tag at all; the value is what says the member reached u as well.
TEST(TaggedUnionEval, AssignedCallResultCarriesTheReturnedTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid -7;\n"
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

// §11.9 (printed page 304): reading a member inconsistent with the current
// tag is a run-time error, and the tag `u = g()` gives u is the one g's
// `return tagged Valid -7` gave its result. With the bits copied and no tag,
// `u.Other` raised nothing.
TEST(TaggedUnionEval, AssignedCallResultTagIsCheckedAgainstAnotherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid -7;\n"
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

// §13.4.1 (printed page 342): a function's value may be given by assigning
// the variable that has the function's own name, and §7.3.2 (printed 151)
// has `k = tagged Valid 3` give it a tag beside the bits, which §13.5.1
// copies into the formal of `f(k())` with the value and §11.9 (printed 304)
// checks the body's read against. The assignment set the tag under the
// function's name alone, so the formal took the result untagged: `a.Valid`
// of `h()`, whose body assigns `tagged Invalid`, raised nothing. The 3 read
// through k's result says the value travels too, whichever way the tag goes.
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

// §7.3.2 (printed page 151): a tagged union variable's value is its tag
// beside the member's bits, so `return v` hands out the tag v holds, and
// §13.4.1 (printed 342) gives the implicit variable of `g()` that value,
// which `u = g()` copies into u. The return recorded a tag from a `tagged`
// expression alone, so u kept the Other it held and `u.Valid` was reported
// against it; the -7 read through u says the bits travel beside the tag.
TEST(TaggedUnionEval, ReturnedVariableCarriesItsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u, v;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    v = tagged Valid -7;\n"
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

// §11.9 (printed page 304): reading a member inconsistent with the current
// tag is a run-time error, and the tag `u = g()` gives u is the Valid the
// returned variable held. With u's earlier Other left standing, `u.Other`
// raised nothing.
TEST(TaggedUnionEval, ReturnedVariableTagIsCheckedAgainstAnotherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u, v;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    v = tagged Valid -7;\n"
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

// §10.4.2 (printed page 253): a nonblocking assignment evaluates its
// right-hand side when the statement executes and lands the value in the NBA
// region, and §7.3.2 (printed 151) makes a tagged union's value its tag beside
// the member's bits, so `u <= tagged Valid 5` lands Valid with the 5; §11.9
// (printed 304) then checks `u.Valid` clean and reports `u.Other`. The update
// carried the bits alone, so u kept the Other it held: `u.Valid` was reported
// and `u.Other` raised nothing.
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

// §10.4.2 (printed page 253) with §13.4.1 (printed 342): `u <= g()` evaluates
// the call when the statement executes, and the implicit variable of the
// call holds the tagged union value g returned, tag included (§7.3.2, printed
// 151), which the update lands in u. The tag a call's body returned reached a
// blocking assignment's target and never a nonblocking one's, so `u.Valid`
// was reported against the Other u held and `u.Other` raised nothing.
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

// §7.3.2 (printed page 151): a tagged union's value is its tag beside the
// member's bits wherever the union stands, so `s.u = tagged Valid 9` gives
// the member u of s the tag Valid with the 9, and §11.9 (printed 304) makes a
// later write into another member of it, `s.u.Other = 3`, a run-time error
// that changes nothing. The member store took the bits alone and no tag was
// kept for a member, so the write into Other went through unreported and the
// 9 was gone.
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

// §13.4.1 (printed page 342) gives the implicit variable of `g()` the tagged
// union value g returned, tag included (§7.3.2, printed 151), and `s.u = g()`
// copies it into the member u of s, tag and bits, so §11.9 (printed 304)
// reports `s.u.Other = 3` against the Valid the call returned. The returned
// tag reached a bare variable's target and never a member's.
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

// §11.9 (printed page 304) lets a tagged union variable be initialized with
// a tagged union expression, and §7.3.2 (printed 151) has its value carry the
// tag beside the member's bits wherever the variable stands -- a function
// body's own local (§13.3, printed 337) included -- so `u_t v = tagged Valid
// -7; return v;` hands the caller a value tagged Valid, which `u = g()`
// copies into u over the Other it held. The local was created with no layout
// and no tag, so the return recorded none: u kept its Other, `u.Valid` was
// reported against it and `u.Other` raised nothing. The -7 read through
// `u.Valid` says the bits travel beside the tag.
TEST(TaggedUnionEval, LocalDeclarationInitializerTagIsReturnedWithTheLocal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y, z;\n"
      "  function u_t g();\n"
      "    u_t v = tagged Valid -7;\n"
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

// §7.2.1 with §6.18: a local declared by the typedef's name has the members
// the union declares, so `v.Valid` inside the body is the window of the
// member, and §11.9 (printed 304) checks each such read against the tag the
// local's `tagged` initializer gave it. The local had no layout bound to its
// name, so `v.Valid` was read through no member at all, and no tag, so
// `v.Other` raised nothing; -7 through `v.Valid` says the member is reached
// and the report at the body's line says the tag is the initializer's.
TEST(TaggedUnionEval, LocalTaggedUnionIsReadInTheBodyAgainstItsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  int y, z;\n"
      "  function int g();\n"
      "    u_t v = tagged Valid -7;\n"
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

// A design declaring `pair_t`, a structure of two ints, and `u_t`, a tagged
// union holding a pair_t under Add, followed by `rest` -- the subroutine
// declaring a u_t local from a `tagged Add '{...}` initializer and the
// initial block reading y from it -- so the three cases below read the
// local's a * 10 + b through one pair of layouts.
std::string PairUnionLocalSrc(const std::string& rest) {
  return "module t;\n"
         "  typedef struct { int a, b; } pair_t;\n"
         "  typedef union tagged { void None; pair_t Add; int One; } u_t;\n"
         "  int y;\n" +
         rest + "endmodule\n";
}

// §11.9 (printed page 304) lets a tagged union variable be initialized with
// a tagged union expression whose braces are a §10.9.2 structure assignment
// pattern, and §10.9.2 (printed 263) evaluates each member expression in the
// context of an assignment to the member it initializes -- for `'{3, 8'd4}`
// against pair_t, 3 into a and 4 into b. A body local's initializer was
// evaluated with no layout to place the pattern by, so its elements were
// concatenated in written order at their self-determined widths: forty bits
// holding 3 above the byte 4, which the union's frame took as a = 0 and b =
// 0x304, reading 772 where the members hold 34.
TEST(TaggedUnionEval, LocalTaggedPatternInitializerIsPlacedByTheMember) {
  EXPECT_EQ(RunAndGet(PairUnionLocalSrc("  function int g();\n"
                                        "    u_t v = tagged Add '{3, 8'd4};\n"
                                        "    return v.Add.a * 10 + v.Add.b;\n"
                                        "  endfunction\n"
                                        "  initial y = g();\n"),
                      "y"),
            34u);
}

// §7.3.2 (printed page 151) has the local's value carry Add's tag beside the
// member's bits, and §13.4.1 (printed 342) hands `return v` to the caller as
// the function's value, so `u = g()` gives u the members the initializer
// placed. The bits reaching u were the concatenation the body's local held,
// so `u.Add.a * 10 + u.Add.b` read 772 from a = 0 and b = 0x304 where the
// placed members read 34.
TEST(TaggedUnionEval, LocalTaggedPatternInitializerReachesTheCallerPlaced) {
  EXPECT_EQ(RunAndGet(PairUnionLocalSrc("  u_t u;\n"
                                        "  function u_t g();\n"
                                        "    u_t v = tagged Add '{3, 8'd4};\n"
                                        "    return v;\n"
                                        "  endfunction\n"
                                        "  initial begin\n"
                                        "    u = g();\n"
                                        "    y = u.Add.a * 10 + u.Add.b;\n"
                                        "  end\n"),
                      "y"),
            34u);
}

// §10.9.2 (printed page 263) also lets a structure pattern name its members,
// in any order, so `'{b: 4, a: 3}` gives a 3 and b 4 whatever position each
// is written at. The keyed pattern was concatenated in written order like the
// positional one, 4 landing in a and 3 in b, so the body read 43 where the
// named members read 34.
TEST(TaggedUnionEval, LocalKeyedTaggedPatternInitializerIsPlacedByName) {
  EXPECT_EQ(
      RunAndGet(PairUnionLocalSrc("  function int g();\n"
                                  "    u_t v = tagged Add '{b: 4, a: 3};\n"
                                  "    return v.Add.a * 10 + v.Add.b;\n"
                                  "  endfunction\n"
                                  "  initial y = g();\n"),
                "y"),
      34u);
}

}  // namespace
