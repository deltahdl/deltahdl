#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The tagged union every test below assigns, and the structure holding one as
// its member u; each occupies one line of the module, so a body's lines are
// numbered from the line after these.
constexpr const char* kUnionDecl =
    "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n";
constexpr const char* kStructDecl = "  typedef struct { u_t u; int c; } s_t;\n";

void ElaborateAndRun(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
}

// The value the run left in the variable `name`, or zero with a failed
// expectation where the run declared no such variable.
uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

// What an event-controlled update of the variable u leaves behind: w, read
// through `u.Other` at line `before` (time 1, before the event) holds the 1
// the union was given and raises nothing, y, read through `u.Valid` at the
// next line (time 3, after the event) holds the 5 the update landed and
// raises nothing, and `u.Other` at the line after that is reported against
// the Valid the update set.
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

// What an update of the member s.u leaves behind: `s.u.Other = 2` at line
// `before`, in the time step of the statement, is consistent with the Other
// the member still holds and raises nothing; y and z, read through
// `s.u.Valid` after the update, hold the 5 it landed, z after the write
// `s.u.Other = 3` at line `after` was reported against the Valid the update
// set and declined.
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

// §10.4.2 (printed page 253) evaluates a nonblocking assignment's right-hand
// side when the statement executes, and an intra-assignment event control
// (§9.4.5) holds the update until the event, so `u <= @(e) tagged Valid 5`
// lands Valid with the 5 when e triggers at time 2 and not before: at time 1
// u still holds the Other it was given (§7.3.2, printed 151), which §11.9
// (printed 304) has `u.Other` read clean, and at time 3 `u.Valid` reads
// clean and `u.Other` is reported. The event-controlled update carried the
// bits alone, so u kept the tag Other and `u.Other` raised nothing at time
// 3; the read at time 1 tells a tag landed with the update from one set
// where the statement executed.
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

// §10.4.2 (printed page 253) with §13.4.1: `u <= @(e) g()` evaluates the
// call when the statement executes, and the implicit variable of the call
// holds the tagged union value g returned, tag included (§7.3.2, printed
// 151), which the update lands in u once e triggers. The tag a call's body
// returned reached the undeferred nonblocking form and never the
// event-controlled one, so `u.Other` raised nothing at time 3.
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

// §7.3.2 (printed page 151): a tagged union's value is its tag beside the
// member's bits wherever the union stands, so `s.u <= tagged Valid 5` lands
// Valid with the 5 in the member u of s at the end of the time step (§10.4.2,
// printed 253), and §11.9 (printed 304) makes a later write into another
// member of it, `s.u.Other = 3`, a run-time error that changes nothing. The
// write into Other in the same time step, before the update lands, is
// consistent with the Other the member still holds and goes through clean.
// The member's update carried the bits alone, so s.u kept the tag Other and
// `s.u.Other = 3` after the update was not reported and overwrote the 5.
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

// §13.4.1 gives the implicit variable of `g()` the tagged union value g
// returned, tag included (§7.3.2, printed 151), and `s.u <= g()` lands it in
// the member u of s at the end of the time step (§10.4.2, printed 253), tag
// and bits, so §11.9 (printed 304) reports `s.u.Other = 3` against the Valid
// the call returned. The returned tag reached a bare variable's nonblocking
// update and never a member's.
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

}  // namespace
