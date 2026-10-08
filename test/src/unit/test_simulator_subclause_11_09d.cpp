#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates and runs `src`, answering the variable `y` it declares so a
// test reads the value a member access produced beside what the run
// reported.
Variable* RunReadingY(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  EXPECT_NE(y, nullptr);
  return y;
}

// Elaborates and runs `src` with standard output captured, answering the
// text the run printed.
std::string RunPrinting(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §7.3.2 (printed page 151): a tagged union's value is its tag beside the
// member's bits wherever the union stands, so `s.u = tagged Valid 9` gives
// the member u of s the tag Valid with the 9, and §11.9 (printed 304) has
// `s.u.Valid` read consistently with that tag: the 9 comes back and nothing
// is reported. The read checked the layout of s alone, a structure with no
// tag of its own, so this was clean before as well; it is the reading beside
// the one below that tells a check against the member's tag from none.
TEST(TaggedUnionEval, MemberReadConsistentWithTheMembersTagIsClean) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    y = s.u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
}

// §11.9 (printed page 304): reading a member inconsistent with the current
// tag is a run-time error, and the tag `s.u = tagged Valid 9` gives the
// member u of s is Valid (§7.3.2, printed 151), so `y = s.u.Other` is
// reported against it, naming the union as the access spelled it, and y
// takes the unknown value a refused read yields rather than the 9 Valid
// holds. The read split the access into the variable s and the path
// u.Other, asked s's layout, a structure, for a tag, and let the read through
// with the 9.
TEST(TaggedUnionEval, MemberReadIsCheckedAgainstTheMembersTag) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    y = s.u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_FALSE(y->value.IsKnown());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Other' of tagged union 's.u' which "
      "currently has tag 'Valid'",
      8, "11.9"));
}

// §7.3.2 (printed page 151) puts no bound on how deep the structure holding
// the tagged union stands: `m.s.u = tagged Valid 9` tags the union two
// members down, under the key the whole path spells, and §11.9 (printed 304)
// checks `m.s.u.Other` against that tag while `m.s.u.Valid` reads the 9.
// The walk descends a segment at a time, so the union is found at any depth.
TEST(TaggedUnionEval, TwoLevelMemberReadIsCheckedAgainstItsUnionsTag) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  typedef struct { s_t s; int d; } m_t;\n"
      "  m_t m;\n"
      "  logic [31:0] y, z;\n"
      "  initial begin\n"
      "    m.s.u = tagged Valid 9;\n"
      "    y = m.s.u.Valid;\n"
      "    z = m.s.u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(z, nullptr);
  EXPECT_FALSE(z->value.IsKnown());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Other' of tagged union 'm.s.u' which "
      "currently has tag 'Valid'",
      10, "11.9"));
}

// §21.2.1.6 (printed page 662): a tagged union prints under %p as its tag
// beside the currently valid member's value, and §7.3.2 (printed 151) has the
// member u of s hold the tag `s.u = tagged Valid 9` gave it, so `s.u` prints
// as the variable `u` would after `u = tagged Valid 9`: '{Valid:9}. The
// formatter asked for a tag by the argument's name, which a member access has
// none of, and printed the member's bits as one number.
TEST(TaggedUnionEval, MemberTaggedUnionPrintsTagAndValue) {
  SimFixture f;
  auto out = RunPrinting(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    $display(\"%p\", s.u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:9}\n");
}

// §11.9 packs a tagged union expression's member expression against the
// member's type wherever the expression stands, and §11.4.11 has a known
// predicate of `?:` yield the arm it selects. So a tagged expression that is
// an arm of `?:`, positional or by name, and one that is the member expression
// of another tagged expression, keep the first member of their structure:
// reg1 1 and 19, cc 2. Concatenated at the items' own widths and cut to the
// member's, the first member was lost and read 0.
TEST(TaggedUnionSim, ANestedTaggedExpressionKeepsItsStructsFirstMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef union tagged {\n"
      "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
      "    union tagged { bit [9:0] JmpU;\n"
      "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC; } Jmp;\n"
      "  } Instr;\n"
      "  Instr i1, i2, i3;\n"
      "  bit [4:0] e1 = 1, e2 = 2, ed = 3;\n"
      "  bit e = 1;\n"
      "  initial begin\n"
      "    i1 = e ? tagged Add '{e1, 4, ed}\n"
      "           : tagged Add '{reg2: e2, regd: 3, reg1: 19};\n"
      "    i3 = !e ? tagged Add '{e1, 4, ed}\n"
      "            : tagged Add '{reg2: e2, regd: 3, reg1: 19};\n"
      "    i2 = tagged Jmp (tagged JmpC '{2, 83});\n"
      "    $display(\"%0d %0d %0d %0d %0d\", i1.Add.reg1, i1.Add.reg2,\n"
      "             i3.Add.reg1, i2.Jmp.JmpC.cc, i2.Jmp.JmpC.addr);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 19 2 83\n");
}

// §11.9 (printed page 304): a member read inconsistent with the tag is a
// run-time error, and the read gives all x. A structure so read, stored and
// then read for its string member, gives the empty string: the member's x
// handle names no text.
TEST(TaggedUnionEval, AStringMemberOfAStructureReadAgainstTheTagIsEmpty) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  typedef union tagged {int i; pair_t p;} u_t;\n"
      "  u_t u;\n"
      "  pair_t q;\n"
      "  initial begin\n"
      "    u = tagged i 5;\n"
      "    q = u.p;\n"
      "    $display(\"[%s]\", q.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "accessing member 'p' of tagged union 'u' which "
                            "currently has tag 'i'",
                            8, "11.9"));
}

}  // namespace
