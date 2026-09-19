#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

// §6.19.5.6 Name()
//
// Prototype:  function string name();
//
// Normative rules owned by this subclause:
//   R1  name() returns the string representation (the enumeration name) of the
//       value the given enumeration variable currently holds.
//   R2  if that value is not a member of the enumeration, name() returns the
//       empty string "".
//   R1 also reaches a base that is itself a call of first(), last(), next() or
//       prev(), since §6.19.5.1 through §6.19.5.4 give those the enumeration's
//       own type as their result; name() then reports the member that result
//       is.
//
// Which string name() yields is decided entirely by how the enumeration is
// declared (which names map to which values, §6.19) and by how the variable
// gets the value it holds (a declaration default, a procedural assignment, or a
// cast, §6.19). The name() call itself only looks that value up. Because the
// result depends on how the enum type and the current value are produced, every
// test builds the enumeration and the value from real source and drives the
// whole pipeline (parse -> elaborate -> lower -> run). The returned string is
// observed through the §6.16 string == operator, reading back the 1-bit result
// of comparing the name against an expected literal. There is no fixed-width or
// otherwise input-independent facet of name() to pin with a single-stage test:
// the result is a string whose width is the name length, itself a product of
// the declaration.

using namespace delta;

namespace {

// R1: a value that is a middle member reports that member's name.
TEST(EnumNameMethod, NameOfMiddleMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = GREEN;
    s = c.name();
    r = (s == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, boundary: the first member's name.
TEST(EnumNameMethod, NameOfFirstMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = RED;
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, boundary: the last member's name.
TEST(EnumNameMethod, NameOfLastMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = BLUE;
    s = c.name();
    r = (s == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1: a single-member enumeration reports its sole name.
TEST(EnumNameMethod, NameOfSingleMemberEnum) {
  const char* src = R"(
module m;
  typedef enum { SOLE } one_t;
  one_t o;
  string s;
  int r;
  initial begin
    o = SOLE;
    s = o.name();
    r = (s == "SOLE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, declaration default: an enum variable that is never assigned holds the
// value of its first member (0), so name() reports the first member's name.
TEST(EnumNameMethod, NameOfDefaultInitializedIsFirstMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, value produced by a declaration initializer on the enum variable (§6.19):
// the variable is seeded with a member at its own declaration rather than by a
// later procedural assignment, and name() reports that member's name.
TEST(EnumNameMethod, NameOfDeclarationInitializedMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c = GREEN;
  string s;
  int r;
  initial begin
    s = c.name();
    r = (s == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, explicit packed base type (§6.19 enum_base_type): declaring the enum over
// a sized base type does not change the name each value maps to.
TEST(EnumNameMethod, NameWithExplicitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [2:0] { A, B, C, D } e_t;
  e_t v;
  string s;
  int r;
  initial begin
    v = C;
    s = v.name();
    r = (s == "C");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, explicit member values (§6.19): the name lookup follows the declared
// value-to-name mapping even when the values are sparse and non-contiguous.
TEST(EnumNameMethod, NameWithExplicitMemberValues) {
  const char* src = R"(
module m;
  typedef enum { LOW = 2, MID = 50, HIGH = 9999 } sparse_t;
  sparse_t v;
  string s;
  int r;
  initial begin
    v = MID;
    s = v.name();
    r = (s == "MID");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, value produced by a cast into the enum's set (§6.19): casting an in-range
// integer to the enum type yields a member value, and name() reports that
// member's name.
TEST(EnumNameMethod, NameFromCastToMemberValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(2);
    s = c.name();
    r = (s == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, §6.19.2 range members: a name written with the range shorthand expands
// into one member per index (OP[3] -> OP0, OP1, OP2), and name() reports the
// expanded member's name.
TEST(EnumNameMethod, NameOfRangeExpandedMember) {
  const char* src = R"(
module m;
  typedef enum { OP[3] } op_t;
  op_t v;
  string s;
  int r;
  initial begin
    v = OP1;
    s = v.name();
    r = (s == "OP1");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, result used directly as a string operand: name() need not be routed
// through an intermediate string variable; its result compares directly.
TEST(EnumNameMethod, NameResultUsedDirectlyAsOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, result in a declaration-initializer position: a string variable is seeded
// from name() at its declaration, exercising the variable-initialization
// lowering path rather than a procedural assignment.
TEST(EnumNameMethod, NameResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string nm = c.name();
  int r;
  initial r = (nm == "RED");
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R2: a value that is not a member of the enumeration (an out-of-range cast,
// §6.19) yields the empty string.
TEST(EnumNameMethod, NameOfNonMemberIsEmpty) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(99);
    s = c.name();
    r = (s == "");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R2, negative contrast: a non-member value's name is not any declared member
// name -- it is empty, so comparing it against a real member name is false.
TEST(EnumNameMethod, NameOfNonMemberIsNotAMemberName) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  string s;
  int r;
  initial begin
    c = color_t'(7);
    s = c.name();
    r = (s == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// R1, base written as an enum method call: §6.19.5.3 gives next() the
// enumeration's own type as its result, so name() applies to that result and
// reports the member after the variable's own. Read back through the variable
// itself the name would be GREEN; the empty string of a call that never
// resolved compares false.
TEST(EnumNameMethod, NameOfNextCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = (c.next().name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, base written as last() (§6.19.5.2): the name reported is the last
// member's whatever the variable holds, here the first member.
TEST(EnumNameMethod, NameOfLastCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = (c.last().name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, base written as first() (§6.19.5.1) on a variable holding the last
// member: the name is the first member's, not the variable's own.
TEST(EnumNameMethod, NameOfFirstCallResultOnLastMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.first().name() == "RED");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, base written as prev() (§6.19.5.4): the name is the member before the
// variable's own.
TEST(EnumNameMethod, NameOfPrevCallResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.prev().name() == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, base written as next(N) with a step count (§6.19.5.3): the name is the
// member two past the variable's own, which is neither the variable's own nor
// the one a default step would give.
TEST(EnumNameMethod, NameOfNextCallResultWithStepCount) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE, YELLOW } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = (c.next(2).name() == "BLUE");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, a chain of two enum-typed calls under name(): first() yields the
// enumeration type, next() applies to that result, and name() to the next's.
TEST(EnumNameMethod, NameOfFirstThenNextChain) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = (c.first().next().name() == "GREEN");
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// §6.19.5.3, chained on itself: next() applied to the result of next() steps
// twice from the variable's value.
TEST(EnumNameMethod, NextChainedOnNextResult) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE, YELLOW } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = (c.next().next() == YELLOW);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, inside a class method, on a local of a package-declared enumeration
// type: name() of the next() result reports the member after the local's.
TEST(EnumNameMethod, NameOfNextCallResultInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity s;
    s = s.first();
    return (s.next().name() == "UVM_WARNING");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, inside a class method: name() of the last() result reports the last
// member while the local holds the first.
TEST(EnumNameMethod, NameOfLastCallResultInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity s;
    s = s.first();
    return (s.last().name() == "UVM_FATAL");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// R1, inside a class method, with a step count: name() of next(2) reports
// the member two past the local's value.
TEST(EnumNameMethod, NameOfNextCallResultWithStepCountInClassMethod) {
  const char* src = R"(
package p;
  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL } uvm_severity;
endpackage
import p::*;
class rep;
  function int check();
    uvm_severity sev;
    sev = UVM_WARNING;
    return (sev.next(2).name() == "UVM_FATAL");
  endfunction
endclass
module m;
  int r;
  initial begin
    rep h;
    h = new;
    r = h.check();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

}  // namespace
