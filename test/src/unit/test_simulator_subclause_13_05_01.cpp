#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PassByValueSim, DefaultMechanismWithoutDirectionQualifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function int add_ten(int v);\n"
      "    v = v + 10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    y = add_ten(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 15u}});
}

TEST(PassByValueSim, AutomaticFunctionRetainsLocalCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function automatic int modify_arg(input int v);\n"
      "    v = v + 100;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    y = modify_arg(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, TaskInputArgNotVisibleOutside) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task modify(input int v);\n"
      "    v = v + 100;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    modify(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

// C1 in the task syntactic position: a task argument written with no direction
// qualifier defaults to input and is therefore passed by value. The callee
// mutates its local copy, yet the caller's variable is unchanged (x stays 4),
// while the copied-in value reaches the callee (y == 54). Distinct from the
// function no-qualifier case and from the explicit-input task case.
TEST(PassByValueSim, TaskDefaultDirectionArgPassedByValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task apply(int v);\n"
      "    v = v + 50;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 4;\n"
      "    apply(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 4u}, {"y", 54u}});
}

TEST(PassByValueSim, MultipleArgsCopiedIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  function int swap_and_add(int x, int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 7;\n"
      "    result = swap_and_add(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}, {"result", 10u}});
}

TEST(PassByValueSim, RecursiveAutomaticUsesPerActivationStackCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  function automatic int sum_down(int n);\n"
      "    if (n == 0) return 0;\n"
      "    return n + sum_down(n - 1);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = sum_down(4);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 10u}});
}

TEST(PassByValueSim, SameSourceBoundToTwoFormalsCopiesIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  function int scale_first_minus_second(int a, int b);\n"
      "    a = a * 10;\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    result = scale_first_minus_second(x, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"result", 63u}});
}

// §13.5.1 illustrates the copy with an unpacked array formal (byte packet[]).
// Passing an array by value copies every element into the subroutine area: the
// callee reads the copied-in values (sum == 7) yet its later writes to the
// local copy leave the caller's array untouched, so the mutation is not visible
// outside the call.
TEST(PassByValueSim, UnpackedArrayArgumentCopiedElementwise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte packet [0:1];\n"
      "  int total;\n"
      "  function int sum_then_clobber(byte p [0:1]);\n"
      "    int s;\n"
      "    s = p[0] + p[1];\n"
      "    p[0] = 99;\n"
      "    p[1] = 99;\n"
      "    return s;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    packet[0] = 3;\n"
      "    packet[1] = 4;\n"
      "    total = sum_then_clobber(packet);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"packet[0]", 3u}, {"packet[1]", 4u}, {"total", 7u}});
}

// §13.5.1 copies each argument into the subroutine area, and §10.8 lists "the
// passing of a value to a subroutine input, output, or inout argument" among
// the assignment-like contexts, so §10.7 truncates or extends the actual into
// the width the formal's type declares. §6.18 makes a formal written with a
// user-defined type name an object of the type that name stands for, which is
// the width in question here.
//
// Each case passes a value the formal's type is too narrow to hold, because
// that is what the two answers disagree about: a formal the simulator could not
// size was left at whatever width the caller's expression had, so `8'hFF` read
// 255 where four bits read 15. A formal of exactly 32 bits, or a value that
// fits the type, reads the same either way.
TEST(PassByValueSim, TypedefNameInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  function int take(input nib p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(8'hFF);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

// A task's formals are bound by the same code as a function's, but a task is
// reached by its own call path and neither case stands for the other. The
// output formal here is how the value is read back and is a 32-bit `int`, so
// what it reports is the input formal's width and not its own.
TEST(PassByValueSim, TypedefNameTaskInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  task take(input nib p, output int o);\n"
      "    o = p;\n"
      "  endtask\n"
      "  initial begin\n"
      "    y = 0;\n"
      "    take(8'hFF, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

// The four-bit cases cannot say a formal wider than the 32 bits an unsized
// formal used to fall back to keeps its own width: a clamp to 32 would truncate
// 8'hFF to 15 as well. Forty bits spans two words, and the three answers
// separate -- 48'hFFFF00000001 passed whole reads 281470681743361, clamped to
// thirty-two reads 1, and truncated to the forty bits `wide` declares reads
// 1095216660481, whose set bits above the first word are what say the high word
// survived.
TEST(PassByValueSim, TypedefNameFormalWiderThanOneWordKeepsItsHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] y;\n"
      "  function logic [63:0] take(input wide p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(48'hFFFF00000001);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 1095216660481ull}});
}

// §8.3 makes a class variable a handle to an object rather than an object of a
// width, so there is nothing here for §10.7 to truncate and the formal takes
// the handle it was passed. What makes this worth a case of its own is that a
// class name can reach the elaborated typedef table and answer a width there:
// §8.27's forward declaration records the name before the class exists, with a
// data type that is still DataTypeKind::kImplicit, which §6.10 makes a scalar.
// A formal sized from that answer would hold one bit of the handle and read 0
// rather than the 42 the object carries -- and only in a design that happens to
// forward- declare the class, which is why the accompanying `typedef class
// Packet;` is the whole point of the case and not decoration.
TEST(PassByValueSim, ForwardDeclaredClassFormalKeepsTheWholeHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class Packet;\n"
      "class Packet;\n"
      "  integer i = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int y;\n"
      "  function integer read_i(Packet p);\n"
      "    read_i = p.i;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    Packet q;\n"
      "    q = new;\n"
      "    y = read_i(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 42u}});
}

// §13.5.1 passes an input argument by copying "the values of the actual
// arguments" into the formal, and §6.11.2 -- "any unknown or high-impedance
// bits shall be converted to zeros" -- converts that copy where the formal is
// declared 2-state. The conversion is entitled to the copy and to nothing
// else: a call that names `carried` and does no more than read it must leave
// every bit of `carried` standing. The binding handed it the actual's own
// storage instead -- EvalExpr answers a bare identifier with the caller's
// variable's Logic4Vec, and a Logic4Vec copies its words pointer -- so the
// in-place conversion cleared the caller's unknowns from inside a call that
// wrote nothing.
//
// The two widths must match, and 8 is written on both declarations for that
// reason: on a width difference the resize allocates and hands the conversion
// a buffer of its own, so a formal of any other width would be the path where
// nothing was ever wrong and this case would say nothing.
//
// ToUint64 cannot see this. It projects aval & ~bval, so a bit that is already
// unknown reads as 0 through it and clearing that bit changes nothing it
// reports; the assertions read words[0] directly. 8'b0z1x0110 is stored as
// aval 0x36 with bval 0x50, an x digit being aval 1 with bval 1 and a z digit
// aval 0 with bval 1, and the 2-state conversion of it is aval 0x26 with bval
// 0x00 -- which the formal, and `observed` after it, alone are entitled to
// hold. Asserting on both is what says the conversion still happens and only
// says where. bval is what separates the two unknown states: a conversion that
// cleared the x bit and kept the z would answer the same aval and leave bval
// at 0x40.
TEST(PassByValueSim, ActualBoundToASameWidthTwoStateFormalKeepsItsUnknowns) {
  SimFixture f;
  auto* carried = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] carried;\n"
      "  bit [7:0] observed;\n"
      "  function bit [7:0] keep(bit [7:0] copy_in);\n"
      "    return copy_in;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    carried = 8'b0z1x0110;\n"
      "    observed = keep(carried);\n"
      "  end\n"
      "endmodule\n",
      f, "carried");
  ASSERT_NE(carried, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* observed = f.ctx.FindVariable("observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(carried->value.words[0].aval & 0xFFu, 0x36u);
  EXPECT_EQ(carried->value.words[0].bval & 0xFFu, 0x50u);
  EXPECT_EQ(observed->value.words[0].aval & 0xFFu, 0x26u);
  EXPECT_EQ(observed->value.words[0].bval & 0xFFu, 0x00u);
}

// The second expression the binding can be handed with no copy of its own, and
// the reason the case above does not state the whole claim: §7.4.2 makes each
// element of an unpacked array an object in its own right, and a select of one
// is answered with that element variable's own Logic4Vec rather than with a
// value read out of the array. The actual here is written only as an index, so
// it reaches the binding by a different production from the bare identifier
// above while arriving with the same storage shared -- and a whole-array
// actual would not reach this path at all, being bound elementwise before the
// by-value bind is consulted.
//
// Eight bits on both declarations again, so that no resize stands between the
// element and the conversion: a formal of a different width would be handed a
// freshly allocated buffer and the element could not be touched.
//
// z as well as x, because §6.11.2 converts "any unknown or high-impedance
// bits" and the two are stored apart. 8'b11x0z101 is aval 0xE5 with bval 0x28,
// and the conversion of it is aval 0xC5 with bval 0x00 -- what `copied` alone
// is entitled to hold, while `lanes[1]`, read once and never written after the
// call, must still hold what the initial block put there. A conversion that
// dropped the x bit and kept the z would answer the same aval and leave bval
// at 0x08, which is why bval is asserted on both.
TEST(PassByValueSim, ArrayElementActualKeepsItsUnknownsAcrossTheBinding) {
  SimFixture f;
  auto* lane = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] lanes [0:1];\n"
      "  bit [7:0] copied;\n"
      "  function bit [7:0] relay(bit [7:0] one_lane);\n"
      "    return one_lane;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    lanes[1] = 8'b11x0z101;\n"
      "    copied = relay(lanes[1]);\n"
      "  end\n"
      "endmodule\n",
      f, "lanes[1]");
  ASSERT_NE(lane, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* copied = f.ctx.FindVariable("copied");
  ASSERT_NE(copied, nullptr);
  EXPECT_EQ(lane->value.words[0].aval & 0xFFu, 0xE5u);
  EXPECT_EQ(lane->value.words[0].bval & 0xFFu, 0x28u);
  EXPECT_EQ(copied->value.words[0].aval & 0xFFu, 0xC5u);
  EXPECT_EQ(copied->value.words[0].bval & 0xFFu, 0x00u);
}

// The boundary the two cases above are written to avoid, stated on purpose:
// when the formal's declared width differs from the actual's, §10.7 truncates
// the value into that width -- an assignment-like context by §10.8 -- and the
// truncation produces a vector of its own, so the §6.11.2 conversion has never
// had the caller's storage to write through. This case therefore reads the
// same before and after the binding is made to copy, and it is not an exposure
// of that: it pins that the path which was already correct still truncates and
// still converts, and that the eight-bit actual keeps the four unknown-bearing
// bits above the formal's width.
//
// The actual is a 4-state variable carrying unknowns on both sides of the
// four-bit boundary, which is what no other case in this file offers the
// resize: the typedef cases pass 2-state literals and read their answer
// through ToUint64, which cannot report an unknown at all. 8'b1x01z100 is aval
// 0xD4 with bval 0x48, and the caller's variable must still read that after
// the call. The low nibble alone is aval 0x4 with bval 0x8, whose conversion
// is aval 0x4 with bval 0x00.
//
// The formal is read back through a 32-bit `int` and not a four-bit variable,
// because a four-bit destination would truncate a formal that had wrongly kept
// all eight bits down to the same nibble and report 0x4 either way. Through an
// `int` the two answers separate: 0x4 says the formal was sized by its own
// declaration, and 0x94 -- the whole eight bits converted -- says it was left
// at the actual's width.
TEST(PassByValueSim, NarrowerFormalTruncatesWithoutTouchingTheActual) {
  SimFixture f;
  auto* source_bits = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] source_bits;\n"
      "  int read_back;\n"
      "  function int shrink(bit [3:0] narrow_in);\n"
      "    return narrow_in;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    source_bits = 8'b1x01z100;\n"
      "    read_back = shrink(source_bits);\n"
      "  end\n"
      "endmodule\n",
      f, "source_bits");
  ASSERT_NE(source_bits, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* read_back = f.ctx.FindVariable("read_back");
  ASSERT_NE(read_back, nullptr);
  EXPECT_EQ(source_bits->value.words[0].aval & 0xFFu, 0xD4u);
  EXPECT_EQ(source_bits->value.words[0].bval & 0xFFu, 0x48u);
  EXPECT_EQ(read_back->value.words[0].aval & 0xFFu, 0x4u);
  EXPECT_EQ(read_back->value.words[0].bval & 0xFFu, 0x0u);
}

// §13.5.1: "This argument passing mechanism works by copying each argument into
// the subroutine area ... If the arguments are changed within the subroutine,
// the changes are not visible outside the subroutine." The four aggregate binds
// copied the container and every entry's Logic4Vec, which carries the words
// pointer rather than the words, so the formal's entries were the actual's.
// §7.8.7's write to bits of an element is the writer that shows it:
// DepositBitField writes through the words it finds, so the callee's write
// landed in the caller's array as well.
TEST(PassByValueSim, AssocFormalElementBitsAreNotTheActualsWords) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[int]);\n"
      "    a[5][3:0] = 4'hF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[5] = 8'h00;\n"
      "    poke(aa);\n"
      "    r = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x00u);
}

// The queue bind, whose elements live in a QueueObject rather than in
// variables. A whole-element write replaces the entry's vector rather than
// writing through it, so this passed before the copy and is the guard on it:
// the fix must not have made the formal share the actual's container.
TEST(PassByValueSim, QueueFormalElementWriteIsNotVisibleOutside) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] qu[$];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[$]);\n"
      "    a[0] = 8'hFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    qu.push_back(8'h11);\n"
      "    poke(qu);\n"
      "    r = qu[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x11u);
}

// The fixed-size array bind, whose elements are per-element variables of the
// caller, and the same guard over it.
TEST(PassByValueSim, FixedArrayFormalElementWriteIsNotVisibleOutside) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr[0:1];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[0:1]);\n"
      "    a[1] = 8'hFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    arr[1] = 8'h11;\n"
      "    poke(arr);\n"
      "    r = arr[1];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x11u);
}

// §13.5.1's copy has to answer to the formal's name inside the call, and a
// queue's elements live in a QueueObject registered by name rather than in
// variables. Registered for the whole run and looked up without asking the
// scope stack, a formal named after a module's queue was the module's queue to
// every writer in the callee. The two names have to match for the two answers
// to differ, which is the case none of the existing argument cases writes.
TEST(PassByValueSim, QueueFormalNamedLikeTheModulesIsItsOwnCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int r;\n"
      "  task automatic fill(input int q[$]);\n"
      "    q[0] = 99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(7);\n"
      "    fill(q);\n"
      "    r = q[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 7u);
}

// The associative array is a separate object, a separate map and a separate
// lookup, so it needs its own case.
TEST(PassByValueSim, AssocFormalNamedLikeTheModulesIsItsOwnCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int r;\n"
      "  task automatic fill(input int aa[int]);\n"
      "    aa[5] = 99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[5] = 7;\n"
      "    fill(aa);\n"
      "    r = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 7u);
}

// The other half of the same registration: §23.9 gives the copy the lifetime of
// the scope that declared it, so once the call has returned the name reads the
// module's queue again rather than the formal's copy.
TEST(PassByValueSim, QueueFormalCopyDoesNotOutliveTheCall) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int r;\n"
      "  task automatic fill(input int q[$]);\n"
      "    q.push_back(99);\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(7);\n"
      "    fill(q);\n"
      "    r = q.size();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

// §6.11.1 makes byte, shortint, int, integer and longint signed by default, and
// §6.18 makes a formal declared with a name for one an object of that type, so
// §10.7 sign-extends it into a wider target. The formal's cell was created by
// asking IsSignedType with an empty typedef map, which resolves a name through
// nothing and answers unsigned, so -1 came back as the magnitude 255. The value
// has to be negative and the target wider for the two answers to differ.
TEST(PassByValueSim, TypedefSignedFormalSignExtendsIntoAWiderTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int widen(input b_t p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

// §6.11.1's default signedness and an explicit `signed` keyword reach
// IsSignedType by different arms, so the typedef of an explicitly signed vector
// is its own case.
TEST(PassByValueSim, TypedefExplicitlySignedFormalSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef logic signed [7:0] s8_t;\n"
      "  int r;\n"
      "  function int widen(input s8_t p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

// The sign read through an operator rather than through an assignment: §11.4.4
// compares a signed operand as a signed value, which an unsigned cell makes
// false for every value it can hold.
TEST(PassByValueSim, TypedefSignedFormalComparesAsSigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int is_negative(input b_t p);\n"
      "    return (p < 0) ? 1 : 0;\n"
      "  endfunction\n"
      "  initial r = is_negative(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

// A body local declared with the same name, which CreateFuncLocalVar creates by
// its own path and asked the same empty map.
TEST(PassByValueSim, TypedefSignedBodyLocalSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int widen();\n"
      "    b_t p = -1;\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

}  // namespace
