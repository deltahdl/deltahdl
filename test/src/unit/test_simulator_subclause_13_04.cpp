#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionSim, FunctionWithLocalVars) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] compute(input logic [31:0] a,\n"
      "                                input logic [31:0] b);\n"
      "    logic [31:0] tmp;\n"
      "    tmp = a + b;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute(32'd10, 32'd20);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 30u);
}

TEST(FunctionSim, FunctionCallsFunction) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] add(input logic [31:0] a,\n"
      "                            input logic [31:0] b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  function logic [31:0] add3(input logic [31:0] a,\n"
      "                             input logic [31:0] b,\n"
      "                             input logic [31:0] c);\n"
      "    return add(add(a, b), c);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add3(32'd1, 32'd2, 32'd3);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

TEST(FunctionSim, FunctionEmptyBody) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 32'd5;\n"
      "    nop();\n"
      "    x = x + 32'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

// §13.4 p.341 argument-direction table: an inout formal copies the actual's
// value in at the start of the call and copies the formal's value back out at
// the end. Reading the incoming value (41) and writing an updated value back
// exercises both halves — a missing copy-in would start from the default and a
// missing copy-out would leave x at 41, so x==42 discriminates both. Input
// (copy-in) and output (copy-out) are already observed by FunctionWithLocalVars
// and FunctionMultipleStatements; this closes the remaining inout input form.
TEST(FunctionSim, FunctionInoutArgCopiesInAndOut) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void bump(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd41;\n"
      "    bump(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(FunctionSim, FunctionMultipleStatements) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void multi(output logic [31:0] v);\n"
      "    v = 32'd1;\n"
      "    v = v + 32'd2;\n"
      "    v = v + 32'd3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    multi(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

// §6.18: a variable declared with a user-defined type name is an object of the
// type that name stands for, so the `nib v` of a function body is four bits
// wide, and §6.8 makes the declaration's initializer an assignment into it, so
// §10.7 truncates 8'hFF to 15 on the way in. A local the simulator could not
// size took a 32-bit carrier instead, and an initializer that replaced the
// vector rather than being assigned into it read 255. The typedef has to be
// narrower than that carrier for the two answers to differ, which is why it is
// not the `logic [31:0] tmp` of FunctionWithLocalVars.
//
// The value is written as the declaration's initializer rather than by a
// following `v = 8'hFF;` so that what is claimed is the declaration, which
// establishes the width, and not the assignment, which truncates to a width
// already established. test_simulator_subclause_10_07.cpp claims the
// assignment, on a target whose width no declaration of a typedef name is
// involved in.
TEST(FunctionSim, TypedefNameLocalIsSizedByTheTypeItNames) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] f();\n"
      "    nib v = 8'hFF;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 15u);
}

// The case above cannot say a local wider than the carrier keeps its width:
// clamping every local to 32 bits would truncate 8'hFF to 15 as well. Forty
// bits spans two words, and the three answers separate -- 48'hFFFF00000001 kept
// whole reads 281470681743361, clamped to 32 bits reads 1, and held in the
// forty bits `wide` declares reads 1095216660481, whose set bits above the
// first word are what say the high word survived.
TEST(FunctionSim, TypedefNameLocalWiderThanOneWordKeepsItsHighBits) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] x;\n"
      "  function logic [63:0] f();\n"
      "    wide v = 48'hFFFF00000001;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 1095216660481ull);
}

// §6.8: "A variable is an abstraction of a data storage element. A variable
// shall store a value from one assignment to the next." A declaration in a
// subroutine body declares a storage element of its own, so `logic [7:0]
// mirror = held;` reads `held` and must leave `held` holding what it was last
// assigned. CreateFuncLocalVar stored what EvalExpr answered; EvalExpr answers
// a bare identifier with the source variable's own Logic4Vec, a Logic4Vec
// copies its `words` pointer rather than the words, and ResizeToWidth hands
// back a value already at the declared width -- so the declaration left
// `mirror` and `held` one element. The eight bits on each side are
// load-bearing: a declared width other than the source's makes the resize
// build the value in a fresh store, which hides the sharing entirely.
//
// The declaration itself writes nothing in place, so it takes a later writer
// to show the sharing, and which writer it is decides what this case can be. A
// store to `mirror` will not do it: ExecFuncBlockingAssign owns its right-hand
// words, and ExecFuncIdentifierAssign puts that owned vector in the local's
// place before it coerces, so a later store leaves `held`'s buffer
// unreferenced rather than writing through it. The writer that does reach it
// is the one that coerces a vector it did not build: §13.5.1 passes an input
// argument by copying "the values of the actual arguments" into the formal,
// and §6.11.2 -- "When a 4-state value is automatically converted to a 2-state
// value, any unknown or high-impedance bits shall be converted to zeros" --
// converts that copy in place. Handing `mirror` to a `bit [7:0]` formal of its
// own width therefore cleared `held`'s unknowns from inside a call that read
// nothing but a local copy of it.
//
// That the conversion reaches the actual's own buffer is a defect of this
// same family at the binding site (#3564), and it is what makes this case
// discriminating rather than merely true: with the binding taking its own
// copy, the conversion would land on that copy whether or not the
// declaration above shared its words, and the case would go on holding with
// nothing left to expose the sharing. No writer in the tree reaches a plain
// integral local's buffer in place, so this is the exposure the claim has.
//
// ToUint64 cannot see this. It projects aval & ~bval, so a bit that is already
// unknown reads as 0 through it and clearing that bit changes nothing it
// reports; the assertions read words[0] directly. 8'b0x1110x0 is stored as
// aval 0x7A with bval 0x42, an x digit being aval 1 with bval 1, and the
// 2-state conversion of it is aval 0x38 with bval 0x00 -- which is what the
// formal, and `seen` after it, alone are entitled to hold.
TEST(FunctionSim, DeclaredLocalInitializedFromAVariableGetsItsOwnWords) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] held;\n"
      "  bit [7:0] seen;\n"
      "  function bit [7:0] note(bit [7:0] arg);\n"
      "    return arg;\n"
      "  endfunction\n"
      "  function void relay();\n"
      "    logic [7:0] mirror = held;\n"
      "    seen = note(mirror);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    held = 8'b0x1110x0;\n"
      "    relay();\n"
      "  end\n"
      "endmodule\n",
      f, "held");
  ASSERT_NE(source, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* noted = f.ctx.FindVariable("seen");
  ASSERT_NE(noted, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0x7Au);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x42u);
  EXPECT_EQ(noted->value.words[0].aval & 0xFFu, 0x38u);
  EXPECT_EQ(noted->value.words[0].bval & 0xFFu, 0x00u);
}

// The other expression the declaration site can be handed, and the reason the
// case above does not state the whole claim: §7.4.2 makes each element of an
// unpacked array an object in its own right, and a select of one is answered
// with that element variable's own Logic4Vec rather than with a value read out
// of the array. So `logic [7:0] slot = bank[1];` shares its buffer with an
// element -- a variable the source names only through an index, and one no
// later store in the subroutine mentions at all.
//
// z as well as x, because §6.11.2 converts "any unknown or high-impedance
// bits" and the two are stored apart: 8'b1zz01x10 is aval 0x8E with bval 0x64,
// a z digit being aval 0 with bval 1 where an x digit is aval 1 with bval 1,
// and the conversion of it is aval 0x8A with bval 0x00. bval is what separates
// the two states: a conversion that dropped the x bits and kept the z bits
// would answer the same aval and leave bval at 0x60.
//
// That the conversion reaches the actual's own buffer is a defect of this
// same family at the binding site (#3564), and it is what makes this case
// discriminating rather than merely true: with the binding taking its own
// copy, the conversion would land on that copy whether or not the
// declaration above shared its words, and the case would go on holding with
// nothing left to expose the sharing. No writer in the tree reaches a plain
// integral local's buffer in place, so this is the exposure the claim has.
//
// Eight bits throughout for the reason the case above gives, and the element
// is read once and never written after `lift()` returns, so the array must
// still hold what the initial block put in it.
TEST(FunctionSim, DeclaredLocalInitializedFromAnElementGetsItsOwnWords) {
  SimFixture f;
  auto* element = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] bank [0:1];\n"
      "  bit [7:0] taken;\n"
      "  function bit [7:0] echo_bits(bit [7:0] bits_in);\n"
      "    return bits_in;\n"
      "  endfunction\n"
      "  function void lift();\n"
      "    logic [7:0] slot = bank[1];\n"
      "    taken = echo_bits(slot);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    bank[1] = 8'b1zz01x10;\n"
      "    lift();\n"
      "  end\n"
      "endmodule\n",
      f, "bank[1]");
  ASSERT_NE(element, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* lifted = f.ctx.FindVariable("taken");
  ASSERT_NE(lifted, nullptr);
  EXPECT_EQ(element->value.words[0].aval & 0xFFu, 0x8Eu);
  EXPECT_EQ(element->value.words[0].bval & 0xFFu, 0x64u);
  EXPECT_EQ(lifted->value.words[0].aval & 0xFFu, 0x8Au);
  EXPECT_EQ(lifted->value.words[0].bval & 0xFFu, 0x00u);
}

}  // namespace
