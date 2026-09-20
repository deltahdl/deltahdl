#include <gtest/gtest.h>

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

// §13.4: a function body holds the statements a procedure does but the
// timing controls, a case statement among them: a module function selects
// its item by the case expression, a class method by a property, each
// assigning the function's name, and a default item answers the rest.
TEST(FunctionSim, CaseStatementInFunctionAndMethodBodies) {
  auto val = RunAndGet(
      "class C;\n"
      "  int kind = 2;\n"
      "  function int tens();\n"
      "    case (kind)\n"
      "      1: tens = 10;\n"
      "      2: tens = 20;\n"
      "      default: tens = 90;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  function int units(int k);\n"
      "    case (k)\n"
      "      1: units = 1;\n"
      "      2: units = 2;\n"
      "      default: units = 9;\n"
      "    endcase\n"
      "  endfunction\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    r = o.tens() + units(1) + 100 * units(7);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 921u);
}

// §13.4 with §27.4 and §23.6: a function declared in a loop generate block
// is a member of the block instance's scope, and §23.6 names that instance
// through the block with an instance select, `blk[1].triple`, from outside
// the block; from inside the block its bare name reaches it. The block's own
// initial packs its 30 in the units and the module's initial, a time step
// later, the hierarchical call's 30 in the hundreds, 3030; a hierarchical
// call that reaches no function answers 0 and leaves 30.
TEST(FunctionSim, GenerateBlockFunctionCalledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int triple(int x); return x * 3; endfunction\n"
      "      initial if (g == 1) r = triple(10);\n"
      "    end\n"
      "  endgenerate\n"
      "  initial #1 r = r + 100 * blk[1].triple(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3030u);
}

// §27.4: each instance of the block is a separate scope with its own implicit
// localparam, so the function of instance 0 and the function of instance 1
// are two functions reading two values of `g`, and the instance select
// picks which. `scaled` answers x * (g + 2): 20 from blk[0] and 30 from
// blk[1], packed as 3020; a call that ran every instance's function as one
// reads the same for both, and one that lost the localparam reads 20 or 0
// for both.
TEST(FunctionSim, GenerateBlockFunctionReadsItsOwnInstanceLoopIndex) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial r = blk[0].scaled(10) + 100 * blk[1].scaled(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3020u);
}

// §27.4 with §23.9: the function's body reads the block instance's own
// declaration by its simple name, the block being the scope the function was
// declared in, whichever process calls it. Each instance's initial sets its
// `base` to 100 * g at time zero, and the module's initial reads
// blk[1].addbase(5) a step later: 105, where a body resolving `base` in the
// caller's scope finds no such variable and answers 5, and one resolving it
// in instance 0 answers 5 as well.
TEST(FunctionSim, GenerateBlockFunctionReadsTheBlockInstancesOwnVariable) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      int base;\n"
      "      initial base = 100 * g;\n"
      "      function int addbase(int x); return x + base; endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial #1 r = blk[1].addbase(5);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 105u);
}

// §13.5 with §27.4: the actuals are the caller's expressions, so an actual
// written in one block instance and passed to another instance's function
// reads the caller's own `base`, while the body reads the callee's. Instance
// 0 calls blk[1].addbase(base) at #1 with its own base of 7 and the callee
// adds its 100: 107; an actual read in the callee's scope passes 100 and
// answers 200.
TEST(FunctionSim, GenerateBlockFunctionActualReadsTheCallersBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      int base;\n"
      "      initial base = g == 0 ? 7 : 100;\n"
      "      function int addbase(int x); return x + base; endfunction\n"
      "      initial if (g == 0) #1 r = blk[1].addbase(base);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 107u);
}

// §27.5 with §23.6: a conditional generate block's instance is named by the
// block's name alone, `g1.quad`, there being no index to select by, and a
// function it declares is reached so: 40.
TEST(FunctionSim, ConditionalGenerateBlockFunctionCalledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  generate\n"
      "    if (1) begin : g1\n"
      "      function int quad(int x); return x * 4; endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "  initial r = g1.quad(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 40u);
}

// §13.3 with §27.4: a task declared in the block is enabled the same way,
// `blk[1].tk(2)`, and may suspend there; it adds its instance's `g` and 10
// to the module's `r` after the delay: 11, where the task of instance 0 or
// one with no `g` adds 10.
TEST(FunctionSim, GenerateBlockTaskEnabledByHierarchicalName) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      task tk(int d); #d r = r + g + 10; endtask\n"
      "    end\n"
      "  endgenerate\n"
      "  initial blk[1].tk(2);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 11u);
}

// §23.6: the path may go on through a module instance, `u1.blk[1].scaled`,
// the block being the instance's; the body reads the loop index of the
// instance's block: 30.
TEST(FunctionSim, GenerateBlockFunctionOfAChildInstance) {
  auto val = RunAndGet(
      "module sub;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n"
      "module t;\n"
      "  int r;\n"
      "  sub u1();\n"
      "  initial r = u1.blk[1].scaled(10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 30u);
}

// §23.6: the complete path starts at a top-level module and may be used from
// a parallel hierarchy, so n's `m.blk[1].scaled(10)` is m's block's
// function: 30.
TEST(FunctionSim, GenerateBlockFunctionOfAParallelTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module m;\n"
      "  genvar g;\n"
      "  generate\n"
      "    for (g = 0; g < 2; g++) begin : blk\n"
      "      function int scaled(int x); return x * (g + 2); endfunction\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n"
      "module n;\n"
      "  int r;\n"
      "  initial r = m.blk[1].scaled(10);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 30u}});
}

}  // namespace
