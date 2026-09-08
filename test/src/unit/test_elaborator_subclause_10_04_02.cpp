#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSim, NbaAppliesToValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a <= 10;\n"
      "    b <= 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(NonblockingAssignSim, MultipleNBASameVarLastWins) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    a <= 2;\n"
      "    a <= 3;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(NonblockingAssignSim, NBAExpressionRHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 7;\n"
      "    b <= a + 3;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(NonblockingAssignSim, NBABitSelectLHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'b0000_0000;\n"
      "    a[3] <= 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(NonblockingAssignSim, NBAPartSelectLHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[3:0] <= 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(NonblockingAssignSim, NBAConcatenationRHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] hi;\n"
      "  logic [3:0] lo;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'h5;\n"
      "    result <= {hi, lo};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(NonblockingAssignSim, NBATernaryRHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result <= sel ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NonblockingAssignSim, NBAInAlwaysFF) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [31:0] q;\n"
      "  logic [31:0] d;\n"
      "  initial begin\n"
      "    d = 77;\n"
      "    clk = 0;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(NonblockingAssignSim, NBAWithIfElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    cond = 0;\n"
      "    if (cond)\n"
      "      a <= 100;\n"
      "    else\n"
      "      a <= 200;\n"
      "    cond = 1;\n"
      "    if (cond)\n"
      "      b <= 300;\n"
      "    else\n"
      "      b <= 400;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 200u);

  EXPECT_EQ(b->value.ToUint64(), 300u);
}

TEST(NonblockingAssignSim, NBAWithCase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 2;\n"
      "    case (sel)\n"
      "      0: result <= 10;\n"
      "      1: result <= 20;\n"
      "      2: result <= 30;\n"
      "      default: result <= 40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(NonblockingAssignSim, NBAInForLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    for (int i = 0; i < 5; i = i + 1) begin\n"
      "      acc <= acc + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSim, NBAFunctionCallRHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int double_val(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result <= double_val(21);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NonblockingAssignSim, NBABitwiseOperators) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] r_and;\n"
      "  logic [7:0] r_or;\n"
      "  logic [7:0] r_xor;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "    r_and <= a & b;\n"
      "    r_or  <= a | b;\n"
      "    r_xor <= a ^ b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r_and", 0x30u}, {"r_or", 0xFCu}, {"r_xor", 0xCCu}});
}

TEST(NonblockingAssignSim, NBAShiftOperators) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  logic [7:0] r_shl;\n"
      "  logic [7:0] r_shr;\n"
      "  initial begin\n"
      "    val = 8'h0F;\n"
      "    r_shl <= val << 2;\n"
      "    r_shr <= val >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_shl = f.ctx.FindVariable("r_shl");
  auto* r_shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(r_shl, nullptr);
  ASSERT_NE(r_shr, nullptr);

  EXPECT_EQ(r_shl->value.ToUint64(), 0x3Cu);

  EXPECT_EQ(r_shr->value.ToUint64(), 0x07u);
}

TEST(NonblockingAssignSim, NBAComparisonResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic r_eq;\n"
      "  logic r_lt;\n"
      "  logic r_gt;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq <= (a == b);\n"
      "    r_lt <= (a < b);\n"
      "    r_gt <= (a > b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);
}

TEST(NonblockingAssignSim, MultipleNBAsInSequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic [31:0] c;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= a;\n"
      "    a = 2;\n"
      "    c <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);

  EXPECT_EQ(b->value.ToUint64(), 1u);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(NonblockingAssignSim, NBARegisterFilePattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] regfile [0:3];\n"
      "  initial begin\n"
      "    regfile[0] <= 100;\n"
      "    regfile[1] <= 200;\n"
      "    regfile[2] <= 300;\n"
      "    regfile[3] <= 400;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r0 = f.ctx.FindVariable("regfile[0]");
  auto* r1 = f.ctx.FindVariable("regfile[1]");
  auto* r2 = f.ctx.FindVariable("regfile[2]");
  auto* r3 = f.ctx.FindVariable("regfile[3]");
  ASSERT_NE(r0, nullptr);
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  ASSERT_NE(r3, nullptr);
  EXPECT_EQ(r0->value.ToUint64(), 100u);
  EXPECT_EQ(r1->value.ToUint64(), 200u);
  EXPECT_EQ(r2->value.ToUint64(), 300u);
  EXPECT_EQ(r3->value.ToUint64(), 400u);
}

TEST(NonblockingAssignSim, DifferentWidths) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] nibble;\n"
      "  logic [15:0] half;\n"
      "  logic [31:0] word;\n"
      "  initial begin\n"
      "    nibble <= 4'hA;\n"
      "    half   <= 16'hBEEF;\n"
      "    word   <= 32'hDEADCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* nibble = f.ctx.FindVariable("nibble");
  auto* half = f.ctx.FindVariable("half");
  auto* word = f.ctx.FindVariable("word");
  ASSERT_NE(nibble, nullptr);
  ASSERT_NE(half, nullptr);
  ASSERT_NE(word, nullptr);
  EXPECT_EQ(nibble->value.width, 4u);
  EXPECT_EQ(nibble->value.ToUint64(), 0xAu);
  EXPECT_EQ(half->value.width, 16u);
  EXPECT_EQ(half->value.ToUint64(), 0xBEEFu);
  EXPECT_EQ(word->value.width, 32u);
  EXPECT_EQ(word->value.ToUint64(), 0xDEADCAFEu);
}

TEST(NonblockingAssignSim, NBABitwiseNot) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    result <= ~a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(NonblockingAssignSim, NBAReplicationRHS) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result <= {4{2'b10}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// §10.4.2 states "It shall be illegal to make nonblocking assignments to
// automatic variables or to elements of dynamically sized array variables". For
// a variable of an automatic task the rejection is reported under §13.3.2,
// which states the same prohibition with the reason it exists: such variables
// are deallocated at the end of the task invocation, so "They shall not be
// assigned values using nonblocking assignments or procedural continuous
// assignments."
TEST(NonblockingAssignSim, AutomaticVariableNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task automatic set_val();\n"
      "    int x;\n"
      "    x <= 42;\n"
      "  endtask\n"
      "  initial set_val();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            4, "13.3.2"));
}

// §10.4.2 bars a nonblocking assignment to an element of a dynamically sized
// array variable, and a queue is one. §6.21 states the same prohibition and
// states it for continuous and procedural continuous assignments as well:
// "Automatic variables and elements of dynamically sized array variables shall
// not be written with nonblocking, continuous, or procedural continuous
// assignments." The check enforces both halves of that sentence, so the report
// names §6.21.
TEST(NonblockingAssignSim, QueueElementNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q.push_back(0);\n"
      "    q[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "nonblocking assignment to element of dynamically sized "
                    "array",
                    5, "6.21"));
}

// An associative array is dynamically sized as well, so the same §6.21
// prohibition rejects a nonblocking assignment to one of its elements.
TEST(NonblockingAssignSim, AssociativeArrayElementNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  initial begin\n"
      "    aa[5] = 0;\n"
      "    aa[5] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "nonblocking assignment to element of dynamically sized "
                    "array",
                    5, "6.21"));
}

// The dynamic array is the case §6.21 and §10.4.2 both name outright.
TEST(NonblockingAssignSim, DynamicArrayElementNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    dyn = new[4];\n"
      "    dyn[0] <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "nonblocking assignment to element of dynamically sized "
                    "array",
                    5, "6.21"));
}

// The member-qualified spelling of the same target. `b[2].x` is a name for bits
// inside the element `b[2]`, so a write to it is a write to an element of a
// dynamically sized array variable and §10.4.2's "It shall be illegal to make
// nonblocking assignments to ... elements of dynamically sized array variables"
// reaches it exactly as it reaches AssociativeArrayElementNbaIsError above. The
// standard states the wider form itself in §6.21's closing sentence, which
// limits references to "elements or members of dynamic variables", so a member
// path is not a way out of the restriction the element is under.
//
// §7.8.7 is why an associative array is the one to write it on: a member write
// to an element that does not exist allocates the element, which is the storage
// motion the prohibition exists for, and it would have to happen between the
// schedule and the update.
//
// The subclause and the line are named in full and the message by its opening
// words alone. What this case claims is that line 4 is rejected under §6.21,
// as the element spelling of AssociativeArrayElementNbaIsError is; the rest of
// that sentence is the report's own account of which target it found, and the
// three cases above already hold it to every word of it.
TEST(NonblockingAssignSim, AssocElementMemberNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  initial b[2].x <= 5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "nonblocking assignment to",
                            4, "6.21"));
}

// A queue element's member, written from the clocked block a nonblocking
// assignment normally lives in. The queue is the kind §10.4.2's prohibition is
// least intuitive for -- `pq[0]` looks like an ordinary index -- but a queue
// grows and shrinks at either end, so the element a scheduled write named may
// not be the element that index reaches when the update region runs.
TEST(NonblockingAssignSim, QueueElementMemberNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { byte lo; byte hi; } pair_t;\n"
      "  pair_t pq[$];\n"
      "  logic clk;\n"
      "  always @(posedge clk) pq[0].hi <= 8'd9;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "nonblocking assignment to",
                            5, "6.21"));
}

// The dynamic array under the same spelling, with the array sized before the
// statement so the element the member path names exists. Its existence is not
// what the rule turns on: `new[]` may be called again in the same time step and
// move the storage, which is the whole of why the element is barred whether or
// not it is there when the assignment is scheduled.
TEST(NonblockingAssignSim, DynamicArrayElementMemberNbaIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int hits = 0; int miss = 0; } tally_t;\n"
      "  tally_t stats[];\n"
      "  initial begin\n"
      "    stats = new[3];\n"
      "    stats[1].hits <= 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "nonblocking assignment to",
                            6, "6.21"));
}

// What the three cases above must not cost. §7.2.1 packs a structure's members
// into the bits of one variable of fixed size, so `w.tag` is a window on `w`
// and nothing about it is dynamically sized; §10.4.2 asks of a nonblocking
// target only that it be "a data type that is valid for a procedural assignment
// statement", which this is. The elaborator therefore has nothing to report.
//
// A check that read the dot rather than what stands to the left of it would
// reject this, and it would still pass every rejection case above. That is what
// this case is here to say, so it asserts both that the run recorded no error
// at all and that no report of the §6.21 kind was among what it recorded.
TEST(NonblockingAssignSim, PackedStructMemberNbaElaboratesClean) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] tag; logic [7:0] data; } word_t;\n"
      "  word_t w;\n"
      "  initial w.tag <= 8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "a packed struct member is a legal target";
  EXPECT_EQ(FindDiag(f, "nonblocking assignment to"), nullptr);
}

// The other legal member target, and the one furthest from an array element: a
// class property lives in the object a handle designates, allocated by `new`
// and reached through no index at all. §10.4.2 names the shape outright where
// it settles when the handle is read -- "a class handle in the left-hand side
// shall be evaluated at the same time as the expression on the right-hand
// side" -- which it would have no reason to say of a target it forbade.
TEST(NonblockingAssignSim, ClassPropertyNbaElaboratesClean) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Slot;\n"
      "  logic [7:0] val;\n"
      "endclass\n"
      "module t;\n"
      "  Slot r;\n"
      "  initial begin\n"
      "    r = new;\n"
      "    r.val <= 8'h5A;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FindDiag(f, "nonblocking assignment to"), nullptr);
  EXPECT_FALSE(f.has_errors) << "a class property is a legal target";
}

}  // namespace
