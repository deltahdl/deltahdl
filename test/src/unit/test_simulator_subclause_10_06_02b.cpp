// §10.6.2's override read against the writers that carry an assignment to a
// forced variable, continuing test_simulator_subclause_10_06_02a.cpp.
//
// The rule itself and the net side of it -- what a force on a net overrides,
// what a release hands back, and the strength the net reports while each holds
// -- are in test_simulator_subclause_10_06_02a.cpp. What varies here is the
// form the assignment takes rather than the rule: a compound operator, an
// increment, an assignment written as an expression rather than as a statement,
// a bit-select and a part-select target, the nonblocking forms of those
// selects, an element of a concatenation left-hand side, and each of the ones
// the subroutine-body executor has its own execution of, written in a task or
// a function body. The release companions among them are what say the decline
// is bounded by the release rather than standing for the rest of the run.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §10.4 lists "Nonblocking procedural assignment statements
// (see 10.4.2)" as one of the three kinds of procedural assignment statement,
// and lists "Bit-selects, part-selects, and slices of packed arrays" among the
// forms "The left-hand side of a procedural assignment can take", so indexing
// the target of a `<=` leaves it inside the class a force overrides. The
// clause's own "It shall not be a bit-select or a part-select of a variable"
// restricts what may be forced, not what a force overrides.
//
// This is ForcePreventsNonblockingAssign, in the sibling file, with the target
// indexed, and it is the case that claims SetupBitSelectNbaCallback.
// ScheduleNonblockingAssign asks TryResolveArrayElement for an element variable
// named `x[3]` first, and CreateArrayElements makes those only for an unpacked
// declaration, so a packed `logic [7:0] x` has none and the select branch
// installs the deferred write.
// SetupWholeVarNbaCallback beside it has always tested is_forced inside its own
// lambda; this callback tested it nowhere, so the update region deposited the
// bit after the force. The forced 50 is 8'b0011_0010, so setting bit 3 read 58.
// The `#1;` is what ForcePreventsNonblockingAssign uses to give the deferred
// write its region before the run ends.
TEST(ForceReleaseSim, ForcePreventsANonblockingBitSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] <= 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The same rule stated against a nonblocking part-select, which is a second
// callback rather than a second route into the first one:
// SetupSelectNbaCallback picks between SetupBitSelectNbaCallback and
// SetupPartSelectNbaCallback on whether the select carries an index_end, so the
// bit-select case above never enters this one. TryResolveArrayElement declines
// any lhs carrying an index_end outright, which puts even an unpacked array
// here, and SetupPartSelectNbaCallback had no simulator case of any kind before
// this one -- a decline written into only the bit-select callback would leave
// this form overriding the force.
//
// The forced 50 is 8'b0011_0010, whose low nibble is 4'h2, so the deferred
// write of 4'hF over x[3:0] read 63 where §10.6.2 has it not land at all.
TEST(ForceReleaseSim, ForcePreventsANonblockingPartSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3:0] <= 4'hF;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §11.4.1 states a compound assignment as one of those
// assignments -- "an assignment operator is semantically equivalent to a
// blocking assignment" -- and §10.4 puts a blocking assignment written in an
// initial block among the procedural assignments, so `x += 8'd10;` is the same
// statement ForcePreventsBlockingAssign writes in the sibling file, and the
// force declines it the same way.
//
// A compound operator is the one form that reaches WriteVar, and WriteVar was
// the only writer on the blocking-assignment path that consulted the flag
// nowhere, so this read 60 -- the forced 50 with the 10 added to it -- where
// the plain `x = 8'd100;` of that file already read 50. No other case in this
// file reaches that writer.
TEST(ForceReleaseSim, ForcePreventsACompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// §11.4.2 states the increment and decrement operators as blocking assignments
// -- "These increment and decrement assignment operators behave as blocking
// assignments" -- so §10.6.2 overrides `x++` exactly as it overrides the
// `x = 8'd100;` of ForcePreventsBlockingAssign and the `x += 8'd10;` of
// ForcePreventsACompoundAssign above. A bare `x++;` is an expression statement
// naming no subroutine, so ExecInlineTaskCall declines it and hands it to
// EvalExpr; the increment therefore happens in the expression evaluator rather
// than on any statement-assignment path.
//
// That is why this case failed while the two above passed. EvalIncDec stores
// into var->value itself instead of calling WriteVar, so the guard #3506 put
// in WriteVar sat on a path this one never takes: the increment read the
// forced 50, added 1 and stored 51.
//
// Only the write is declined -- the operator still yields the value it
// computed -- but a postfix `++` yields what the target held beforehand, which
// is the forced 50 whether or not the write lands. Nothing here can read that
// half of the rule; the case below is what does.
TEST(ForceReleaseSim, ForcePreventsAnIncrement) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x++;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The increment written where its value is read. EvalIncDec is one function
// for all four spellings, so a decrement and a postfix form cannot fail while
// ForcePreventsAnIncrement passes; what they cannot say is whether the decline
// stopped at the write. §11.4.2 states the operator as a blocking assignment,
// which §10.6.2 overrides, and states nothing about the value it yields, so a
// prefix increment still reads 51 while the target it declined to write stays
// at the forced 50. A decline written as an early return from EvalIncDec would
// hand back the operand unchanged and leave y at 50.
TEST(ForceReleaseSim, ForcePreventsAnIncrementWithoutChangingWhatItYields) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (++x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 51u);
}

// The compound operator written as an expression rather than as a statement.
// §11.4.1 makes the two spellings one assignment, so §10.6.2 declines both;
// but the expression form reaches neither WriteVar nor the read-modify-write
// the statement form performs. EvalCompoundAssign stores into var->value
// itself, so x read 60 here -- the forced 50 with the 10 added to it -- after
// ForcePreventsACompoundAssign above had already been made to read 50.
//
// y is what says the decline is confined to the write. §11.3.6 has an
// assignment expression "evaluates the right-hand side, casts the right-hand
// side to the left-hand data type, stacks it, updates the left-hand side, and
// returns the stacked value": the value is stacked before the update, so what
// comes back is the value the operator computed and not a re-read of the
// target. The addition produces 60 whichever way the update goes, so y takes
// 60 while x stays at 50. A decline written as an early return from
// EvalCompoundAssign, or as returning what the forced target still holds,
// would leave y at 50 and satisfy the assertions on x alone.
//
// LvalueSim.CompoundAssignExpressionYieldsTheTargetsDataType in
// test_simulator_subclause_11_04_01.cpp reads the rest of the same sentence,
// that "the data type of the value that is returned is the data type of the
// left-hand side" -- which is what sizes this 60 at x's eight bits rather than
// at the literal's.
TEST(ForceReleaseSim, ForcePreventsACompoundAssignWrittenAsAnExpression) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (x += 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 60u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §10.4 puts a blocking assignment written in an initial
// block among those procedural assignments, and naming a bit-select as the
// target does not take the statement out of that class -- the clause's own "It
// shall not be a bit-select or a part-select of a variable" restricts what may
// be forced, not what a force overrides.
//
// This is ForcePreventsBlockingAssign with the target indexed, and it is the
// case that claims WriteBitSelect. Every whole-variable writer declines --
// WriteVar, AssignToScalarLhs, PerformBlockingAssign -- but a select target
// reaches none of them. TryResolveArrayElement asks for an element variable
// named `x[3]`, and CreateArrayElements makes those only for an unpacked
// declaration, so a packed `logic [7:0] x` has none; ResolveLhsVariable then
// walks the select down to its base and TrySelectBlockingAssign hands the whole
// variable to WriteBitSelect, which consulted the flag nowhere. The forced 50
// is 8'b0011_0010, so depositing a 1 in bit 3 read 58.
TEST(ForceReleaseSim, ForcePreventsABitSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The same rule stated against a part-select. WriteBitSelect holds two deposits
// and the presence of an index_end is what picks between them: a bit-select
// clears and sets the one bit in place and returns, while a part-select
// resolves the window the select names and hands it to WritePartSelect, which
// the bit-select case above never enters. A decline written into the
// bit-select arm rather than at the top of the writer would leave this form
// overriding the force.
//
// The forced 50 is 8'b0011_0010, whose low nibble is 4'h2, so writing 4'hF over
// x[3:0] read 63 where §10.6.2 has the write not land at all.
TEST(ForceReleaseSim, ForcePreventsAPartSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3:0] = 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The select form of §11.4.1's compound operator, which is a second route into
// the same writer rather than a second writer. ApplyCompoundAssignOp's select
// arm asks TryResolveArrayElement for an element variable first and, a packed
// vector having none, falls through to the branch that reads the target,
// computes, and writes the result back through TrySelectBlockingAssign. It
// never reaches AssignToScalarLhs, which is the arm that would have declined on
// its own, so this is the route that would silently escape a decline applied at
// only one of WriteBitSelect's call sites.
//
// Traced for `logic [7:0] x`: x[3] of the forced 8'b0011_0010 reads 0, the
// addition makes 1, and WriteBitSelect deposited that in bit 3 for 58 -- the
// same answer the plain bit-select assignment above gave, arrived at by a
// different path, which is what makes the route and not the value the thing
// this case claims.
TEST(ForceReleaseSim, ForcePreventsABitSelectCompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] += 1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §11.4.12 makes a concatenation a left-hand side -- "The
// concatenation is treated as a packed vector of bits. It can be used on the
// left-hand side of an assignment or in an expression" -- and §10.4.1 lists
// `{carry, acc} = rega + regb;   // a concatenation` among its examples of a
// blocking procedural assignment, which §10.4 puts among the assignments
// occurring "within procedures such as always, initial, task, and function".
// An element of a concatenation left-hand side therefore receives a procedural
// assignment, and a force on that element overrides it.
//
// UnpackConcatLhs is the writer every concatenation target reaches, and its
// whole-variable element deposit consulted the flag nowhere, so a took the high
// slice of 16'h1234 and read 18. The route reaches none of the writers that do
// decline: PerformBlockingAssign hands a concatenation to UnpackConcatLhs and
// returns before its own is_forced test, which is the shape the select arm
// beside it already had.
//
// b is what says only the forced element was declined. The concatenation is a
// packed vector of sixteen bits over two eight-bit variables, so a takes 8'h12
// and b takes 8'h34; §10.6.2 stops the first at the forced 50 and says nothing
// about the second, which takes 52. Asserting on a alone would be satisfied by
// a decline that dropped the whole statement.
TEST(ForceReleaseSim, ForcePreventsAConcatenationElementAssign) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    force a = 8'd50;\n"
      "    {a, b} = 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so the assignment a force overrides is the same
// statement wherever it is written.
//
// A task called with parentheses runs its body on the ordinary statement
// executor: SetupTaskCall claims a kTaskDecl and ExecInlineTaskCall walks the
// body through ExecStmt, reaching the same AssignToScalarLhs that
// ForcePreventsBlockingAssign exercises in the sibling file. So this case reads
// the rule through a task call rather than through the subroutine-body
// executor, and the function case below is what claims that executor -- a void
// function called with parentheses is declined by SetupTaskCall and reaches
// ExecFunctionBody instead.
TEST(ForceReleaseSim, ForcePreventsATaskBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd100;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The subroutine-body executor itself, which consulted the flag nowhere, so an
// assignment written here overwrote a forced variable where the same statement
// in an initial block or in a task did not.
TEST(ForceReleaseSim, ForcePreventsAFunctionBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x = 8'd100;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The same compound assignment written in a function body. This is not a second
// writer: #3500 routed the subroutine-body executor's `lhs op= rhs` to
// ApplyCompoundAssignOp, the single read-modify-write the ordinary statement
// executor performs, so this case and ForcePreventsACompoundAssign above now
// reach WriteVar by one route rather than two. What it claims is that the rule
// holds for the subroutine route as well, §10.4 putting procedural assignments
// "within procedures such as always, initial, task, and function".
//
// Before #3500 this case failed for a different reason than the initial-block
// one: the statement's right-hand side is itself the compound operator, so
// evaluating it reached EvalCompoundAssign, which wrote x before
// ExecFuncIdentifierAssign's own is_forced check could decline the write it was
// handed. Either way the answer was 60 and §10.6.2 says 50.
TEST(ForceReleaseSim, ForcePreventsACompoundAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x += 8'd10;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The select target written inside a subroutine body, which is the last of the
// six routes into WriteBitSelect. The subroutine-body executor is its own
// execution of every statement form, and its select arm ExecFuncSelectAssign
// calls TrySelectBlockingAssign directly rather than going through the
// statement executor's arms.
//
// A function is what reaches that arm, not a task. SetupTaskCall claims a
// kTaskDecl and ExecInlineTaskCall then walks the body through the ordinary
// ExecStmt, so `x[3] = 1'b1;` written in a `task poke;` retraces
// ForcePreventsABitSelectAssign's route instead of claiming a new one; a void
// function called with parentheses is declined by SetupTaskCall and reaches
// ExecFunctionBody, exactly as ForcePreventsAFunctionBodyAssign above records.
// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so this is the same statement wherever it is written,
// and it read 58 here as well.
TEST(ForceReleaseSim, ForcePreventsABitSelectAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x[3] = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The concatenation left-hand side written inside a subroutine body, which is
// a second route into UnpackConcatLhs rather than a second writer.
// ExecFuncWriteValue asks TryUnpackConcatLhs before anything else, so the
// subroutine-body executor reaches the same element deposit without ever
// passing ExecFuncIdentifierAssign, the arm that carries the is_forced check --
// a decline written into that arm rather than into UnpackConcatLhs would leave
// this form overriding the force. §10.4 puts procedural assignments "within
// procedures such as always, initial, task, and function", so this is the same
// statement wherever it is written, and a read 18 here as well.
//
// A void function is what claims that executor and not a task: SetupTaskCall
// claims a kTaskDecl and ExecInlineTaskCall then walks the body through the
// ordinary ExecStmt, as the comment on ForcePreventsATaskBodyAssign above
// records, so the same statement written in a task retraces the initial-block
// route instead of claiming this one.
TEST(ForceReleaseSim, ForcePreventsAConcatenationElementAssignInAFunctionBody) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  function void poke();\n"
      "    {a, b} = 16'h1234;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force a = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// The other half of §10.6.2: the override lasts "until a release procedural
// statement is executed on the variable", and a released variable "shall
// maintain its current value until the next procedural assignment to the
// variable is executed". That next assignment is the one inside the task here,
// so this is what says the decline above is bounded by the release rather than
// standing for the rest of the run.
TEST(ForceReleaseSim, ReleaseThenATaskBodyAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd77;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "    release x;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

// The compound operator's half of the other rule in §10.6.2: the override lasts
// "until a release procedural statement is executed on the variable", and a
// released variable "shall maintain its current value until the next procedural
// assignment to the variable is executed". Here that next assignment is itself
// a compound one, so the released 50 becomes 77 rather than staying at 50.
//
// ForcePreventsACompoundAssign and ForcePreventsACompoundAssignInAFunctionBody
// are the only other cases in this file that reach WriteVar, and both expect it
// to write nothing; a WriteVar that dropped every write would satisfy them.
// This is what says the new decline is the force's and is bounded by the
// release -- and the first `x += 8'd10;` here, which leaves x at 50 and not 60,
// is what makes 77 the answer rather than 87.
TEST(ForceReleaseSim, ReleaseThenACompoundAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "    release x;\n"
      "    x += 8'd27;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

// The select form's half of the other rule in §10.6.2: the override lasts
// "until a release procedural statement is executed on the variable", and a
// released variable "shall maintain its current value until the next procedural
// assignment to the variable is executed". Every select case above expects
// WriteBitSelect to write nothing, so a decline that never lifted would satisfy
// all four of them; this is what says the decline is the force's and is bounded
// by the release.
//
// The forced 50 is 8'b0011_0010, in which bit 3 and bit 0 are both clear, so
// the two writes separate three outcomes. 50 is the decline never lifting and
// neither write landing. 59 is the pre-release `x[3] = 1'b1;` having wrongly
// landed alongside the post-release one, 50 | 8 | 1. 51 is what §10.6.2 asks
// for: the write before the release declined and only the write after it
// landing. (A fourth reading, 58, would be the pre-release write landing and
// the post-release one not, which is the rule inverted.)
TEST(ForceReleaseSim, ReleaseThenABitSelectAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "    release x;\n"
      "    x[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 51u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §11.4.14.3 makes each name in a streaming target the
// recipient of an assignment -- "When a streaming_concatenation appears as the
// target of an assignment, the streaming operators perform the reverse
// operation; i.e., to unpack a stream of bits into one or more variables" --
// and §10.4 puts a blocking assignment written in an initial block among the
// procedural assignments occurring "within procedures such as always, initial,
// task, and function". Writing the target as a streaming concatenation does not
// take the statement out of the class the force overrides, so a keeps 50 and
// the slice it would have taken is dropped.
//
// UnpackStreamingConcatLhs is the writer every streaming target reaches, and
// this statement takes its default pass: ShouldForwardResolveUnpack claims only
// the shape in which a with-range names a target unpacked to its left, so the
// element walk lands in WriteStreamElement's resolved-lvalue arm and deposits
// through StoreStreamValueToVar, which consulted the flag nowhere. The route
// reaches none of the writers that do decline -- PerformBlockingAssign hands a
// streaming target to UnpackStreamingConcatLhs and returns before its own
// is_forced test, and WriteBitSelect, which #3519 gave the check, is reached
// for a select element and not for a plain name. So a took the high byte of
// 16'hABCD and read 171 where §10.6.2 leaves it at the forced 50.
//
// b is what says only the forced element was declined rather than the whole
// statement dropped. §11.4.14.3 consumes the stream "from its left (most
// significant) end" and §11.4.14.2 has `>>` perform "no re-ordering", so the
// sixteen bits reach the two eight-bit targets in the order they are written:
// a's 8'hAB and b's 8'hCD. b is seeded with 8'h0F first, a value neither slice
// carries, so a b left alone reads 15 and not the 205 it has to take.
TEST(ForceReleaseSim, ForcePreventsAStreamingConcatTargetWrite) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'h0F;\n"
      "    force a = 8'd50;\n"
      "    {>> {a, b}} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xCDu);
}

// The deferred route into the same unpacker, with the force executed after the
// assignment statement and before the region that carries it out.
// ScheduleStreamingConcatNba samples the right-hand side and queues an update
// event whose callback calls UnpackStreamingConcatLhs, so the writes happen in
// the NBA region of time 0, after the `force a = 8'd50;` written below the
// assignment has run in the active region. §10.4 names the nonblocking form
// among the procedural assignments whatever its left-hand side is, and §10.6.2
// asks what stands when the assignment is carried out: the force "shall
// override a procedural assignment ... until a release procedural statement is
// executed on the variable", and none has been, so the write finds a forced and
// declines it.
//
// The force is written after the assignment rather than before it because that
// is the order which separates a check inside the write from one asked at
// scheduling time. A decline asked when the event was queued reads is_forced
// false, the force not having executed yet, and the update region then deposits
// 8'h5A over the forced 50 -- the timing point
// ForcePreventsANonblockingBitSelectAssign makes for the select callbacks, made
// here for the unpacker's callback. Both orders read 90 before the fix, since
// the callback consulted the flag at no moment at all.
//
// b, seeded with 8'hF0, is again what says the statement was not dropped: the
// stream 16'h5A3C splits into a's 8'h5A and b's 8'h3C, so b reads 60. The `#1;`
// is what gives the deferred write its region before the run ends.
TEST(ForceReleaseSim, ForcePreventsANonblockingStreamingConcatTargetWrite) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'hF0;\n"
      "    {>> {a, b}} <= 16'h5A3C;\n"
      "    force a = 8'd50;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(vb->value.ToUint64(), 0x3Cu);
}

// The streaming form's half of the other rule in §10.6.2: the override lasts
// "until a release procedural statement is executed on the variable", after
// which the variable "shall not immediately change value and shall maintain its
// current value until the next procedural assignment to the variable is
// executed". That next assignment is the streaming one, so a leaves the forced
// 50 for the 8'hAB its slice carries and reads 171.
//
// The two cases above expect StoreStreamValueToVar to write nothing to a, and a
// decline that never lifted -- one keyed on a condition the release does not
// clear -- would satisfy both of them. b cannot say otherwise there, since b is
// never forced and takes its slice under either reading. So this is what says
// the decline is the force's and is bounded by the release, as
// ReleaseThenABitSelectAssignResumes says it for the select writer, and it is
// what keeps the fix from becoming a streaming write that never lands.
TEST(ForceReleaseSim, ReleaseThenAStreamingConcatTargetWriteResumes) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'h11;\n"
      "    force a = 8'd50;\n"
      "    release a;\n"
      "    {>> {a, b}} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_FALSE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 0xABu);

  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

}  // namespace
