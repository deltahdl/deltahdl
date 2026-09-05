#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

// §11.5.2 sends a select of an array element to §11.5.1 for judgement: "Once
// selected, bit-selects and part-selects shall be addressed in the same manner
// as net and variable bit-selects and part-selects (see 11.5.1)." §11.5.1 then
// bars this operand: "A bit-select or part-select of a scalar, or of a real
// variable or real parameter, shall be illegal." `arr[i]` selects one real
// element, and `[0]` selects a bit out of that real, so the source is illegal.
//
// This fails while CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp opens with ExprIdent(e->base), which
// returns nothing for `arr[i][0]` because the base of the outer select is
// another select rather than an identifier. The check then judges nothing and
// the run reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same operand written as a part-select. §11.5.1 names a bit-select and a
// part-select as two constructs, and `arr[i][3:0]` is the second of them.
// CheckRealSelectNode in src/elaborator/elaborator_validate.cpp chooses between
// the two messages on fields of the select node -- `index_end`,
// `is_part_select_plus` and `is_part_select_minus` -- that are separate from
// the `base` field a fix has to walk to reach the element. So a fix that
// reaches the real element could still name the wrong construct, and this case
// fails when it does as well as when no report is made.
TEST(RealSelect, PartSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same §11.5.1 breach written in the statement-target position, which
// CheckRealSelectStmt in src/elaborator/elaborator_validate.cpp reaches through
// `s->lhs` by a different call into CheckRealSelect than the one that reaches
// the source position through `s->rhs`. A fix applied to the source position
// alone therefore leaves this select unjudged, and this case fails when it
// does.
TEST(RealSelect, BitSelectOfARealArrayElementAsATargetIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial arr[i][0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// §11.5.1's other alternative, reached by the same §11.5.2 route: "A bit-select
// or part-select of a scalar, or of a real variable or real parameter, shall be
// illegal." `s` is declared `logic s[4]`, so `s[i]` selects one scalar element
// and `[0]` selects a bit out of that scalar.
//
// This fails while CheckScalarSelectNode in
// src/elaborator/elaborator_validate.cpp opens with ExprIdent(e->base) and
// stops when the answer is empty, which it is for a base that is itself a
// select. A fix that walks the chain for reals alone leaves this case silent.
TEST(SelectElaboration, BitSelectOfAScalarArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = s[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

// The control that stops a fix from rejecting the case §11.5.2 exists to
// permit. §11.5.2 reads: "To express bit-selects or part-selects of array
// elements, the desired word shall first be selected by supplying an address
// for each dimension." `mem[i]` is that one address and selects the word, and
// `[0]` then bit-selects a vector element, which §11.5.1 bars only for a scalar
// or a real. This fails when a fix reports every second address rather than
// reading the element's type.
TEST(SelectElaboration, BitSelectOfAPackedArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// This pins that "an address for each dimension" is counted against the
// declaration rather than assumed to be one. `mem` is declared with two
// unpacked dimensions, so `mem[i][i]` selects the word and `[0]` is the first
// address past the declaration's dimensions. This fails when a fix treats the
// second address as the bit-select whatever the declaration says, which rejects
// a legal element select of a two-dimensional array.
TEST(SelectElaboration, BitSelectOfATwoDimensionalArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4][4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §11.5.1: "A bit-select or part-select of a scalar, or of a real variable or
// real parameter, shall be illegal." The sentence names the parameter and not
// the position the parameter is written in, so a real parameter declared in a
// parameter port list draws the same report as one declared in the module
// body. This fails while a parameter port reaches BuildParamDeclShell in
// src/elaborator/elaborator_module.cpp, which writes the name into none of the
// elaborator's name sets. CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp then finds no entry for `P` in
// real_param_names_, and the run reports no error at all.
TEST(RealSelect, BitSelectOfARealParameterPortNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

// The same parameter port written with a part-select. §11.5.1 names a
// bit-select and a part-select as two constructs, and `P[3:0]` is the second of
// them. This pins that the parameter port position reaches the same message
// chosen on two axes -- the construct written and the operand selected -- as
// the module body position does, rather than a message of its own. This fails
// when a fix registers the parameter port on a path that emits its own text, as
// well as when the port draws no report at all.
TEST(RealSelect, PartSelectOfARealParameterPortNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  wire [3:0] y;\n"
      "  assign y = P[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

// A localparam written in the parameter port list draws the same report.
// BuildParamDeclShell in src/elaborator/elaborator_module.cpp distinguishes a
// localparam port from a parameter port through `decl->localparam_port_names`,
// which it reads to set `pd.is_localparam`. §6.20.2 makes a localparam a value
// parameter, so §11.5.1 -- "A bit-select or part-select of a scalar, or of a
// real variable or real parameter, shall be illegal" -- reaches it the same
// way. This fails when a fix registers the name only where
// `decl->localparam_port_names` does not hold it.
TEST(RealSelect, BitSelectOfARealLocalparamPortNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(localparam real P = 1.5);\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

// The control that keeps a legal use of a real parameter port legal. §11.5.1
// bars one construct -- "A bit-select or part-select of a scalar, or of a real
// variable or real parameter, shall be illegal" -- and `assign v = P;` writes
// neither a bit-select nor a part-select, so the source is legal. This stops a
// fix that reports every use of a real parameter port rather than every select
// of one.
TEST(RealSelect, RealParameterPortWithNoSelectIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  real v;\n"
      "  assign v = P;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The statement RealSelect.BitSelectOfARealArrayElementIsIllegal writes in an
// initial procedure, written in an always_comb procedure instead. §9.2.2.2
// says what that procedure is: "SystemVerilog provides a special always_comb
// procedure for modeling combinational logic behavior." The clause does not
// change what a statement inside the procedure may contain. §11.5.1 therefore
// bars `arr[i][0]` here exactly as it bars the same select in an initial
// procedure.
//
// This fails while `is_proc` in
// src/elaborator/elaborator_validate_matches.cpp names kAlwaysBlock and
// kInitialBlock alone. CheckRealSelectStmt runs behind that flag, so a
// kAlwaysCombBlock item never reaches it and the run reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysCombIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  always_comb v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same select written in an always_ff procedure. §9.2.2.4 says what that
// procedure is: "The always_ff procedure can be used to model synthesizable
// flip-flop logic behavior." The clause does not change what a statement
// inside the procedure may contain. §11.5.1 therefore bars `arr[i][0]` here as
// well, and the event control the procedure requires decides nothing about the
// select.
//
// This fails while `is_proc` in
// src/elaborator/elaborator_validate_matches.cpp names kAlwaysBlock and
// kInitialBlock alone. A kAlwaysFFBlock item reaches neither
// CheckRealSelectStmt nor the eight other calls behind that flag, and the run
// reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysFfIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  logic clk;\n"
      "  always_ff @(posedge clk) v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 6,
                            "11.5.1"));
}

// The same select written in an always_latch procedure. §9.2.2.3 says what
// that procedure is: "SystemVerilog also provides a special always_latch
// procedure for modeling latched logic behavior." The clause does not change
// what a statement inside the procedure may contain. §11.5.1 therefore bars
// `arr[i][0]` here as well.
//
// This fails while `is_proc` in
// src/elaborator/elaborator_validate_matches.cpp names kAlwaysBlock and
// kInitialBlock alone. A kAlwaysLatchBlock item never reaches
// CheckRealSelectStmt, and the run reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysLatchIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  always_latch v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same select written in a final procedure. §9.2.3 says what that
// procedure is: "The final procedure is like an initial procedure, defining a
// procedural block of statements, except that it occurs at the end of
// simulation time and executes without delays." The clause does not change
// what a statement inside the procedure may contain. §11.5.1 therefore bars
// `arr[i][0]` here exactly as it bars the same select in the initial procedure
// the clause compares this one to.
//
// This fails while `is_proc` in
// src/elaborator/elaborator_validate_matches.cpp names kAlwaysBlock and
// kInitialBlock alone. A kFinalBlock item never reaches CheckRealSelectStmt,
// and the run reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementInFinalIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  final v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// A.6.12 makes a randsequence code block a list of statements, so the §11.5.1
// walk reaches this select; mirrors ScalarBitSelectError in
// test/src/unit/test_elaborator_subclause_11_05_01a.cpp.
TEST(SelectElaboration, ScalarSelectInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = x[0]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            6, "11.5.1"));
}

// §16.3 makes an assertion's pass action a statement, held in
// Stmt::assert_pass_stmt; mirrors RealVariableBitSelectError in
// test/src/unit/test_elaborator_subclause_11_05_01a.cpp.
TEST(SelectElaboration, RealSelectInAnAssertPassArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial assert (1) y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "11.5.1"));
}

// A.6.8 makes a for-loop initialization a statement; mirrors
// IndexedPartSelectWidthMustBeConstant in
// test/src/unit/test_elaborator_subclause_11_05_01a.cpp, whose width is the
// same non-constant.
TEST(SelectElaboration, IndexedPartSelectWidthInAForInitIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  initial for (y = data[0+:w]; w < 2; w = w + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 5, "11.5.1"));
}

// The control on the three above: A.6.12's code block holds a part-select
// §11.5.1 allows, so a walk that newly reaches it must report nothing.
TEST(SelectElaboration, PartSelectInARandsequenceCodeBlockIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = data[7:4]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §11.5.1 says where a select may stand by saying nothing about it: "A
// bit-select or part-select of a scalar, or of a real variable or real
// parameter, shall be illegal." The sentence bars the operand, so it bars the
// operand wherever an expression may be written, and §11.5 writes out several
// of those places -- "A concatenation of other operands (including nested
// concatenations) can be specified as an operand" and "A function call is an
// operand".
//
// The cases below stand in the positions CheckRealSelect, CheckScalarSelect and
// CheckIndexedPartSelectWidth in src/elaborator/elaborator_validate.cpp did not
// reach. Each walk recursed through `lhs`, `rhs`, `base` and `index` and named
// no other link, so a select written under the conditional operator, in a call
// argument, inside a concatenation or in the second bound of a part-select was
// judged by nothing. Every source here but the one control was accepted.

// The conditional operator's first operand, which reaches the select through
// `condition`. §11.4.11 gives the operator three expressions and makes this one
// the test; §11.5.1 bars a bit-select of a real variable in it as in any other.
TEST(RealSelect, BitSelectOfARealInAConditionalConditionIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  assign v = r[0] ? 1.0 : 2.0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "11.5.1"));
}

// The conditional operator's second operand, reached through `true_expr`. It is
// a separate link from `condition`, so a fix that walks one and not the other
// leaves this case unjudged.
TEST(RealSelect, BitSelectOfARealInAConditionalTrueArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  logic c;\n"
      "  assign v = c ? r[0] : 1.0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The conditional operator's third operand, reached through `false_expr`, which
// is a third link again.
TEST(RealSelect, BitSelectOfARealInAConditionalFalseArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  logic c;\n"
      "  assign v = c ? 1.0 : r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// A call argument, reached through `args`. §11.5 makes the call itself an
// operand -- "A function call is an operand" -- and the argument inside it is
// an expression like any other, so §11.5.1 bars this select too.
TEST(RealSelect, BitSelectOfARealInACallArgumentIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  function automatic real ident(input real a);\n"
      "    ident = a;\n"
      "  endfunction\n"
      "  assign v = ident(r[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 7,
                            "11.5.1"));
}

// A concatenation element, reached through `elements`. §11.5 makes the
// concatenation an operand and its elements operands in turn, so §11.5.1
// reaches inside one. Written as a part-select so that the message the report
// names is the part-select form: a walk that newly reaches the node still has
// to choose between §11.5.1's two constructs from the fields of that node.
TEST(RealSelect, PartSelectOfARealInAConcatenationNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [4:0] y;\n"
      "  assign y = {r[3:0], 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "11.5.1"));
}

// The second bound of a non-indexed part-select, reached through `index_end`.
// §11.5.1 gives that form as `vect[msb_expr:lsb_expr]`, and the walk followed
// `index` alone, so the msb bound was searched for a further select and the lsb
// bound was not. The bound written here is not a constant either, which draws
// its own report; the one this case names is the §11.5.1 report about the real
// operand.
TEST(RealSelect, BitSelectOfARealInAPartSelectBoundIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] y;\n"
      "  assign y = d[3:r[0]];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// §11.5.1 bars a bit-select of a real variable or a scalar and no other, so a
// bit-select of a vector is legal in the conditional operator's second operand
// exactly as it is legal on an assignment. This is what fails when a walk that
// newly reaches a position reports every select it finds there rather than the
// selects §11.5.1 names.
TEST(RealSelect, BitSelectOfAVectorInAConditionalTrueArmIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  logic c;\n"
      "  logic y;\n"
      "  assign y = c ? v[0] : 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The scalar half of §11.5.1's sentence in an unwalked position.
// CheckScalarSelect in src/elaborator/elaborator_validate.cpp is written in the
// same four-link shape as CheckRealSelect, so it has the same gap, and a fix
// applied to the real walk alone leaves this case accepted.
TEST(SelectElaboration, ScalarBitSelectInAConditionalTrueArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s;\n"
      "  logic c;\n"
      "  logic y;\n"
      "  assign y = c ? s[0] : 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

// §11.5.1's rule on the indexed part-select in an unwalked position: "the
// width_expr shall be a positive constant integer expression".
// CheckIndexedPartSelectWidth in src/elaborator/elaborator_validate.cpp is the
// third walk written in the four-link shape, and a concatenation element is a
// position none of the three reached.
TEST(SelectElaboration, IndexedPartSelectWidthInAConcatenationIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [8:0] y;\n"
      "  assign y = {data[0+:w], 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 5, "11.5.1"));
}

// §11.5.1: "The actual bit that is accessed by an address is, in part,
// determined by the declaration of acc" -- the clause sets `logic [15:0] acc`
// beside `logic [2:17] acc` and observes that one value of an index reaches a
// different bit in each. §27.4 makes a generate block "a separate scope and a
// new level of hierarchy when it is instantiated" and says nothing that would
// make §11.5.1 stop there, so a parameter declared inside a block is addressed
// over its declared range exactly as one declared among the module's own items
// is. SelectElaboration.ParameterBitSelectIsAddressedOverItsDeclaredRange in
// test_elaborator_subclause_11_05_01a.cpp is the module-level twin.
//
// P is declared [2:17], which ascends, so index 17 names its least significant
// bit and 16'h0001 puts a 1 there. Reading the index as a distance above the
// least significant end asks for offset 17 of a sixteen-bit value and answers
// 0. Neither bound is 0, so no index makes the two coincide and the case can
// fail, which the "Tests" section of .claude/CLAUDE.md requires of the input.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamRangeRegistryGuard:
// RegisteredParamRange then answers nothing for the whole of a block's body,
// and SelectOffset in src/elaborator/const_eval.cpp takes the index for the
// offset.
TEST(PackedRangeSelect,
     SelectInAGenerateBlockUsesTheBlockParameterDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam logic [2:17] P = 16'h0001;\n"
      "      localparam Q = P[17];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_resolved);
  EXPECT_EQ(q->resolved_value, 1);
}
