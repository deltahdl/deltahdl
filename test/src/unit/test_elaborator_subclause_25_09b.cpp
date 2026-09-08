// §25.9 "Virtual interfaces": the statement positions its rules reach. Each
// case here writes one source that §25.9 rejects and varies only the statement
// position it stands in, holding the breach itself fixed. The first group
// writes the illegal addition of two virtual interfaces that
// AdditionOperator_Error in test_elaborator_subclause_25_09a.cpp writes at the
// top level of an initial block; the two groups after it write the illegal
// clocking-block access and the incompatible array-of-virtual-interface
// initializer element, and each names the walk it covers.
//
// §25.9 states which operations a virtual interface admits and names no
// statement those rules are suspended in, so every child-statement link Stmt
// declares is a position the rule reaches.
// Elaborator::WalkStmtsForVirtualInterfaceOps in
// src/elaborator/elaborator_validate_datatype_ops.cpp had written out six of
// the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so the addition
// elaborated clean in any of the other seven. The walk now takes its list from
// ForEachChildStmt, and the cases below are one per newly reached position:
// A.6.3's par_block (Stmt::fork_stmts), A.6.8's for_initialization and
// for_step (Stmt::for_inits, Stmt::for_steps), A.6.10's action_block
// (Stmt::assert_pass_stmt, Stmt::assert_fail_stmt), §18.16's randcase_item
// (Stmt::randcase_items), and A.6.12's rs_code_block (Stmt::rs_productions).
//
// The cases for which operations §25.9 admits at all, and for the declarations
// that may name a virtual interface, are in
// test_elaborator_subclause_25_09a.cpp, which the 1000-line cap in
// .github/workflows/deltahdl.yml separated this file from.
//
// The last group leaves the statement positions and covers the expression
// positions the other sentence of §25.9 reaches: "These components can only be
// used in procedural statements; they cannot be used in continuous assignments
// or sensitivity lists" (printed page 802). A component written directly in
// either place is already rejected, by
// Elaborator::ValidateVirtualInterfaceContAssign and
// Elaborator::ValidateVirtualInterfaceSensitivity in
// src/elaborator/elaborator_validate_datatype_ops.cpp, and
// ComponentInContinuousAssignLhs_Error, ComponentInContinuousAssignRhs_Error
// and ComponentInSensitivityList_Error in
// test_elaborator_subclause_25_09a.cpp pin that. What the sentence also reaches
// is a component written one expression deeper than those walks descend: an
// argument of a call standing in the continuous assignment, and the `iff`
// operand A.6.5 writes inside the event_expression a sensitivity list is made
// of. Two acceptance cases hold the far edge, because a walk that reached too
// far would bar a call argument in a procedural statement, which the same
// sentence permits, and a call carrying no virtual interface at all.

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceElaboration, AdditionOperatorInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial fork\n"
      "    c = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (c = a + b; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; c = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionPassStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionFailStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) else c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial randcase\n"
      "    1 : c = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration,
     AdditionOperatorInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { c = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 6,
                            "25.9"));
}

// The cases below cover two further §25.9 walks in
// src/elaborator/elaborator_validate_interface.cpp that had written their own
// list of the same six links, and are here rather than in a file of their own
// because the rule each enforces is §25.9's and this file holds §25.9's
// statement positions.

// §25.9 gives a virtual interface access to the clocking blocks of the
// interface it stands for, so `vif.cb.sig` naming something the interface does
// not declare as a clocking block is an error. WalkStmtsForVifClocking in
// src/elaborator/elaborator_validate_interface.cpp now takes its child-
// statement list from ForEachChildStmt, and the seven cases below are one per
// position it could not reach before.

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial fork\n"
      "    x = vif.cb.sig;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (x = vif.cb.sig; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = vif.cb.sig) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInAssertionPassStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial assert (1) x = vif.cb.sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 5,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInAssertionFailStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial assert (1) else x = vif.cb.sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 5,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial randcase\n"
      "    1 : x = vif.cb.sig;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = vif.cb.sig; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 7,
      "25.9"));
}

// §25.9 admits an interface instance as an element of an array-of-virtual-
// interface initializer only when the instance is of the element's interface
// type. WalkStmtsForArrayOfVifInit in
// src/elaborator/elaborator_validate_interface.cpp now takes its child-
// statement list from ForEachChildStmt, and its offending construct is a
// variable declaration rather than a statement, so only two of the seven
// positions it newly reaches can hold one.
//
// The five that cannot, each ruled out by Annex A:
//   - Stmt::for_inits: A.6.8 gives `for_variable_declaration ::= [ var ]
//     data_type variable_identifier = expression { , variable_identifier =
//     expression }`, which admits no unpacked dimension, so no array
//     declaration stands in a for initialization.
//   - Stmt::for_steps: A.6.8 gives `for_step_assignment ::=
//     operator_assignment | inc_or_dec_expression | function_subroutine_call`,
//     none of them a declaration.
//   - Stmt::assert_pass_stmt and Stmt::assert_fail_stmt: A.6.10 gives
//     `action_block ::= statement_or_null | [ statement ] else
//     statement_or_null`, and A.6.4's statement_item holds no data_declaration.
//   - Stmt::randcase_items: A.6.9 gives `randcase_item ::= expression :
//     statement_or_null`, a statement for the same reason.
// The two that can are A.6.3's `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword` and A.6.12's
// `rs_code_block ::= { { data_declaration } { statement_or_null } }`, both of
// which admit a data_declaration. Each declares the array through the
// `typedef virtual` spelling §25.9 itself writes, since A.6.3 and A.6.12 admit
// a data_declaration whatever names its data_type.

TEST(ArrayOfVirtualInterfaceInit, IncompatibleElementInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  typedef virtual bus_a vbus;\n"
      "  initial fork\n"
      "    vbus v[1] = '{u};\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface instance 'u' of type 'bus_b' is not "
                            "compatible with virtual interface element type "
                            "'bus_a'",
                            7, "25.9"));
}

TEST(ArrayOfVirtualInterfaceInit,
     IncompatibleElementInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  typedef virtual bus_a vbus;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { vbus v[1] = '{u}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface instance 'u' of type 'bus_b' is not "
                            "compatible with virtual interface element type "
                            "'bus_a'",
                            8, "25.9"));
}

// §25.9 bars a virtual interface component from a continuous assignment
// without naming a depth, and A.8.2 makes the argument of a
// subroutine_call an expression of the assignment's own right-hand side, so
// a component reached through a call stands in the continuous assignment as
// plainly as one written there. ExprUsesVirtualInterface in
// src/elaborator/elaborator_validate_datatype_ops.cpp descends lhs, rhs, base,
// index, condition, true_expr, false_expr and elements but not Expr::args, so
// the two cases below elaborated clean.

TEST(VirtualInterfaceElaboration, ComponentAsCallArgInContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pkt_if; logic v; endinterface\n"
      "module top;\n"
      "  virtual pkt_if pif;\n"
      "  wire q;\n"
      "  function logic idf(input logic z); return z; endfunction\n"
      "  assign q = idf(pif.v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 6, "25.9"));
}

// A second call around the first: the argument list is reached by the same
// recursion, so nesting is a distinct position only while args is unwalked.

TEST(VirtualInterfaceElaboration, ComponentInNestedCallArgInContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ctrl_if; logic e; endinterface\n"
      "module top;\n"
      "  virtual ctrl_if cif;\n"
      "  wire r;\n"
      "  function logic hold(input logic p); return p; endfunction\n"
      "  function logic wrap(input logic p); return hold(p); endfunction\n"
      "  assign r = wrap(hold(cif.e));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 7, "25.9"));
}

// A.6.5 gives `event_expression ::= [ edge_identifier ] expression [ iff
// expression ] | ...`, so the `iff` operand is written inside the
// event_expression the sensitivity list is made of, and §25.9 bars a component
// from a sensitivity list without carving any operand of one out. That §9.4.2.3
// has the `iff` operand read at the event rather than watched says when it is
// sampled, not where it is written, and the walk already treats a component
// anywhere under a sensitivity entry's signal as barred rather than only its
// root. Elaborator::ValidateVirtualInterfaceSensitivity read only
// EventExpr::signal, never EventExpr::iff_condition, so this elaborated clean.

TEST(VirtualInterfaceElaboration, ComponentInSensitivityIffCondition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface gate_if; logic g; endinterface\n"
      "module top;\n"
      "  virtual gate_if gif;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk iff gif.g) q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot appear in event "
                            "expression",
                            5, "25.9"));
}

// The same sentence of §25.9 that bars the three cases above states the
// permission they are the exception to, so a walk that took a call argument to
// be barred everywhere would reject this, which is legal: the call stands in a
// procedural statement, the position §25.9 names as the one components may be
// used in. ComponentInProceduralStatement_Ok in
// test_elaborator_subclause_25_09a.cpp holds the same edge for a component
// written directly.

TEST(VirtualInterfaceElaboration, ComponentAsCallArgInProceduralStmt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface log_if; logic s; endinterface\n"
      "module top;\n"
      "  log_if u();\n"
      "  virtual log_if lif;\n"
      "  logic w;\n"
      "  function logic thru(input logic t); return t; endfunction\n"
      "  initial begin\n"
      "    lif = u;\n"
      "    w = thru(lif.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// And the walk that now descends a call's arguments reaches every call in a
// continuous assignment, including the ones carrying no virtual interface. The
// module declares one so that the walk runs at all.

TEST(VirtualInterfaceElaboration, CallWithoutComponentInContAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface mem_if; logic m; endinterface\n"
      "module top;\n"
      "  virtual mem_if mif;\n"
      "  logic y;\n"
      "  wire z;\n"
      "  function logic same(input logic k); return k; endfunction\n"
      "  assign z = same(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
