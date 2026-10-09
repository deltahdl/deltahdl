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
// positions the other sentence of §25.9 reaches: the components are for
// procedural statements only, never for continuous assignments or sensitivity
// lists (printed page 802). A component written directly in either place is
// already rejected, by Elaborator::ValidateVirtualInterfaceContAssign and
// Elaborator::ValidateVirtualInterfaceSensitivity in
// src/elaborator/elaborator_validate_datatype_ops.cpp, and
// ComponentInContinuousAssignLhs_Error, ComponentInContinuousAssignRhs_Error
// and ComponentInSensitivityList_Error in test_elaborator_subclause_25_09a.cpp
// pin that. What the sentence also reaches is a component written one
// expression deeper than those walks descend: an argument of a call standing in
// the continuous assignment, and the `iff` operand A.6.5 writes inside the
// event_expression a sensitivity list is made of. Two acceptance cases hold the
// far edge, because a walk that reached too far would bar a call argument in a
// procedural statement, which the same sentence permits, and a call carrying no
// virtual interface at all.

#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "common/source_loc.h"
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
      "    static vbus v[1] = '{u};\n"
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

// §25.9 admits an interface instance as a virtual interface's source, and an
// interface instance is reached in more ways than its simple name. Each case
// below assigns one, and none is the "can only be assigned from" refusal.

constexpr const char* kViSourceRefusal =
    "virtual interface can only be assigned from another virtual interface, an "
    "interface instance, or null";

// An element of an array of interface instances.
TEST(VirtualInterfaceElaboration, SourceIsAnInstanceArrayElement_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "module top;\n"
      "  SBus s[0:1]();\n"
      "  virtual SBus v;\n"
      "  initial v = s[1];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 5, "25.9"));
}

// An instance in a loop generate block, named through the block instance.
TEST(VirtualInterfaceElaboration, SourceIsAGenerateBlockInstance_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "module top;\n"
      "  for (genvar i = 0; i < 3; i++) begin : g\n"
      "    SBus s();\n"
      "  end\n"
      "  virtual SBus v;\n"
      "  initial v = g[1].s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 7, "25.9"));
}

// A program's interface port, which denotes the instance it is connected to.
TEST(VirtualInterfaceElaboration, SourceIsAnInterfacePort_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "program P(SBus b);\n"
      "  virtual SBus v;\n"
      "  initial v = b;\n"
      "endprogram\n"
      "module top;\n"
      "  SBus s();\n"
      "  P p(s);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 4, "25.9"));
}

// The virtual interface a class function returns.
TEST(VirtualInterfaceElaboration, SourceIsAFunctionsResult_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "class Pool;\n"
      "  virtual SBus vs[2];\n"
      "  function virtual SBus pick(int i); return vs[i]; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  Pool p;\n"
      "  virtual SBus got;\n"
      "  initial got = p.pick(1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 9, "25.9"));
}

// §25.9 reaches every component of the instance a virtual interface
// represents, and §25.3 lets an interface hold an instance of another, so
// `vo.in.v` names a member of outer_if.
TEST(VirtualInterfaceElaboration, NestedInterfaceInstanceIsAMember_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface inner_if; int v; endinterface\n"
      "interface outer_if;\n"
      "  int w;\n"
      "  inner_if in();\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if o();\n"
      "  virtual outer_if vo;\n"
      "  initial begin\n"
      "    vo = o;\n"
      "    vo.in.v = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'in' is not a clocking block or member of "
                             "interface 'outer_if'",
                             11, "25.9"));
}

// §25.9: a call through a virtual interface names a task or a function of the
// interface it refers to an instance of, so one naming nothing that interface
// declares is reported, while a call of its task, a method call through a
// class handle, a package's function behind its scope and a call through a
// chain are not (#5808).
TEST(VirtualInterfaceCallElaboration, ACallNamingNothingTheInterfaceDeclares) {
  ElabFixture f;
  ElaborateSrc(
      "package p; function void pf(); endfunction endpackage\n"
      "interface other; task nosuch(); endtask endinterface\n"
      "interface ifc; logic x; task t(); endtask endinterface\n"
      "module top;\n"
      "  class C; function void g(); endfunction C h; endclass\n"
      "  ifc i (); virtual ifc v = i; C c = new;\n"
      "  initial if (0) begin\n"
      "    v.nosuch();\n"
      "    v.t(); c.g(); p::pf(); c.h.g();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            8, "25.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 9u) << diag.message;
  }
}

// §25.9: a call through a virtual interface a block declares, or through a
// class property of virtual interface type, names a task or a function of
// its interface too (#5809). The calls of line 14 name the interface's task
// through a module's class, the compilation unit's, a static property, a chain
// of handles, a hierarchical name and a package's class, or call a method
// through a function's result, and none is reported.
TEST(VirtualInterfaceCallElaboration,
     ACallThroughABlocksOrAPropertysVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "package p; class K; K f; function void t(); endfunction endclass "
      "endpackage\n"
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; static virtual ifc sv; H k; "
      "function void m(); endfunction endclass\n"
      "module top;\n"
      "  import p::*;\n"
      "  class C; virtual ifc cv; endclass\n"
      "  function H mkh(); return null; endfunction\n"
      "  ifc i (); virtual ifc v = i; H h = new; C c = new; "
      "K kk = new;\n"
      "  initial if (0) begin\n"
      "    virtual ifc w;\n"
      "    w = i;\n"
      "    w.nosuch();\n"
      "    h.vif.nosuch();\n"
      "    w.t(); h.vif.t(); c.cv.t(); mkh().m(); H::sv.t(); h.k.vif.t(); "
      "top.v.t(); kk.f.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            12, "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            13, "25.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 14u) << diag.message;
  }
}

// §25.9 with §26.3: the class holding a virtual interface property may be one
// a package declares, brought in by an explicit import, written behind its
// package's scope, or imported in the compilation unit, and a call through
// the property naming nothing the interface declares is reported each way
// (#5810). Line 14's calls, one through a struct whose type is no class, are
// not.
TEST(VirtualInterfaceCallElaboration,
     ACallThroughAPackageClasssVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package p; class K; virtual ifc vif; function void m(); endfunction "
      "endclass class Q; virtual ifc vif; endclass endpackage\n"
      "package r; class R; virtual ifc vif; endclass endpackage\n"
      "package e; endpackage\n"
      "import r::R;\n"
      "module top;\n"
      "  import p::K; import e::*; import p::Q;\n"
      "  typedef struct { K h; } S;\n"
      "  K k = new; p::Q q = new; R rr = new; S s;\n"
      "  initial if (0) begin\n"
      "    k.vif.nosuch();\n"
      "    q.vif.nosuch();\n"
      "    rr.vif.nosuch();\n"
      "    k.vif.t(); s.h.m();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {11u, 12u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'nosuch' names no task or function of "
                              "interface 'ifc'",
                              kLine, "25.9"))
        << kLine;
  }
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 14u) << diag.message;
  }
}

// §25.9 with §6.18: a class handle declared through a typedef of the class
// holds the class's virtual interface property all the same, through a chain
// of the module's typedefs, the compilation unit's, one a wildcard import
// brings in, one behind its package's scope and one the compilation unit's
// import brings in, and a call through it naming nothing the interface
// declares is reported each way (#5811).
TEST(VirtualInterfaceCallElaboration,
     ACallThroughATypedefdClassHandlesVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "package p; class K; virtual ifc vif; endclass typedef K KT; "
      "typedef K KI; endpackage\n"
      "package q; class QC; virtual ifc vif; endclass typedef QC QT; "
      "endpackage\n"
      "import q::*;\n"
      "typedef H HU;\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef H HT; typedef HT HT2;\n"
      "  HT2 a = new; HU b = new; KI c = new; p::KT d = new; QT e = new;\n"
      "  initial if (0) begin\n"
      "    a.vif.nosuch();\n"
      "    b.vif.nosuch();\n"
      "    c.vif.nosuch();\n"
      "    d.vif.nosuch();\n"
      "    e.vif.nosuch();\n"
      "    a.vif.t(); d.vif.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {12u, 13u, 14u, 15u, 16u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'nosuch' names no task or function of "
                              "interface 'ifc'",
                              kLine, "25.9"))
        << kLine;
  }
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 17u) << diag.message;
  }
}

// §25.9 with §6.18: a chain of eight typedefs, as many as the search follows,
// still reaches the class, so a call through a handle of the last naming
// nothing the interface declares is reported (#5811).
TEST(VirtualInterfaceCallElaboration, AnEightTypedefChainReachesTheClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "module top;\n"
      "  typedef H T1; typedef T1 T2; typedef T2 T3; typedef T3 T4;\n"
      "  typedef T4 T5; typedef T5 T6; typedef T6 T7; typedef T7 T8;\n"
      "  T8 g = new;\n"
      "  initial if (0) g.vif.nosuch();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            7, "25.9"));
}

}  // namespace
