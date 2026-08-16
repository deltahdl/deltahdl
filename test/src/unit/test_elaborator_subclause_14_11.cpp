#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CycleDelayElab, WithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

// §14.11: the missing-default-clocking diagnostic is conditional, not a blanket
// rejection of ##. When a default clocking block governs the current module the
// rule must stay silent, so the same cycle delay elaborates cleanly.
TEST(CycleDelayElab, WithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11 + §14.12: what constitutes a cycle is fixed by the default clocking in
// effect. §14.12 lets the default be established by a reference/assignment form
// -- `default clocking <name>;` naming an already-declared clocking block --
// rather than an inline default block. The missing-default-clocking rule must
// consume that reference form too and stay silent, since a default IS in
// effect.
TEST(CycleDelayElab, WithReferenceFormDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the missing-default-clocking requirement is stated for the current
// module, interface, checker, or program -- not only a module. A cycle delay in
// a program with no default clocking in effect is rejected. The scope is
// exercised end-to-end: the program is declared with real syntax and reached by
// instantiating it from a top module so the elaborator visits its body.
TEST(CycleDelayElab, ProgramScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

// §14.11: the same program with a default clocking in effect elaborates
// cleanly. Pairing this positive with the negative above isolates the
// diagnostic to the missing-default-clocking rule rather than any incidental
// program-scope error.
TEST(CycleDelayElab, ProgramScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the interface is another enumerated scope for the requirement. A
// cycle delay in an instantiated interface with no default clocking is
// rejected.
TEST(CycleDelayElab, InterfaceScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

// §14.11: the interface positive pair -- a default clocking in effect keeps the
// rule silent for the same cycle delay in interface scope.
TEST(CycleDelayElab, InterfaceScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11 names the checker as the fourth scope whose missing default clocking
// is an error, and a cycle delay in an instantiated checker without one is
// rejected. Two rules independently reject this source, though -- §17.5 allows
// an initial procedure in a checker only an event control for timing -- so it
// is the companion below, which supplies the default clocking and is still
// rejected, that says which of them is doing the work.
TEST(CycleDelayElab, CheckerScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk;\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

// The checker scope has no positive pair, unlike the module, interface and
// program scopes above: supplying the default clocking §14.11 asks for does not
// make this legal, because a second rule reaches it first.
//
// §17.5: an initial procedure in a checker body "may contain let declarations,
// immediate, deferred, and concurrent assertions, and a procedural timing
// control statement using an event control only". A.6.5 lists the three
// alternatives of procedural_timing_control -- delay_control, event_control and
// cycle_delay -- as siblings, so a cycle delay is not an event control and has
// no place in a checker initial procedure whatever clocking is in effect.
// §14.11's own description points the same way: it defines ## as a wait for
// clocking block events, which is what it does, not what the grammar calls it.
//
// So §14.11 naming the checker among its four scopes is not about a cycle delay
// written as a procedural statement in a checker procedure. The distinction
// this test now records is that adding the default clocking changes nothing
// here, which is exactly what separates checker scope from the three above.
TEST(CycleDelayElab, CheckerInitialCycleDelayRejectedWithDefaultClocking) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk;\n"
      "    default clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  // The rejection this case records is §17.5's, not §14.11's: the default
  // clocking above silences ValidateCycleDelayDefaultClocking, and what is left
  // is the checker-initial rule reported by CheckCheckerBodyItemRules in
  // src/elaborator/elaborator_items_udp.cpp.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an initial procedure in checker 'chk' may use only an event control", 6,
      "17.5"));
}

// §14.11: the missing-default-clocking check applies to a cycle delay wherever
// it sits in a process body, not only at the top level. The validator descends
// into nested control flow, so a ## buried inside a branch is still rejected
// when no default clocking governs the module.
TEST(CycleDelayElab, NestedCycleDelayWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

// §14.11: a cycle delay is not legal as an intra-assignment delay on a blocking
// assignment. A default clocking is present so the missing-default-clocking
// rule stays silent; the only remaining violation is the intra-assignment ##.
TEST(CycleDelayElab, IntraAssignBlockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a = ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

// §14.11: the same prohibition applies to a nonblocking assignment carrying a
// cycle-delay intra-assignment timing control.
TEST(CycleDelayElab, IntraAssignNonblockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a <= ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

// §14.11: the intra-assignment cycle-delay prohibition applies wherever the
// offending assignment sits, not only at the top of a process body. The
// validator descends into nested control flow, so an intra-assignment ## buried
// inside a branch is still rejected even when a default clocking is present.
TEST(CycleDelayElab, NestedIntraAssignCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      a <= ##2 b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

// §14.11: the intra-assignment prohibition is about the timing control, not the
// exact target shape. A cycle delay on a blocking assignment whose target is a
// bit-select of an ordinary variable is still an illegal intra-assignment delay
// -- the target is not a clocking-block variable, so it cannot be a synchronous
// drive. A default clocking is present so only the intra-assignment rule fires.
TEST(CycleDelayElab, IntraAssignBitSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3] = ##3 b[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

// §14.11: the same holds for a part-select target on a nonblocking assignment.
// A slice of an ordinary variable is not a clockvar, so the leading ## is an
// illegal intra-assignment delay rather than a synchronous drive.
TEST(CycleDelayElab, IntraAssignPartSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3:0] <= ##2 b[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

// §14.11: a concatenation target is another non-clockvar lvalue form. A cycle
// delay on a blocking assignment to a concatenation of ordinary variables is an
// illegal intra-assignment delay, not a synchronous drive, and must be
// rejected.
TEST(CycleDelayElab, IntraAssignConcatLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    {a, b} = ##3 c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 8, "14.11"));
}

// §14.11/§14.16: a bit-select of a clocking output variable is still a
// synchronous drive, so a leading cycle delay on it is legal. The tightened
// discriminator must peel the select and recognize the clockvar underneath
// rather than treating any non-identifier target as an intra-assignment.
TEST(CycleDelayElab, SynchronousDriveBitSelectWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data[3] <= ##1 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11/§14.16: the prohibition targets plain assignments, not synchronous
// drives. A clocking-block variable driven through a member access with a cycle
// delay is a legal synchronous drive and must not be flagged.
TEST(CycleDelayElab, SynchronousDriveWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##1 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: "if no default clocking has been specified for the current module,
// interface, checker, or program, then the compiler shall issue an error". The
// sentence is stated against the module, not against a process, so an always
// block that a generate if holds is judged by the same default clocking as one
// written beside it. The report stands at the always keyword on line 3, the
// location of the process item holding the cycle delay. A walk that reads
// ModuleItem::body off the items of the module reaches no generate item's
// gen_body, so the nested ## is accepted silently.
TEST(CycleDelayElab, GenerateBlockWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  if (1) begin : g\n"
      "    always begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

// §14.11: the same sentence -- "if no default clocking has been specified for
// the current module, interface, checker, or program, then the compiler shall
// issue an error" -- reaches a generate loop's body as readily as a generate
// if's, and a loop is a different ModuleItemKind, so one walk has to cover
// both. The report stands at the always keyword on line 3. Without that walk
// the elaborator accepts the nested ## silently.
TEST(CycleDelayElab, GenerateLoopWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
      "    always begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

// §14.11: "cycle delay timing controls shall not be legal for use in
// intra-assignment delays in either blocking or nonblocking assignment
// statements". The sentence names no process, so an assignment in a task body
// breaks the rule exactly as one in an initial block does. The report stands at
// the assignment on line 6. A default clocking is present so the
// missing-default-clocking rule stays silent. A walk that reads
// ModuleItem::body reaches no subroutine's func_body_stmts, so the ## in the
// task is accepted silently.
TEST(CycleDelayElab, IntraAssignCycleDelayInTaskErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  task t;\n"
      "    q = ##2 d;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

// §14.11: the same sentence -- "cycle delay timing controls shall not be legal
// for use in intra-assignment delays in either blocking or nonblocking
// assignment statements" -- covers a function body, and the subclause asserted
// here is what distinguishes the rule that fired. §13.4 separately forbids a
// time-controlling statement in a function, and the function-body checker in
// src/elaborator/elaborator_validate_funcbody.cpp reports that one under
// "13.4", so a §14.11 walk that never reached func_body_stmts would leave this
// case with no 14.11 report at all. The report stands at the assignment on line
// 6.
TEST(CycleDelayElab, IntraAssignCycleDelayInFunctionErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  function void fn();\n"
      "    q = ##2 d;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

// §14.11/§14.16: the intra-assignment prohibition reaches a task body, and the
// synchronous-drive exemption has to travel with it. §14.16 makes a leading
// cycle delay on a write to a clocking output variable a synchronous drive
// rather than an intra-assignment delay, so this source is legal wherever the
// drive is written. A walk that reached func_body_stmts while dropping the
// clockvar test would reject a design the standard permits. There is no report
// to name, so the assertion is that the source was accepted.
TEST(CycleDelayElab, SynchronousDriveInTaskNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic d;\n"
      "  task t;\n"
      "    cb.data <= ##2 d;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
