#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §6.5 rules on printed page 91 that data is declared before it is used,
// implicit nets aside, and two walks in
// src/elaborator/elaborator_scope_rules_names.cpp answer that question of a
// procedural assignment: CollectProcLocalNames gathers the names a procedural
// block declares and CollectProcRhsIdents gathers the names its assignments
// read, and Elaborator::ValidateUnresolvedReferences reports a read that
// neither the block nor the module declares.
//
// Each walk wrote out nine of the thirteen child-statement links Stmt declares,
// and both now take the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The four links neither reached
// are Stmt::assert_pass_stmt, Stmt::assert_fail_stmt, the body of a randcase
// item, and the two statement lists Stmt::rs_productions holds --
// RsProd::code_stmts and RsRule::weight_code, which ForEachRandsequenceRuleStmt
// reaches by different members, so each of those is its own position and each
// gets its own case below.
//
// The five cases here cover CollectProcLocalNames, whose omission cost a report
// made wrongly rather than a report not made: a declaration the walk did not
// see is absent from the set of block-local names, so the read of that name
// resolves against nothing and is reported as unresolved under §23.9 although
// §6.5 was satisfied where it stands. Each source declares a variable and reads
// it in one newly reached position, and asserts the source is accepted, so each
// fails if CollectProcRhsIdents is put on the shared list while
// CollectProcLocalNames is left with its own. The rejecting counterparts, one
// per position, stand in test/src/unit/test_elaborator_subclause_26_03b.cpp.
//
// An accepted source produces no report, so there is nothing here for
// ReportedError in lib/cpp/test_helpers/helpers_reported_error.h to name.
//
// `stmt` is the whole statement of the initial procedure and may run to several
// lines. `a` is declared in an unnamed begin-end, which §23.9 lists among the
// elements defining a scope, and `r` is the module variable it is read into.
bool ElaboratesWithBlockLocalIn(const std::string& stmt) {
  return ElabOk("module m;\n  int r;\n  initial\n    " + stmt +
                "\nendmodule\n");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(NetsAndVariables, BlockLocalReadInAnAssertionPassStmtIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn("assert (r) begin int a; r = a; end"));
}

TEST(NetsAndVariables, BlockLocalReadInAnAssertionFailStmtIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("assert (r) else begin int a; r = a; end"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.5 is a rule about the source, so the declaration answers for the
// read whether the weighted draw would select the item or not.
TEST(NetsAndVariables, BlockLocalReadInARandcaseItemIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "randcase 1: begin int a; r = a; end endcase"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(NetsAndVariables, BlockLocalReadInARandsequenceCodeBlockIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("begin\n"
                                 "      randsequence(main)\n"
                                 "        main : { begin int a; r = a; end };\n"
                                 "      endsequence\n"
                                 "    end"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(NetsAndVariables, BlockLocalReadInARandsequenceWeightCodeBlockIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin int a; r = a; end };\n"
      "        alt : { r = 1; };\n"
      "      endsequence\n"
      "    end"));
}

// §23.7 calls `v.f` a dotted name and rules that a member select's first name
// component matches a data object, which is what LhsBaseName answers for each
// of the six checks that reduce an lvalue to its base. Its member arm followed
// `base`, a field only a select carries, so it walked off the end of every
// dotted name and answered nothing, and each caller reads nothing as "no base
// to check". §6.5's rule against procedural and continuous assignments mixed
// over the terms of one variable's longest static prefix expansion is the one
// that makes that observable: the continuous assignment names `v` and the
// procedural one names a member of it, which is a term in the same expansion.
TEST(NetsAndVariables,
     MemberQualifiedProceduralTargetIsAWriteToItsBaseVariable) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic f; } s_t;\n"
      "  s_t v;\n"
      "  logic a, b;\n"
      "  assign v = a;\n"
      "  initial v.f = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
}

// §23.7.1: a name with a package or class scope resolution prefix (::) always
// resolves downwards, so the name before `::` is a package or a class rather
// than a data object, and the walk ends there rather than returning it. A net
// and a package can carry one name, which is what lets this case put the two
// together: descending through the prefix would record `p::x = 1` as a
// procedural write to the net `p` and draw §10.4's report of a net as a
// procedural assignment's left-hand side over a statement that writes no net at
// all.
TEST(NetsAndVariables, PackageScopedAssignmentIsNotAWriteToThePrefixName) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  wire p;\n"
             "  logic a;\n"
             "  assign p = a;\n"
             "  initial p::x = 1;\n"
             "endmodule\n",
             f));
}

// §10.4 with §23.2.2.3 (printed page 735): an output port declared with no
// port kind and no data type, `output b`, is a net of the default net type,
// the clause's own `mh8 (output x)`, so `b <= a` inside an always_ff is a
// procedural assignment whose left-hand side is no variable and is reported
// as the write to a declared `wire w` above is. This is the suite's
// 14.3--clocking-block-signals-error.sv (#2917), whose clocking block declares
// `output b` as a clockvar and whose always_ff writes the port itself; the
// port was known to the rule as no net and the write was accepted.
TEST(NetsAndVariables, UntypedOutputPortIsANetAProcedureCannotWrite) {
  ElabFixture f;
  Elaborate(
      "module top(input clk, input a, output b, output c);\n"
      "  clocking ck1 @(posedge clk);\n"
      "    default input #10ns output #5ns;\n"
      "    input a;\n"
      "    output b;\n"
      "    output #3ns c;\n"
      "  endclocking\n"
      "  always_ff @(posedge clk) begin\n"
      "    b <= a;\n"
      "    c <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'b' cannot be the target of a procedural assignment", 9, "10.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'c' cannot be the target of a procedural assignment", 10, "10.4"));
}

// §23.2.2.3: an output port declared with an explicit data type and no port
// kind, `output logic b`, is a variable, so the same always_ff write is the
// ordinary procedural assignment §10.4 allows and nothing is reported. This is
// the shape of the suite's passing 14.3--clocking-block-signals.sv, and the
// discriminating half of the case above: a rule that took every output port
// for a net would report it.
TEST(NetsAndVariables, TypedOutputPortIsAVariableAProcedureMayWrite) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module top(input clk, input a, output logic b);\n"
             "  always_ff @(posedge clk) b <= a;\n"
             "endmodule\n",
             f));
}

// §6.5 (printed page 90): any number of continuous assignments, one or more,
// may write a net, the single-assignment rule being stated of a variable's
// longest static prefix alone. Two continuous assignments to one bit of a
// vector net, or to one element of a wor array, are two drivers the net type
// resolves, and were reported as overlapping elements.
TEST(NetsAndVariables, NetSelectTakesSeveralContinuousAssignments) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  wire [3:0] a;\n"
             "  wor r[2];\n"
             "  assign a[0] = 1'b1;\n"
             "  assign a[0] = 1'b0;\n"
             "  assign r[0] = 1'b0;\n"
             "  assign r[0] = 1'b1;\n"
             "endmodule\n",
             f));
}

// §6.5: a procedural assignment written in a task or a function body writes
// the variable as one in a process does, so a variable a continuous assignment
// also writes is written by a mixture of the two; a subroutine's own formal or
// local of the same name is not that variable.
TEST(NetsAndVariables, SubroutineWriteMeetsContinuousAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y, z;\n"
      "  task automatic t(); y = a; endtask\n"
      "  function automatic void g(output logic z); z = a; endfunction\n"
      "  always_comb t();\n"
      "  assign y = a;\n"
      "  assign z = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' has both continuous and procedural "
                            "assignments",
                            6, "6.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "variable 'z' has both continuous and procedural "
                             "assignments",
                             7, "6.5"));
}

// §6.5 with §27.4: a generate block is a scope of its own, so a variable it
// declares is another variable from the module's of the same name, and each
// takes the one continuous assignment written to it.
TEST(NetsAndVariables, AGenerateBlocksVariableIsNotTheModulesOfThatName) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic w;\n"
      "  assign w = 1'b0;\n"
      "  if (1) begin : a\n"
      "    logic w;\n"
      "    assign w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The module's variable is one variable however many iterations of a loop
// generate construct write it, so a continuous assignment in every iteration
// is more than one assignment to it.
TEST(NetsAndVariables, EveryIterationAssigningTheModulesVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic w;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    assign w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'w'", 4,
                            "6.5"));
}

// An iteration's own variable written by both kinds of assignment within the
// iteration is reported as a mixture, and no iteration's continuous
// assignment is counted against another's.
TEST(NetsAndVariables, AnIterationsVariableTakesNoMixtureOfAssignments) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    logic w;\n"
      "    assign w = 1'b0;\n"
      "    initial w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'w' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "multiple continuous assignments to 'w'", 4,
                             "6.5"));
}

// §6.5's own example of a structure: a continuous assignment to abc.C,
// primitive outputs on abc.A[0] to abc.A[3] and a procedural write to abc.B,
// each covering terms of abc that no other writer covers.
constexpr const char* kAbcExampleHead =
    "module m(input logic clk, input logic sel);\n"
    "  struct {\n"
    "    bit [7:0] A;\n"
    "    bit [7:0] B;\n"
    "    byte C;\n"
    "  } abc;\n"
    "  assign abc.C = sel ? 8'hBE : 8'hEF;\n"
    "  not (abc.A[0], abc.B[0]),\n"
    "      (abc.A[1], abc.B[1]),\n"
    "      (abc.A[2], abc.B[2]),\n"
    "      (abc.A[3], abc.B[3]);\n"
    "  always @(posedge clk) abc.B <= abc.B + 1;\n";

TEST(NetsAndVariables, SectionsStructExampleIsAccepted) {
  EXPECT_TRUE(ElabOk(std::string(kAbcExampleHead) + "endmodule\n"));
}

// Its two illegal additions. A second continuous assignment to abc.C is
// reported. A procedural write to abc.A[7:3] is reported against the primitive
// output on abc.A[3], which its part-select overlaps, and against none of the
// outputs on abc.A[0] to abc.A[2], which it does not.
TEST(NetsAndVariables, SectionsStructExampleAdditionsAreReported) {
  ElabFixture second;
  ElabOk(std::string(kAbcExampleHead) +
             "  assign abc.C = sel ? 8'hDE : 8'hED;\n"
             "endmodule\n",
         second);
  EXPECT_TRUE(ReportedError(
      second.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'abc.C'", 13,
      "6.5"));
  ElabFixture mixed;
  ElabOk(std::string(kAbcExampleHead) +
             "  always @(posedge clk) abc.A[7:3] <= !abc.B[7:3];\n"
             "endmodule\n",
         mixed);
  EXPECT_TRUE(ReportedError(mixed.diag.Diagnostics(),
                            "element 'abc.A[3]' has both a continuous "
                            "assignment and a procedural assignment",
                            8, "10.3.2"));
  EXPECT_FALSE(ReportedError(mixed.diag.Diagnostics(),
                             "element 'abc.A[2]' has both a continuous "
                             "assignment and a procedural assignment",
                             8, "10.3.2"));
}

constexpr const char* kInverterUdp =
    "primitive inv(output o, input i);\n"
    "  table\n"
    "    0 : 1;\n"
    "    1 : 0;\n"
    "  endtable\n"
    "endprimitive\n";

// A UDP's output terminal writes a variable as a gate's does. The UDP is a
// continuous writer whether it drives the whole variable or one bit of it, so
// a procedural write to the same terms, or a second primitive output on them,
// is reported. A procedural write to another bit is accepted.
TEST(NetsAndVariables, UdpOutputIsAContinuousWriterOfAVariable) {
  ElabFixture whole;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a, w;\n"
             "  inv u(w, a);\n"
             "  initial w = 1'b0;\n"
             "endmodule\n",
         whole);
  EXPECT_TRUE(ReportedError(whole.diag.Diagnostics(),
                            "variable 'w' has both continuous and procedural "
                            "assignments",
                            9, "6.5"));
  ElabFixture twice;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a, w;\n"
             "  inv u1(w, a);\n"
             "  inv u2(w, a);\n"
             "endmodule\n",
         twice);
  EXPECT_TRUE(ReportedError(twice.diag.Diagnostics(),
                            "variable 'w' is driven by more than one "
                            "continuous assignment or primitive output",
                            10, "10.3.2"));
  ElabFixture bit;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a;\n"
             "  logic [1:0] v;\n"
             "  inv u(v[0], a);\n"
             "  initial v[0] = 1'b0;\n"
             "endmodule\n",
         bit);
  EXPECT_TRUE(ReportedError(bit.diag.Diagnostics(),
                            "element 'v[0]' has both a continuous assignment "
                            "and a procedural assignment",
                            10, "10.3.2"));
  EXPECT_TRUE(ElabOk(std::string(kInverterUdp) + "module m;\n"
                                                 "  logic a;\n"
                                                 "  logic [1:0] v;\n"
                                                 "  inv u(v[0], a);\n"
                                                 "  initial v[1] = 1'b0;\n"
                                                 "endmodule\n"));
}

// §6.5 counts a procedural assign statement (§10.6.1) as a procedural
// assignment. Beside a continuous assignment to the same variable it is
// reported, whether it stands in an initial procedure, in a generate block or
// in a task, and whether the continuous assignment writes the whole variable
// or a member of it. Standing alone it is accepted.
TEST(NetsAndVariables, ProceduralAssignIsAProceduralWriter) {
  ElabFixture module_level;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  initial assign v = a;\n"
      "  assign v = b;\n"
      "endmodule\n",
      module_level);
  EXPECT_TRUE(ReportedError(module_level.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            4, "6.5"));
  ElabFixture generated;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  assign v = b;\n"
      "  if (1) begin : g\n"
      "    initial assign v = a;\n"
      "  end\n"
      "endmodule\n",
      generated);
  EXPECT_TRUE(ReportedError(generated.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
  ElabFixture in_task;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  task t;\n"
      "    assign v = a;\n"
      "  endtask\n"
      "  assign v = b;\n"
      "endmodule\n",
      in_task);
  EXPECT_TRUE(ReportedError(in_task.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            6, "6.5"));
  ElabFixture member;
  ElabOk(
      "module m;\n"
      "  struct packed { logic p; logic q; } s;\n"
      "  assign s.p = 1'b0;\n"
      "  initial assign s = 2'b00;\n"
      "endmodule\n",
      member);
  EXPECT_TRUE(ReportedError(member.diag.Diagnostics(),
                            "element 's.p' has both a continuous assignment "
                            "and a procedural assignment",
                            3, "10.3.2"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, v;\n"
             "  initial assign v = a;\n"
             "endmodule\n"));
}

// §6.5 makes a force statement neither a continuous nor a procedural
// assignment, so it adds no writer: beside one continuous assignment, beside
// one to a bit of the variable, and beside procedural writes, it is accepted.
TEST(NetsAndVariables, ForceIsNoWriterUnderTheRule) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, v;\n"
             "  assign v = b;\n"
             "  initial force v = a;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic b;\n"
             "  logic [1:0] v;\n"
             "  assign v[0] = b;\n"
             "  initial force v = 2'b00;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, v;\n"
             "  initial begin\n"
             "    v = 1'b0;\n"
             "    assign v = a;\n"
             "    force v = a;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
