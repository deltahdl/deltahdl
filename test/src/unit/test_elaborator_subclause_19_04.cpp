#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.4: an embedded covergroup is instantiated by assigning the result of
// new() to its identifier inside the enclosing class's new() method. Doing so
// there is the sanctioned instantiation site and shall elaborate cleanly.
TEST(EmbeddedCovergroup, AssignInNewMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: an embedded covergroup may take a formal-argument list, and an
// argument may be used within the covergroup, for example to initialize a
// coverage option (the C1 example). Declaring such a parameterized covergroup
// and instantiating it in the constructor is the sanctioned form and shall
// elaborate cleanly rather than be rejected for carrying arguments.
TEST(EmbeddedCovergroup, ParameterizedInstantiatedInNewOk) {
  EXPECT_TRUE(
      ElabOk("class C1;\n"
             "  bit [7:0] x;\n"
             "  bit clk;\n"
             "  covergroup cv (int arg) @(posedge clk);\n"
             "    option.at_least = arg;\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cv = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: the covergroup variable shall not be assigned outside the new()
// method of its parent class. An assignment from any other method is an error.
TEST(EmbeddedCovergroup, AssignOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void build();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

// §19.4: the prohibition covers any assignment, not just a new() construction,
// and applies even when the assignment is nested inside control flow within a
// non-constructor method.
TEST(EmbeddedCovergroup, NestedAssignOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    if (en) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

// §19.4: leaving the covergroup uninstantiated (no assignment anywhere) is
// legal; the standard simply says no data will be sampled in that case.
TEST(EmbeddedCovergroup, NoInstantiationOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.4: the restriction to the new() method holds even when the class does
// have a constructor that legally instantiates the covergroup. A second method
// that reassigns the same covergroup variable is still an error; the presence
// of a valid instantiation site does not license assignments elsewhere.
TEST(EmbeddedCovergroup, AssignInSecondMethodAlongsideNewError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function new();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "  function void reconfig();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  // Line 10 is the assignment in reconfig(); the one on line 7 is inside new()
  // and is the sanctioned instantiation, so no report stands there.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            10, "19.4"));
}

// §19.4: an assignment to the covergroup variable is forbidden outside new()
// wherever it appears, including buried inside a loop body of another method.
TEST(EmbeddedCovergroup, AssignInLoopOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void setup();\n"
      "    for (int i = 0; i < 2; i = i + 1) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

// §19.4: the assign-outside-new() prohibition applies in the else arm of a
// conditional too, not only the then arm. An assignment reached only through
// the else branch of a non-constructor method is still an error.
TEST(EmbeddedCovergroup, AssignInElseBranchOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    if (en) x = 0; else cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

// §19.4: the prohibition also covers an assignment buried in the body of a
// while loop of a non-constructor method.
TEST(EmbeddedCovergroup, AssignInWhileLoopOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void setup();\n"
      "    while (en) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

// §19.4: an assignment inside a case item of a non-constructor method is
// forbidden as well; the rule reaches every branch of the method body.
TEST(EmbeddedCovergroup, AssignInCaseItemOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  int mode;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    case (mode)\n"
      "      0: cg = new;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            9, "19.4"));
}

// §19.4: the covergroup instance variable is the same whether referenced bare
// or through an explicit object handle, so assigning it via `this.cg` outside
// the constructor is just as forbidden as the bare `cg` form.
TEST(EmbeddedCovergroup, AssignViaThisHandleOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    this.cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

// §19.4: an embedded covergroup may build a coverage model over protected and
// local class properties without weakening data encapsulation, and class
// members may appear both in coverpoint expressions and as conditional guards.
// Naming a local property in a coverpoint and a protected property in an iff
// guard must elaborate cleanly rather than be rejected as an access violation.
TEST(EmbeddedCovergroup, CoversLocalAndProtectedPropertiesOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local int x;\n"
             "  protected bit en;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x iff (en);\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// The five cases below cover the links CheckCovergroupAssignStmt in
// src/elaborator/elaborator_validate_class_members.cpp gained when its
// hand-written recursion list was replaced by ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. §19.4 names no statement the
// assignment is permitted in outside new(), so each is a rejection, and each
// report stands at the assignment itself rather than at the statement
// enclosing it.
//
// Stmt::for_inits and Stmt::for_steps take no case, and that is a fact about
// A.6.2 rather than a gap. A covergroup is instantiated by the class_new
// alternative of `blocking_assignment ::= ... hierarchical_variable_identifier
// select = class_new`, and neither `for_initialization`'s
// `variable_assignment ::= variable_lvalue = expression` nor `for_step_
// assignment`'s `operator_assignment` admits a class_new on the right-hand
// side (A.6.8), so no conforming source writes `cg = new` in a for header.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser puts in Stmt::fork_stmts. §13.4.4 admits the
// fork-join_none form inside a function.
TEST(EmbeddedCovergroup, AssignInAForkArmOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    fork\n"
      "      cg = new;\n"
      "    join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(EmbeddedCovergroup, AssignInAnAssertionPassStmtOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    assert (1) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}
TEST(EmbeddedCovergroup, AssignInAnAssertionFailStmtOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    assert (1) else cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §19.4 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(EmbeddedCovergroup, AssignInARandcaseItemOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    randcase\n"
      "      1 : cg = new;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, reached through Stmt::rs_productions and through no other member of
// Stmt.
TEST(EmbeddedCovergroup, AssignInARandsequenceCodeBlockOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    randsequence(main)\n"
      "      main : { cg = new; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

}  // namespace
