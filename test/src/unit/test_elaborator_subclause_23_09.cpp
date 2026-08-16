#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.9: an identifier shall be used to declare only one item within a
// scope. Two nets sharing a name in the same module scope is illegal.
TEST(ScopeRulesElaboration, DuplicateIdentifierInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "23.9"));
}

// §23.9: the same rule applies to the construct the LRM names first — two
// variable declarations sharing a name in one scope. This exercises the
// variable declaration form rather than the net form above.
TEST(ScopeRulesElaboration, DuplicateVariableDeclarationInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int x;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "23.9"));
}

// §23.9 also forbids naming a task the same as a variable in the same
// module scope; the two declarations collide on one identifier.
TEST(ScopeRulesElaboration, TaskNameMatchingVariableRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic foo;\n"
      "  task foo;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'foo'", 3, "23.9"));
}

// §23.9 spells out one form of that collision explicitly: a gate instance
// shall not share the name of the net connected to its output.
TEST(ScopeRulesElaboration, GateInstanceNameMatchingOutputNetRejected) {
  ElabFixture f;
  // CheckGateInstNameDiagnostics files this clash under its own report rather
  // than the redeclaration one: `g1` names the output terminal, which is an
  // implicit net the gate item itself creates, so the name is never entered
  // into declared_names_ twice.
  ElabOk(
      "module m;\n"
      "  wire a, b;\n"
      "  and g1(g1, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate instance name 'g1' conflicts with its "
                            "output net",
                            3, "23.9"));
}

// §23.9: each module opens a new scope, so the same identifier may name an
// item in two different modules without colliding.
TEST(ScopeRulesElaboration, SameNameInSeparateModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire x;\n"
             "endmodule\n"
             "module top;\n"
             "  wire x;\n"
             "  child c();\n"
             "endmodule\n"));
}

// §23.9: a package is another of the listed constructs that opens its own
// scope, so a name declared in a package does not collide with a like-named
// declaration in a module. Covers a scope-creating construct kind other than
// the module-vs-module case above.
TEST(ScopeRulesElaboration, SameNameInPackageAndModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, ConditionalGenerateBlocksAllowSameIdentifier) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter P = 1;\n"
             "  if (P == 1) begin : g\n"
             "    logic data;\n"
             "  end else begin : g\n"
             "    logic data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DirectVariableReferenceStopsAtModuleBoundary) {
  ElabFixture f;
  // The upward search inside `child` never reaches `parent`, so the write is
  // reported as naming nothing rather than as reaching the enclosing module's
  // variable.
  ElabOk(
      "module child;\n"
      "  initial outer_x = 1;\n"
      "endmodule\n"
      "module parent;\n"
      "  logic outer_x;\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'outer_x'", 2, "23.9"));
}

TEST(ScopeRulesElaboration, InstanceNamePrecedenceOverModuleTypeName) {
  EXPECT_TRUE(
      ElabOk("module foo;\n"
             "  integer x;\n"
             "endmodule\n"
             "module top;\n"
             "  foo foo();\n"
             "  initial foo.x = 5;\n"
             "endmodule\n"));
}

// §23.9: a name referenced directly inside a named block that is not declared
// locally triggers an upward search, which continues until the item is found in
// an enclosing scope. Here the write inside block b resolves upward to the
// module-level net, so elaboration succeeds. This is the accepting counterpart
// of DirectVariableReferenceStopsAtModuleBoundary.
TEST(ScopeRulesElaboration, DirectReferenceResolvesUpwardToEnclosingScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic sig;\n"
             "  initial begin : b\n"
             "    sig = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.9: a named begin-end block is one of the elements that occupies the
// enclosing scope's namespace, so two blocks sharing a name in the same scope
// declare one identifier twice and are illegal. This is the general rule whose
// only exception is the conditional-generate case tested above.
TEST(ScopeRulesElaboration, DuplicateNamedBlockLabelsInSameScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin : b\n"
      "  end\n"
      "  initial begin : b\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'b'", 4, "23.9"));
}

// §23.9: the report that rejects a name declared twice in one scope names the
// subclause stating the rule, so a caller learns which rule was enforced
// without matching the wording of the message.
TEST(ScopeRulesElaboration, DuplicateIdentifierNames23_9) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "23.9"));
}

// §23.9 lists "Functions" among the constructs that define a scope, and an
// identifier shall be used to declare only one item within a scope, so a local
// may not be redeclared by another local in the same function body.
TEST(ScopeRulesElaboration, FunctionBodyDuplicateLocalError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int f();\n"
      "    int x;\n"
      "    int x;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
}

// §23.9 lists "Tasks" beside "Functions", so a task body is a scope on the
// same terms and rejects a redeclared local the same way.
TEST(ScopeRulesElaboration, TaskBodyDuplicateLocalError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task t();\n"
      "    int y;\n"
      "    int y;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'y'", 4, "23.9"));
}

// §23.9 states one rule for every construct it lists as defining a scope, so
// the two reports a run makes for it must name one subclause. This source
// breaks the rule twice in one module: `fn_dup` is declared twice directly
// inside a function body, which CheckBlockDeclDups in
// src/elaborator/elaborator_validate_funcbody.cpp reports, and `blk_dup` is
// declared twice directly inside an initial begin-end block, which
// CheckOneBlockLocals in src/elaborator/elaborator_scope_rules.cpp reports.
// One elaboration runs both walks, so this case fails when the two sites
// disagree about which subclause the rule is; a case holding one shape alone
// reads its own site and cannot see the disagreement.
TEST(ScopeRulesElaboration,
     DuplicateLocalReportsOneSubclauseWhereverTheBlockSits) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int fn();\n"
      "    int fn_dup;\n"
      "    int fn_dup;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int blk_dup;\n"
      "    int blk_dup;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'fn_dup'",
                            4, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'blk_dup'",
                            9, "23.9"));
}

// §23.9 lists "fork-join blocks (named or unnamed)" beside "begin-end blocks
// (named or unnamed)" among the elements that define a new scope, and an
// identifier shall be used to declare only one item within a scope, so two
// variables sharing a name directly inside one fork are illegal. This case
// fails while CheckOneBlockLocals in
// src/elaborator/elaborator_scope_rules.cpp is reached only for a
// StmtKind::kBlock node, because Parser::ParseForkStmt puts a declaration
// written inside a fork into Stmt::fork_stmts on a StmtKind::kFork node, which
// that guard never compares against itself.
//
// One source covers all three closing keywords. Parser::ParseForkStmt at
// src/parser/parser_stmt.cpp:644 records the closing keyword in
// Stmt::join_kind and pushes the declarations into Stmt::fork_stmts whether
// join, join_any or join_none closes the block, so the three shapes differ in
// Stmt::join_kind alone and a case per keyword would hand the walk one input
// three times.
TEST(ScopeRulesElaboration, DuplicateLocalInForkJoinError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial fork\n"
      "    int x;\n"
      "    int x;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
}

// §23.9 makes a fork-join block a scope wherever it is written, so the same
// duplicate inside a function body is illegal for the same reason. A second
// case is needed because a second walk reads this shape:
// CheckSubroutineBodyRedeclarations in
// src/elaborator/elaborator_validate_funcbody.cpp checks a function body and
// CheckBlockLocalRedeclarations in src/elaborator/elaborator_scope_rules.cpp
// checks an initial procedure, and each carried its own StmtKind::kBlock guard,
// so repairing one leaves the other silent. This case fails when
// CheckBlockDeclDups is called on Stmt::stmts alone and never on
// Stmt::fork_stmts.
//
// The fork is closed by join_none rather than join because §13.4 rule a) lists
// fork-join among the time-controlling statements a function shall not contain,
// which src/elaborator/elaborator_validate_funcbody.cpp reports as "only
// fork/join_none is permitted inside a function" under §13.4. Closing with join
// here would break a second rule in the source and leave the case asserting on
// one of two reports.
TEST(ScopeRulesElaboration, DuplicateLocalInForkJoinInsideFunctionError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function int fn();\n"
      "    fork\n"
      "      int x;\n"
      "      int x;\n"
      "    join_none\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 5, "23.9"));
}

// §23.9 makes the fork-join block a new scope of its own, so a name declared in
// the fork and in the begin-end block enclosing it declares one item in each of
// two scopes and is legal shadowing. This case fails when the fork's
// declarations are compared against the enclosing block's set instead of
// against a set of their own, which is the shape a repair to
// CheckOneBlockLocals in src/elaborator/elaborator_scope_rules.cpp reaches for
// by merging Stmt::fork_stmts into the list it walks.
TEST(ScopeRulesElaboration, SameLocalNameInForkAndEnclosingBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    int x;\n"
             "    fork\n"
             "      int x;\n"
             "    join\n"
             "  end\n"
             "endmodule\n"));
}

// §23.9: "if the item is a variable, it shall stop at a module boundary". `v`
// is declared in `top` and read in `child`, so the upward search from `child`
// ends at the module boundary and the read names nothing. The elaborator is
// silent on this shape today because the collector that gathers bare reads
// takes a single identifier standing alone as the whole right-hand side, and
// here `v` sits inside the larger expression `v + 0`.
TEST(ScopeRulesElaboration,
     DirectVariableReadInExpressionStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    r = v + 0;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            4, "23.9"));
}

// §23.9: "if the item is a variable, it shall stop at a module boundary". The
// read is the initializer of a module-item declaration rather than a statement,
// and `v` is declared only in `top`, so the search from `child` stops at the
// boundary. The elaborator is silent on this shape today because a declaration
// initializer is visited by no collector: the walk gathers reads from
// statements and never descends into the expression a declaration carries.
TEST(ScopeRulesElaboration,
     DirectVariableReadInDeclarationInitializerStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  int q = v;\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            2, "23.9"));
}

// §23.9: "if the item is a variable, it shall stop at a module boundary". The
// rule holds for a read written in a task body as much as for one written in an
// initial procedure, since the boundary the search stops at is the module's and
// not the statement's. The elaborator is silent on this shape today because a
// task body is a context the module-item walk does not enter: it reaches the
// task's declaration and stops there rather than walking the statements inside.
TEST(ScopeRulesElaboration, DirectVariableReadInTaskBodyStopsAtModuleBoundary) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  task t();\n"
      "    r = v;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            4, "23.9"));
}

// §23.9: "if the item is a variable, it shall stop at a module boundary". The
// read stands in an initial procedure written directly in `child`, beside a for
// generate construct that has nothing to do with it, and `v` is declared only
// in `top`. The elaborator is silent on this shape today because a module
// holding a generate construct is skipped whole: the presence of the generate
// item takes the whole module out of the walk, so the reads written outside it
// are never collected either.
TEST(ScopeRulesElaboration,
     DirectVariableReadStopsAtModuleBoundaryInModuleHoldingGenerateFor) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  integer r;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    wire w;\n"
      "  end\n"
      "  initial r = v;\n"
      "endmodule\n"
      "module top;\n"
      "  integer v;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'v'",
                            7, "23.9"));
}

// §23.9 stops the upward search for a variable at the module boundary, and a
// name a wildcard import supplies is not reached by that search at all: §26.3
// makes `pv` a candidate for the bare name in `m` without `pv` being declared
// in any scope the search walks. This holds the widening honest on the import
// half, where a collector that reports every bare name it cannot find in an
// enclosing scope would reject a legal source.
TEST(ScopeRulesElaboration, BareNameSuppliedByAWildcardImportIsStillAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int pv;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  integer r;\n"
             "  initial begin\n"
             "    r = pv + 0;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.9 stops the upward search at the module boundary, not below it: a
// generate block is a scope inside the module, so a name declared there is
// found by a search starting inside that block and `r` is found by continuing
// upward to the module. This holds the widening honest on the generate half,
// where a collector that reads a module's declarations alone would take `gv`
// for a name nothing declares.
TEST(ScopeRulesElaboration, BareNameDeclaredInAGenerateBlockIsStillAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  integer r;\n"
             "  genvar i;\n"
             "  for (i = 0; i < 2; i = i + 1) begin : g\n"
             "    integer gv;\n"
             "    initial begin\n"
             "      r = gv + 0;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
