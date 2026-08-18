#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §27.4, printed page 821: "It shall be an error if the name of a generate
// block instance array conflicts with any other declaration, including any
// other generate block instance array." The two cases below ask that of a
// module-level declaration that is neither a net, a variable nor a port, and
// they differ in that declaration alone, so the source and the report are
// stated once here and each case supplies the one line that changes.
//
// `module_level_decl` is written at line 4 of the source, so the `for` whose
// array name collides always stands at line 6 and the report always stands
// there. `module child;` is declared for the instance case to instantiate and
// left uninstantiated by the others.
//
// Elaborator::RegisterGenerateForArrayName in
// src/elaborator/elaborator_generate.cpp is the emission site: it formats
// "generate block array '{}' conflicts with an existing declaration in the
// same scope" and passes Subclause("23.9").
void ExpectLoopArrayNameConflictsWith(const std::string& module_level_decl) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  " +
          module_level_decl +
          "\n"
          "  genvar i;\n"
          "  for (i = 0; i < 2; i = i + 1) begin : a\n"
          "    wire w;\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            6, "23.9"));
}

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
// One source covers all three closing keywords. Parser::ParseForkStmt in
// src/parser/parser_stmt.cpp records the closing keyword in
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

// §23.9 lists "Generate blocks" among "the following elements define a new
// scope in SystemVerilog", and rules that "An identifier shall be used to
// declare only one item within a scope". Each module opens its own scope, so a
// generate block in one module and a generate block in another declare their
// names in two scopes that share nothing, and the same name in both is legal.
//
// A generate construct is not elaborated where it is written:
// Elaborator::ElaborateItems queues it into pending_generates_ and
// Elaborator::ResolveDefparamsAndGenerates drains every module's queue together
// once every module has been elaborated. This case fails while the set that
// judges a declaration belongs to the design rather than to a module, because
// module `b`'s `w` then finds module `a`'s entry still there and is reported as
// a redeclaration of a net in a module that is not its own.
TEST(ScopeRulesElaboration,
     GenerateBlockDeclarationNamesDoNotCollideAcrossModules) {
  EXPECT_TRUE(
      ElabOk("module a;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module b;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module top;\n"
             "  a u_a();\n"
             "  b u_b();\n"
             "endmodule\n"));
}

// §23.9 gives each instance of a generate block its own scope, so one module
// instantiated twice declares its generate block's names once per instance
// rather than twice in one scope.
//
// This is the same rule as the case above reached without a second module.
// Elaborator::ElaborateModuleInst calls Elaborator::ElaborateModule once per
// instance and each call queues that module's generate constructs again, so a
// design-wide set is offered `g` and `w` twice and rejects the second
// instantiation. Elaborator::ElaborateModule builds a fresh RtlirModule per
// call, which is what tells the two instances' name sets apart.
TEST(ScopeRulesElaboration,
     RepeatedInstantiationDoesNotRedeclareGenerateBlockNames) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  if (1) begin : g\n"
             "    wire w;\n"
             "  end\n"
             "endmodule\n"
             "module top;\n"
             "  child u1();\n"
             "  child u2();\n"
             "endmodule\n"));
}

// §27.4, printed page 821, rules that "It shall be an error if the name of a
// generate block instance array conflicts with any other declaration". A module
// instance name is such a declaration, and `a` names both the instance of
// `child` and the loop generate block array.
//
// Elaborator::ElaborateModuleInst records an instance name in declared_names_
// and nowhere else: IsNameDeclared in src/elaborator/elaborator_items.cpp reads
// RtlirModule::variables, RtlirModule::nets and RtlirModule::ports, and an
// instance is in none of them. This case is therefore silent while the generate
// construct runs after ItemElaborationStateSaver::Restore has taken the
// module's own declarations back out of the set, and it is the half of the
// defect that loses a report rather than the half that invents one.
TEST(ScopeRulesElaboration,
     GenerateBlockArrayNameConflictingWithAnInstanceNameErrors) {
  ExpectLoopArrayNameConflictsWith("child a();");
}

// §27.4 makes the same conflict an error against a function name, which is a
// declaration of the enclosing module like any other.
//
// A second case is needed because CheckFunctionDeclDiagnostics in
// src/elaborator/elaborator_items.cpp is a different insertion site from
// Elaborator::ElaborateModuleInst, and it is the one that keeps a fix from
// being written against module instances alone. A function name reaches
// declared_names_ and nothing IsNameDeclared reads, so it is invisible to the
// array-name check for exactly the reason the instance name is.
TEST(ScopeRulesElaboration,
     GenerateBlockArrayNameConflictingWithAFunctionNameErrors) {
  ExpectLoopArrayNameConflictsWith("function void a(); endfunction");
}

// §27.4, printed page 821: a generate block "comprises a separate scope and a
// new level of hierarchy when it is instantiated", so an item written once in
// a loop generate body is elaborated once per iteration into a different scope
// each time and declares its name afresh rather than a second time in one
// scope. §23.9 forbids only a second declaration within one scope, so the three
// cases below are conforming sources and shall elaborate.
//
// The three differ in the item the loop body holds and in nothing else, because
// three separate functions in src/elaborator/elaborator_items.cpp record the
// name -- CheckGateInstNameDiagnostics, CheckUdpInstNameDiagnostics and
// CheckFunctionDeclDiagnostics -- and a fix reaching one leaves the others
// rejecting a legal source. So the module and the loop are stated once here and
// each case supplies the item and whatever declaration the item needs ahead of
// the module.
//
// The genvar runs 4 to 5 rather than 0 to 1 so that its value is never the
// ordinal of the block instance the iteration creates, which are 0 and 1. An
// index that equalled the ordinal would make a body keyed by the ordinal and a
// body keyed by the genvar value produce the same key, and the case would pass
// whichever the elaborator used.
void ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
    const std::string& prelude, const std::string& loop_body_item) {
  EXPECT_TRUE(ElabOk(prelude +
                     "module m;\n"
                     "  logic [7:0] d;\n"
                     "  wire [7:0] y;\n"
                     "  genvar i;\n"
                     "  for (i = 4; i < 6; i = i + 1) begin : b\n"
                     "    " +
                     loop_body_item +
                     "\n"
                     "  end\n"
                     "endmodule\n"));
}

// The gate instance form, which reaches CheckGateInstNameDiagnostics.
TEST(ScopeRulesElaboration, LoopGenerateGateInstanceNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "", "and g (y[i], d[i], d[i]);");
}

// The UDP instance form, which reaches CheckUdpInstNameDiagnostics rather than
// the gate one because Parser::ParseUdpInstList is taken for an instance whose
// type name the parser has already seen declared as a primitive. This is the
// shape test/src/e2e/udp_generate.sv is written in, which is the real source
// the bare-name record rejects.
TEST(ScopeRulesElaboration, LoopGenerateUdpInstanceNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "primitive udp_inv (y, a);\n"
      "  output y;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1 ;\n"
      "    1 : 0 ;\n"
      "  endtable\n"
      "endprimitive\n",
      "udp_inv g (y[i], d[i]);");
}

// The function declaration form, which reaches CheckFunctionDeclDiagnostics.
TEST(ScopeRulesElaboration, LoopGenerateFunctionNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration(
      "", "function int fn(); return 0; endfunction");
}

// The task form. Elaborator::ElaborateItem sends kTaskDecl to the same
// CheckFunctionDeclDiagnostics as kFunctionDecl, by falling through one case
// label to the next, so this reaches the same record the case above does. It is
// written anyway: the two kinds share that code only for as long as the
// fallthrough stands, and nothing else would report splitting them.
TEST(ScopeRulesElaboration, LoopGenerateTaskNameRepeatsPerIteration) {
  ExpectLoopBodyItemDeclaresItsNameOncePerIteration("", "task tk(); endtask");
}

// §23.9 still rules that "An identifier shall be used to declare only one item
// within a scope", so two gate instances sharing a name directly in one module
// scope are illegal however a name inside a generate block is keyed. This case
// is what a fix that deleted the check rather than scoping its key would break.
//
// src/elaborator/elaborator_items.cpp is the emission site:
// CheckGateInstNameDiagnostics formats "redeclaration of '{}'" from
// ModuleItem::gate_inst_name and passes Subclause("23.9").
TEST(ScopeRulesElaboration, DuplicateGateInstanceNamesInOneScopeRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire a, b, o1, o2;\n"
      "  and g (o1, a, b);\n"
      "  and g (o2, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'g'", 4, "23.9"));
}

// The width of the one net of `mod` whose name is `name`, and 0 when no net or
// more than one carries it. The four cases below each declare a net whose
// packed range is written over a parameter, and read the width back to say
// which parameter the range folded against: a range that did not fold leaves
// the 1-bit base-type width §6.10 gives a scalar net.
uint32_t WidthOfNetNamed(const RtlirModule* mod, std::string_view name) {
  const RtlirNet* found = nullptr;
  for (const auto& net : mod->nets) {
    if (net.name != name) continue;
    if (found != nullptr) return 0;
    found = &net;
  }
  return found == nullptr ? 0 : found->width;
}

// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// and rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree". Block 'a' is not higher in the module's own branch,
// so the W its localparam declares is not what the module-level range names,
// and `wire [W-1:0] w;` sizes to the 1 bit a scalar net gets.
//
// The test fails when the net is 4 bits wide. Elaborator::BuildParamScope in
// src/elaborator/elaborator_items_scope.cpp keys the ScopeMap every constant
// expression in the module folds against by RtlirParamDecl::name, which
// Elaborator::ElaborateParamDecl writes bare whatever scope declared the
// parameter, so block 'a''s W is entered under "W" and answers a range written
// anywhere in the module.
TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInAModuleLevelExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "  endgenerate\n"
      "  wire [W-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "w"), 1U)
      << "block 'a' localparam W should not size a module-level net";
}

// The same reading where the range stands in a sibling generate block. Blocks
// 'a' and 'c' are siblings, so neither is "higher in the same branch of the
// name tree" than the other and block 'a''s W is not what block 'c''s range
// names. Neither block is at module level, so the case cannot pass by
// Elaborator::ScopedName being the identity.
TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInASiblingBlockExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "    if (1) begin : c\n"
      "      wire [W-1:0] w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "c_w"), 1U)
      << "block 'a' localparam W should not size a sibling block's net";
}

// §11.2.1 makes a parameter a constant expression, and §23.9 rules that an
// identifier declared "locally" is what a direct reference names, so block
// 'a''s own W sizes a range written in block 'a'. The net is 4 bits wide.
//
// This is one of the two cases a fix must not lose: a scope that dropped every
// parameter carrying a generate block prefix would stop a block's parameter
// folding inside the block that declared it.
TEST(GenerateBlockScope, ParameterOfAGenerateBlockStillFoldsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "block 'a' localparam W should size a net in block 'a'";
}

// §23.9 rules that the search for a directly referenced identifier "shall
// continue upward until an item by that name is found or until a module,
// interface, program, or checker boundary is encountered", so a parameter of
// the module is found from inside every generate block in it. The net is 4 bits
// wide.
//
// This is the other case a fix must not lose, and it is the direction the
// defect does not run in: a module's parameter was always visible in a block,
// and a scope built for a block has to keep it so.
TEST(GenerateBlockScope, ParameterOfTheModuleStillFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter W = 4;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "the module's parameter W should size a net in block 'a'";
}

// The parameter of the one child instance of `mod`, which every case below
// reads to see what a defparam wrote into it.
const RtlirParamDecl* OnlyChildParam(const RtlirModule* mod) {
  if (mod->children.size() != 1) return nullptr;
  const RtlirModule* child = mod->children[0].resolved;
  if (child == nullptr || child->params.size() != 1) return nullptr;
  return &child->params[0];
}

// §23.9 puts a generate block's declarations in a scope of their own, so the
// string parameter block 'a' declares is not what a defparam written among the
// module's own items names, and c.S keeps the default the child declared.
//
// A defparam is what reaches this reader. Elaborator::ApplyDefparams opens a
// ParamRangeRegistryGuard (src/elaborator/elaborator_defparam.cpp:343), and
// Elaborator::ResolveDefparamsAndGenerates (src/elaborator/elaborator.cpp:510)
// tests its break before processing a batch of pending generates, so defparams
// are applied once more after block 'a''s parameter is in RtlirModule::params.
// ConstEvalString sends a bare identifier straight to StringParamChars
// (src/elaborator/const_eval.cpp:559) with no ScopeMap in between, which is why
// the scope Elaborator::BuildParamScope builds does not stand in the way here.
//
// The test fails when c.S holds "abcd".
TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockIsNotReadByAModuleLevelDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "  endgenerate\n"
      "  defparam c.S = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_NE(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should not reach a module-level defparam";
}

// The direction the scope test must not lose. §23.9 has an identifier "declared
// locally" name the local item, so a defparam written inside block 'a' does
// name block 'a''s P, and c.S takes its characters.
TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockStillReadsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "      defparam c.S = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should reach a defparam in block 'a'";
}

// The same rule at the other reader the registry answers. §6.16.1 gives
// `function int len()`, which ConstEvalBuiltinMethodFull folds through
// StringParamLength (src/elaborator/const_eval_builtin_method.cpp:148) by
// reading RtlirParamDecl::resolved_string off the registered module, again with
// no ScopeMap in between. Block 'a''s P is four characters, so the test fails
// when c.N holds 4.
TEST(GenerateBlockScope,
     LengthOfAGenerateBlockStringParameterIsNotReadByAModuleLevelDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter N = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "  endgenerate\n"
      "  defparam c.N = P.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->resolved_value, 4)
      << "block 'a' localparam P should not give its length to a module-level "
         "defparam";
}

}  // namespace
