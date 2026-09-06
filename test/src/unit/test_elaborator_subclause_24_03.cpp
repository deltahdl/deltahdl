#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

static RtlirDesign* ElaborateSource(const std::string& src,
                                    ProgramElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

namespace {

TEST(ProgramElab, ElaborateProgramWithPorts) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_ports(input logic clk, input logic rst);\n"
      "endprogram\n",
      f, "prog_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(ProgramElab, ElaborateProgramWithInitialBlock) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_init;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n",
      f, "prog_init");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_FALSE(mod->processes.empty());
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

TEST(ProgramConstruct, ProgramWithDataAndInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    status = 1;\n"
      "  end\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ProgramWithSubroutinesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task do_work;\n"
      "  endtask\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ProgramWithClassElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  class my_trans;\n"
      "    int data;\n"
      "  endclass\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, EmptyProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, NestedProgramInModuleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    initial $display(\"nested\");\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, TwoNestedProgramsShareOuterVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int shared;\n"
      "  program p1;\n"
      "    initial shared = 1;\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial shared = 2;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, TopLevelPortlessProgramImplicitlyInstantiated) {
  ProgramElabFixture f;
  auto* design = ElaborateSource("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->name, "p");
}

TEST(ProgramConstruct, ReferencingProgramSignalFromOutsideIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int psig;\n"
      "  endprogram\n"
      "  initial begin\n"
      "    p.psig = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

// §24.3: nets declared in a program are program signals, exactly as program
// variables are, so a hierarchical reference to a program net from outside the
// program is an error too. The sibling test above uses a program variable; this
// covers the net input form, read through a continuous assignment in the
// enclosing module.
TEST(ProgramConstruct, ReferencingProgramNetFromOutsideIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire w;\n"
      "  program p;\n"
      "    wire pnet;\n"
      "  endprogram\n"
      "  assign w = p.pnet;\n"
      "endmodule\n",
      f, "top");
  // The continuous-assign branch reports at the item's own location, which is
  // the `assign` keyword on line 6.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

TEST(ProgramConstruct, ImplicitlyInstantiatedNestedProgramReusesDeclName) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "module top;\n"
      "  program p;\n"
      "    initial $display(\"hi\");\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  const auto* top = design->top_modules[0];
  // §24.3: a portless nested program that is not explicitly instantiated is
  // implicitly instantiated exactly once, and the implicit instance reuses the
  // declaration name. Counting the matching children observes the "once" part
  // of the rule, not just that some instance exists.
  int instances = 0;
  for (const auto& child : top->children) {
    if (child.module_name == "p") {
      EXPECT_EQ(child.inst_name, child.module_name);
      ++instances;
    }
  }
  EXPECT_EQ(instances, 1);
}

TEST(ProgramConstruct, HierRefBetweenProgramsIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program src;\n"
      "    int sig;\n"
      "  endprogram\n"
      "  program dst;\n"
      "    initial src.sig = 1;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AnonymousProgramHierRefToProgramIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "program;\n"
      "  task t;\n"
      "    prog.psig = 1;\n"
      "  endtask\n"
      "endprogram\n",
      f, "prog");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

// §24.3 closes its account of hierarchical references with "However, anonymous
// programs shall not contain hierarchical references to other program scopes",
// and puts no condition on where the anonymous program itself stands. §24.6
// says where it may stand -- "anonymous programs can be used inside packages
// (see Clause 26) or compilation-unit scopes (see 3.12.1)" -- and A.1.11 makes
// anonymous_program a package_item, so the two placements are one rule.
// AnonymousProgramHierRefToProgramIsError above writes the reference at
// compilation-unit scope; the two cases below write the same reference in a
// package, whose items Parser::TryParsePackageBodyItem puts into
// PackageDecl::items rather than into CompilationUnit::cu_items.
constexpr std::string_view kProgramSignalFromOutside =
    "hierarchical reference to program signal from outside the program is not "
    "permitted";

// A package whose anonymous program holds `subroutine`, which writes the signal
// of the named program `prog` declared above the package. A named program is
// required: with no name in CompilationUnit::programs the check has no program
// to match a reference against and answers nothing. `subroutine` is three lines
// -- its header, the assignment, and its end keyword -- so the assignment is
// line 7 of the source whichever subroutine kind is passed.
void ExpectPackageAnonymousProgramHierRefRejected(
    const std::string& subroutine) {
  ElabFixture f;
  ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "package pkg;\n"
      "  program;\n" +
          subroutine +
          "  endprogram\n"
          "endpackage\n",
      f, "prog");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kProgramSignalFromOutside, 7,
                            "24.3"));
}

// A.1.11 gives `anonymous_program_item ::= task_declaration |
// function_declaration | class_declaration | interface_class_declaration |
// covergroup_declaration | class_constructor_declaration | ;`, so a task is one
// of the things a package's anonymous program declares, and its statements are
// held in ModuleItem::func_body_stmts.
TEST(ProgramConstruct, PackageAnonymousProgramTaskHierRefToProgramIsError) {
  ExpectPackageAnonymousProgramHierRefRejected(
      "    task t;\n"
      "      prog.psig = 1;\n"
      "    endtask\n");
}

// The same reference written in a function, which A.1.11 admits beside the
// task. The two reach the walk as different values of ModuleItem::kind, so a
// check narrowed to one kind reports the case above and not this one.
TEST(ProgramConstruct, PackageAnonymousProgramFunctionHierRefToProgramIsError) {
  ExpectPackageAnonymousProgramHierRefRejected(
      "    function void f();\n"
      "      prog.psig = 1;\n"
      "    endfunction\n");
}

// §24.3 bars an anonymous program from containing a hierarchical reference to
// another program scope and bars nothing else about it, so what the report
// selects is the reference and not the placement. The task below stands in the
// same package anonymous program as the two cases above, beside the same named
// program, and assigns a variable it declared itself.
TEST(ProgramConstruct, PackageAnonymousProgramWithoutHierRefElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "package pkg;\n"
      "  program;\n"
      "    task t;\n"
      "      int held;\n"
      "      held = 1;\n"
      "    endtask\n"
      "  endprogram\n"
      "endpackage\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.3 says "References to program signals from outside any program block
// shall be an error" and puts no condition on where the reference is written,
// so every position a statement holds a statement in is one the report reaches.
// WalkStmtsForProgramRef in
// src/elaborator/elaborator_validate_hier_refs.cpp had written out nine of
// the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h.
// The four cases below stand in the four positions it was missing, each of
// which elaborated clean beforehand with the reference into the program left
// unreported.

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(ProgramConstruct, ProgramSignalRefInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int psig;\n"
      "  endprogram\n"
      "  int q;\n"
      "  logic ok;\n"
      "  initial assert (ok) q = p.psig;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(ProgramConstruct, ProgramSignalRefInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pr;\n"
      "    int level;\n"
      "  endprogram\n"
      "  int depth;\n"
      "  logic armed;\n"
      "  initial assert (armed) else depth = pr.level;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §24.3
// judges the name rather than what runs, so the report stands whether the
// weighted draw would select the item or not.
TEST(ProgramConstruct, ProgramSignalRefInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pk;\n"
      "    int chosen;\n"
      "  endprogram\n"
      "  int taken;\n"
      "  initial randcase 1: taken = pk.chosen; endcase\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ProgramConstruct, ProgramSignalRefInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program ps;\n"
      "    int sampled;\n"
      "  endprogram\n"
      "  int kept;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = ps.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            8, "24.3"));
}

// §24.3: "anonymous programs shall not contain hierarchical references to other
// program scopes", and the clause puts no condition on where in the anonymous
// program the reference stands. A.1.11 admits a class_declaration as an
// anonymous_program_item, so a method of such a class is in the anonymous
// program and the reference it makes is one the clause reaches.
//
// The walk read an anonymous program's task and function bodies and never the
// methods of a class it declares, so this legal placement of an illegal
// reference went unreported. It is the opposite direction from §24.6's rule --
// a reference out of an anonymous program rather than into one -- and each rule
// walks the classes its own side reaches.
TEST(ProgramConstruct, ProgramSignalRefFromAnAnonymousProgramClassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  class C;\n"
      "    function void work();\n"
      "      ps.sampled = 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// §24.3 bars a reference to a "program signal", which the clause defines as a
// net or variable "declared within the scope of a program". §23.9 decides which
// declaration a reference reaches -- "If it is declared locally, then the local
// item shall be used" -- and a begin-end block is one of the scopes it lists,
// so a block-local `p` is what `p.a` names and the nested program `p` is not
// reached at all.
//
// The rule resolved nothing: it matched the leftmost component of a member
// access against the set of program instance names, so this legal source was
// refused. The local carries the program's name deliberately; one named
// anything else cannot fail.
TEST(ProgramConstruct,
     ABlockLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  initial begin\n"
      "    s_t p;\n"
      "    q = p.a;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The true positive beside the case above: the same block with the shadowing
// declaration taken out, so `p.a` reaches the nested program and §24.3's first
// sentence applies. A fix that silenced the rule wherever a member access
// appeared would pass the case above and fail this one, which is what makes the
// two a pair rather than one acceptance.
TEST(ProgramConstruct, AProgramSignalRefWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  initial begin\n"
      "    q = p.a;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// §24.3's third sentence -- "anonymous programs shall not contain hierarchical
// references to other program scopes" -- is read over a different set: the
// named programs of the compilation unit rather than the program instances of
// one module. It matched identifier text the same way, and §23.9 shadows it the
// same way: a function is a scope, so a declaration at the head of its body is
// what `ps.sampled` names.
TEST(ProgramConstruct,
     AnAnonymousProgramSubroutineLocalOfAProgramNameIsNotAHierRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class pkt;\n"
      "  int sampled;\n"
      "endclass\n"
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work();\n"
      "    pkt ps;\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A formal argument shadows the same way §23.9 makes a body-head declaration
// shadow, and reaches the body by a route no statement walk sees, so it is
// erased where the subroutine is read rather than where its statements are.
TEST(ProgramConstruct,
     AnAnonymousProgramSubroutineFormalOfAProgramNameIsNotAHierRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class pkt;\n"
      "  int sampled;\n"
      "endclass\n"
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work(pkt ps);\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The true positive beside the two above, in the same subroutine with nothing
// of the name declared in between, so `ps.sampled` reaches the program `ps` and
// the anonymous program does contain the reference §24.3's third sentence bars.
TEST(ProgramConstruct,
     AnAnonymousProgramHierRefWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work();\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// §24.3 says "References to program signals from outside any program block
// shall be an error" and names no position the reference may stand in, and
// §23.9 makes a task a scope within the module rather than outside it. So a
// module task body is one of the places outside the program that the sentence
// reaches. The rule read a continuous assignment and the body of a procedural
// block and nothing else, and a task's statements are in neither, so this
// source elaborated clean.
TEST(ProgramConstruct, AProgramSignalRefInAModuleTaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  task work();\n"
      "    q = p.a;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// A function beside the task above. The two item kinds are separate
// ModuleItemKind values reaching the walk through one branch, so a fix keyed on
// the task alone would leave the function unreported; the pair is what says the
// branch reads both.
TEST(ProgramConstruct, AProgramSignalRefInAModuleFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  function int work();\n"
      "    q = p.a;\n"
      "    return q;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

// The acceptance beside the task case: §23.9 makes the task a scope of its own,
// so a declaration at the head of its body is what `p.a` selects from and the
// nested program is not reached. The walk added for the task body is
// WalkSubroutineBodyForProgramRef, which erases such a declaration before
// reading the body; one that walked the body with the module's set unnarrowed
// would pass the two cases above and fail this one.
TEST(ProgramConstruct,
     ASubroutineLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  task work();\n"
      "    s_t p;\n"
      "    q = p.a;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A formal argument shadows the same way, and reaches the body by a route
// neither the statement walk nor the body-head loop above sees: it is in
// func_args rather than in func_body_stmts. The two acceptances therefore stand
// for the two erases WalkSubroutineBodyForProgramRef makes.
TEST(ProgramConstruct, AFormalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  function int work(s_t p);\n"
      "    q = p.a;\n"
      "    return q;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
