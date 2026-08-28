#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AnonymousProgramNameSpaceSharing,
     PackageItemAndAnonymousProgramItemSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  task t(); endtask\n"
      "  program;\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  // The collision is reported at the second declaration of `t`, the one inside
  // the anonymous program on line 4.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'t' declared in anonymous program collides with "
                            "name in surrounding package",
                            4, "24.6"));
}

TEST(AnonymousProgramNameSpaceSharing,
     AnonymousProgramItemAndPackageItemSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "  endprogram\n"
      "  function void f(); endfunction\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  // The anonymous program declares `f` first, so the collision is reported at
  // the package-level declaration on line 5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'f' declared in anonymous program collides with "
                            "name in surrounding package",
                            5, "24.6"));
}

TEST(AnonymousProgramNameSpaceSharing,
     CompilationUnitItemAndAnonymousProgramItemSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "task t(); endtask\n"
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  // The compilation-unit `t` comes first, so the collision is reported at the
  // anonymous program's declaration on line 3.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'t' declared in anonymous program collides with "
                            "name in surrounding package",
                            3, "24.6"));
}

TEST(AnonymousProgramNameSpaceSharing,
     TwoAnonymousProgramsInSamePackageWithSameItemNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "  endprogram\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  // Both declarations of `f` sit in anonymous programs; the collision is
  // reported at the second one, on line 6.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'f' declared in anonymous program collides with "
                            "name in surrounding package",
                            6, "24.6"));
}

TEST(AnonymousProgramNameSpaceSharing,
     DistinctNamesAcrossAnonymousProgramAndPackageElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  task outer_t(); endtask\n"
      "  program;\n"
      "    task inner_t(); endtask\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AnonymousProgramNameSpaceSharing,
     DistinctNamesAcrossAnonymousProgramAndCompilationUnitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "task outer_t(); endtask\n"
      "program;\n"
      "  task inner_t(); endtask\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.6: a class is one of the items A.1.11 admits into an anonymous program,
// and it shares the enclosing package's name space like any other. The package
// declares C first, so the collision stands at the anonymous program's own
// declaration. A check comparing only the subroutines reports nothing here, and
// nothing else does either: the §3.13 compilation-unit check passes over an
// anonymous program's items on the ground that this check judges them.
TEST(AnonymousProgramNameSpaceSharing,
     PackageClassAndAnonymousProgramClassSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  class C; endclass\n"
      "  program;\n"
      "    class C; endclass\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'C' declared in anonymous program collides with "
                            "name in surrounding package",
                            4, "24.6"));
}

// §24.6: the same for a class at compilation-unit scope, which reaches the
// check by the other of its two entry points. The anonymous program declares C
// first here, so the collision stands at the compilation-unit declaration that
// follows it — the shared name space is shared in both directions.
TEST(AnonymousProgramNameSpaceSharing,
     AnonymousProgramClassAndCompilationUnitClassSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  class C; endclass\n"
      "endprogram\n"
      "class C; endclass\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'C' declared in anonymous program collides with "
                            "name in surrounding package",
                            4, "24.6"));
}

// §24.6: a covergroup is likewise an anonymous_program_item, and likewise
// shares the name space. It reaches the check by a different item kind from the
// class above, so neither case stands for the other.
TEST(AnonymousProgramNameSpaceSharing,
     PackageCovergroupAndAnonymousProgramCovergroupSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  covergroup cg; endgroup\n"
      "  program;\n"
      "    covergroup cg; endgroup\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'cg' declared in anonymous program collides with "
                            "name in surrounding package",
                            4, "24.6"));
}

// §24.6: what the shared name space forbids is one name declared twice, not a
// class declared inside an anonymous program at all. Distinct names elaborate,
// so the cases above report a collision rather than the anonymous program's
// class itself.
TEST(AnonymousProgramNameSpaceSharing,
     DistinctClassNamesAcrossAnonymousProgramAndPackageElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  class Outer; endclass\n"
      "  program;\n"
      "    class Inner; endclass\n"
      "  endprogram\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.6 opens by ruling that "the set of program definitions and instances
// define a space of program-wide data, tasks, and functions that is accessible
// only to programs", and its NOTE states the consequence for an anonymous
// program: "identifiers declared inside an anonymous program cannot be
// referenced outside any program block". §24.3 says what a program block is,
// giving `program_declaration` its syntax and ruling that "references to
// program signals from outside any program block shall be an error"; the same
// paragraph makes a reference from one program scope to another legal, which is
// what ProgramCallingAnonymousProgramTaskElaborates below stands for.
//
// The three rejection cases below share this substring rather than the whole
// sentence so that one literal serves every position a reference can stand in.
// The report names no identifier: the walk answers whether an expression
// mentions any of the anonymous program's names, so it has no name to quote and
// one wording serves them all. No other report in the tree says a reference is
// barred from a place, so the fragment is this rule's alone.
constexpr std::string_view kNotReferencedOutside =
    "cannot be referenced outside";

// §24.6: a design module is not a program, so a task an anonymous program
// declared at compilation-unit scope is outside its reach. The parser flattens
// the anonymous program's items into CompilationUnit::cu_items (§24.6 declares
// no new scope), so the call resolves like any call to a compilation-unit task
// -- CompilationUnitElaboration.ForwardReferenceToCuScopeTaskAccepted in
// test_elaborator_subclause_03_12_01.cpp is the same shape with no anonymous
// program around the declaration, and it elaborates.
TEST(AnonymousProgramWideSpace, ModuleCallingAnonymousProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  task probe(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  initial probe();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotReferencedOutside, 5, "24.6"));
}

// §24.6: the space is "accessible only to programs", not accessible to nobody.
// A named program is a program block, so the identical call made from inside
// one is legal and elaborates. Without this case, refusing the call from every
// scope satisfies the case above while leaving the anonymous program with no
// caller at all, which is the opposite of what the clause is for.
TEST(AnonymousProgramWideSpace, ProgramCallingAnonymousProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task probe(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  program checker;\n"
      "    initial probe();\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.6: "anonymous programs can be used inside packages (see Clause 26) or
// compilation-unit scopes (see 3.12.1)", and the space is one space however the
// item was declared. A package's items are held in PackageDecl::items rather
// than in CompilationUnit::cu_items and reach a module through the import
// (§26.3), so this is a second route into the module and not the first one
// written twice: a check placed only where the compilation-unit names are
// gathered leaves this call unreported.
TEST(AnonymousProgramWideSpace,
     ModuleCallingImportedAnonymousProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  program;\n"
      "    task probe(); endtask\n"
      "  endprogram\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  initial probe();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotReferencedOutside, 8, "24.6"));
}

// §24.6's NOTE bars every "identifier declared inside an anonymous program"
// from being referenced outside a program block, and puts no kind on the
// identifier. A.1.11 gives `anonymous_program_item ::= task_declaration |
// function_declaration | class_declaration | interface_class_declaration |
// covergroup_declaration | class_constructor_declaration | ;`, so a class is
// one of the things an anonymous program declares, and §24.3 counts "class
// definitions" among a program block's contents. The subject the clause's first
// sentence enumerates -- "data, tasks, and functions" -- is therefore not the
// limit of what the NOTE covers, and a rule written over subroutine calls alone
// leaves the type name reachable.
//
// The reference here is the module's own variable declaration naming the class
// as its type, which the elaborator already recognizes as a class reference:
// Elaborator::ValidateVarDeclTypes in src/elaborator/elaborator_decls_var.cpp
// selects a declaration whose DataType::type_name is in class_names_, and
// ClassifyCuScopeItem in src/elaborator/elaborator_resolve.cpp is what put the
// anonymous program's class into class_names_. The declaration carries no
// initializer, so the report stands on naming the type and not on calling
// new().
TEST(AnonymousProgramWideSpace,
     ModuleDeclaringAnonymousProgramClassHandleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  class Secret; endclass\n"
      "endprogram\n"
      "module top;\n"
      "  Secret handle;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotReferencedOutside, 5, "24.6"));
}

}  // namespace
