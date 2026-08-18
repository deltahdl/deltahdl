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

}  // namespace
