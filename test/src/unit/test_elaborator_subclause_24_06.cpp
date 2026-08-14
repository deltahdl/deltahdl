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

}  // namespace
