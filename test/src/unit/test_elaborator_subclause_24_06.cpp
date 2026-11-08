#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
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

TEST(AnonymousProgramNameSpaceSharing,
     AnonymousProgramFunctionAndPackageVariableSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  program; function int f(); return 7; endfunction endprogram\n"
      "  int f;\n"
      "endpackage\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'f' declared in anonymous program collides with "
                            "name in surrounding package",
                            3, "24.6"));
}

TEST(AnonymousProgramNameSpaceSharing,
     AnonymousProgramTaskAndCompilationUnitVariableSameNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program; task g; endtask endprogram\n"
      "int g;\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'g' declared in anonymous program collides with "
                            "name in surrounding package",
                            2, "24.6"));
}

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

constexpr std::string_view kNotReferencedOutside =
    "cannot be referenced outside";

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

TEST(AnonymousProgramWideSpace, ProgramCallingAnonymousProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task probe(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  program tb;\n"
      "    initial probe();\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

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

void ExpectProgramWideSpaceRefRejected(const std::string& src, uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotReferencedOutside, line, "24.6"));
}

TEST(AnonymousProgramWideSpace, PackageTaskCallingAnonymousProgramTaskIsError) {
  ExpectProgramWideSpaceRefRejected(
      "package pkg;\n"
      "  program;\n"
      "    task probe(); endtask\n"
      "  endprogram\n"
      "  task caller();\n"
      "    probe();\n"
      "  endtask\n"
      "endpackage\n"
      "module top; endmodule\n",
      6);
}

TEST(AnonymousProgramWideSpace,
     PackageItemDeclaringAnonymousProgramClassHandleIsError) {
  ExpectProgramWideSpaceRefRejected(
      "package pkg;\n"
      "  program;\n"
      "    class Secret; endclass\n"
      "  endprogram\n"
      "  Secret handle;\n"
      "endpackage\n"
      "module top; endmodule\n",
      5);
}

TEST(AnonymousProgramWideSpace,
     CompilationUnitItemCallingAnonymousProgramFunctionIsError) {
  ExpectProgramWideSpaceRefRejected(
      "program;\n"
      "  function int probe(); return 1; endfunction\n"
      "endprogram\n"
      "int cached = probe();\n"
      "module top; endmodule\n",
      4);
}

TEST(AnonymousProgramWideSpace,
     AnonymousProgramCallingAnotherAnonymousProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task probe(); endtask\n"
      "endprogram\n"
      "program;\n"
      "  task caller();\n"
      "    probe();\n"
      "  endtask\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AnonymousProgramWideSpace, ABlockLocalOfTheSameNameIsNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  task work();\n"
      "    int t;\n"
      "    t = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AnonymousProgramWideSpace, AFormalArgumentOfTheSameNameIsNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  task work(input int t);\n"
      "    int x;\n"
      "    x = t;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AnonymousProgramWideSpace,
     ACallWithNoShadowingDeclarationIsStillReported) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  task work();\n"
      "    t();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an identifier declared inside an anonymous "
                            "program cannot be referenced outside any program "
                            "block",
                            6, "24.6"));
}

TEST(AnonymousProgramWideSpace, ACallFromAClassMethodInAModuleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  class C;\n"
      "    function void work();\n"
      "      t();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an identifier declared inside an anonymous "
                            "program cannot be referenced outside any program "
                            "block",
                            7, "24.6"));
}

TEST(AnonymousProgramWideSpace,
     ACallFromACompilationUnitClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "class C;\n"
      "  function void work();\n"
      "    t();\n"
      "  endfunction\n"
      "endclass\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an identifier declared inside an anonymous "
                            "program cannot be referenced outside any program "
                            "block",
                            6, "24.6"));
}

TEST(AnonymousProgramWideSpace, AClassMethodLocalOfTheSameNameIsNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  class C;\n"
      "    function void work();\n"
      "      int t;\n"
      "      t = 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AnonymousProgramWideSpace, ACallFromANestedClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void work();\n"
      "        t();\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an identifier declared inside an anonymous "
                            "program cannot be referenced outside any program "
                            "block",
                            8, "24.6"));
}

TEST(AnonymousProgramWideSpace,
     ANestedClassMethodLocalOfTheSameNameIsNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program;\n"
      "  task t(); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void work();\n"
      "        int t;\n"
      "        t = 1;\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
