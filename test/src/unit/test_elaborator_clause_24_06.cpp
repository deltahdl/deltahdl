#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
