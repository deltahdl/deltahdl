#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConstConstantElaboration, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstIntWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstNonblockingReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top #(parameter P = 5);\n"
      "  const int x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromLocalparamSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam LP = 10;\n"
      "  const int x = LP;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromAnotherConstSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int a = 5;\n"
      "  const int b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  const int LIMIT = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "LIMIT") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.6: a static const may be set to an enumerated name. The elaborator
// accepts an enumeration member as the initializing expression without
// requiring a cast or flagging it as a non-constant.
TEST(ConstConstantElaboration, ConstInitializedFromEnumNameSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum int {RED, GREEN, BLUE} color_t;\n"
      "  const int x = GREEN;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.6: a static const may be set to a constant function of the permitted
// operands. A call to a user function in the initializer elaborates cleanly.
TEST(ConstConstantElaboration, ConstInitializedFromConstantFunctionSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int double_it(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  const int x = double_it(21);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.6: unlike a value parameter, a const constant may be initialized from a
// hierarchical name, because const constants are calculated after elaboration.
// The elaborator does not emit the "hierarchical name not allowed" diagnostic
// it raises for enum named constants when the same form appears in a const
// initializer (the LRM example is `const logic option = a.b.c;`).
TEST(ConstConstantElaboration, ConstWithHierarchicalNameInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const logic option = a.b.c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.6: an automatic const (one declared in an automatic scope, such as an
// automatic subroutine) may be set to any expression that would be legal
// without the const keyword, unlike a static const which must be set at
// elaboration time. Here the initializer depends on a run-time argument value.
TEST(ConstConstantElaboration, ConstAutomaticAcceptsRuntimeInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int add_one(int a);\n"
      "    const int local_c = a + 1;\n"
      "    return local_c;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.6: an instance of a class (an object handle) may be declared with the
// const keyword, initialized at its declaration from a constructor call. The
// declaration elaborates without error.
TEST(ConstConstantElaboration, ConstClassHandleDeclarationSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new(int a);\n"
      "    x = a;\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.6: a const object handle behaves like a variable that cannot be
// written, so rebinding the handle to a different object is an error.
TEST(ConstConstantElaboration, ConstClassHandleReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj = new();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.20.6: although a const object handle cannot be rebound, the members of the
// referenced object remain writable. A write to a member of a const handle is
// not flagged as a write to a constant.
TEST(ConstConstantElaboration, ConstObjectMemberWriteSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj.x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
