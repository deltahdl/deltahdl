#include <gtest/gtest.h>

#include <cstdint>
#include <format>

#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentElaboration, NetDeclAssignmentWithUnpackedDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w [3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
}

TEST(DeclarationAssignmentElaboration, ParamAssignmentResolvesConstant) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "WIDTH") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration,
     ParamAssignmentConstantExprReferencesParam) {
  // param_assignment's right side is a constant_param_expression. A literal
  // (covered above) and a reference to another parameter take different
  // constant-evaluation code paths; here B's value is derived from A.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = 4;\n"
      "  parameter B = A * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "B") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, ParamAssignmentNoDefaultInPort) {
  EXPECT_TRUE(
      ElabOk("module child #(parameter int P = 1)(); endmodule\n"
             "module m; child #(.P(10)) c(); endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, TypeAssignmentRegistersType) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter type T = int;\n"
             "  T x = 5;\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, TypeAssignmentNoDefaultInPort) {
  EXPECT_TRUE(
      ElabOk("module child #(parameter type T = int)();\n"
             "  T x = 0;\n"
             "endmodule\n"
             "module m; child c(); endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentPreservesInit) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "x") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentWithUnpackedDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int arr [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "arr") {
      found = true;
      EXPECT_EQ(v.unpacked_size, 4u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentDynamicArray) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int d[];\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentClassVariable) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, DefparamAssignmentOverridesChildParam) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module m;\n"
      "  child c();\n"
      "  defparam c.P = 42;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectParamOverridden(SoleChildInstance(design), "P", 42);
}

TEST(DeclarationAssignmentElaboration,
     DefparamAssignmentOverrideReferencesParam) {
  // defparam_assignment's right side is a constant_mintypmax_expression. Beyond
  // a literal override (covered above), the override value may reference a
  // parameter visible in the enclosing scope; that reference resolves during
  // elaboration to drive the child's parameter.
  ElabFixture f;
  auto* design = Elaborate(
      "module child;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module m;\n"
      "  parameter K = 55;\n"
      "  child c();\n"
      "  defparam c.P = K;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectParamOverridden(SoleChildInstance(design), "P", 55);
}

TEST(DeclarationAssignmentElaboration, DefparamAssignmentDeepHierarchy) {
  ElabFixture f;
  auto* design = Elaborate(
      "module leaf;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module m;\n"
      "  mid mi();\n"
      "  defparam mi.l.P = 99;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* mid_inst = top->children[0].resolved;
  ASSERT_NE(mid_inst, nullptr);
  ASSERT_FALSE(mid_inst->children.empty());
  auto* leaf_inst = mid_inst->children[0].resolved;
  ASSERT_NE(leaf_inst, nullptr);
  bool found = false;
  for (auto& p : leaf_inst->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_TRUE(p.from_override);
      EXPECT_EQ(p.resolved_value, 99);
    }
  }
  EXPECT_TRUE(found);
}

// A.2.4's class_new writes a shallow copy as `new expression`, and footnote 23
// has the expression evaluate to an object handle. An int, a 4-bit logic and a
// net, an int parameter port and a byte parameter are none, and each is
// reported, in a module item's initializer, a block's declaration and an
// assignment alike. A variable and a parameter of a named type, which may be a
// class, and an untyped parameter, whose type is its final value's (§6.20.2),
// are let through. Each was accepted, and the copy built nothing at run time.
TEST(DeclarationAssignmentElaboration, ShallowCopyOfNoHandleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "module m #(parameter int W = 2, parameter U = 1, parameter type T = "
      "int);\n"
      "  typedef int myint_t;\n"
      "  int x;\n"
      "  logic [3:0] y;\n"
      "  wire w;\n"
      "  myint_t z;\n"
      "  parameter byte P = 1;\n"
      "  localparam type L = int;\n"
      "  parameter myint_t N = 3;\n"
      "  C e = new x;\n"
      "  initial begin\n"
      "    C b;\n"
      "    C d = new y;\n"
      "    b = new w;\n"
      "    b = new W;\n"
      "    b = new P;\n"
      "    b = new z;\n"
      "    b = new U;\n"
      "    b = new N;\n"
      "  end\n"
      "endmodule\n",
      f);
  const struct {
    const char* name;
    uint32_t line;
    bool reported;
  } kSources[] = {{"x", 11, true},  {"y", 14, true}, {"w", 15, true},
                  {"W", 16, true},  {"P", 17, true}, {"z", 18, false},
                  {"U", 19, false}, {"N", 20, false}};
  for (const auto& source : kSources) {
    EXPECT_EQ(static_cast<bool>(ReportedError(
                  f.diag.Diagnostics(),
                  std::format("'{}' is no object handle, so 'new' makes no "
                              "shallow copy of it",
                              source.name),
                  source.line, "A.2.4")),
              source.reported)
        << source.name;
  }
}

// A handle is a shallow copy's source in each of its forms: a handle variable
// in a module item's initializer and in an assignment, an element of an array
// of handles, and `this` in a method.
TEST(DeclarationAssignmentElaboration, ShallowCopyOfHandleIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "  function C copy();\n"
      "    C c = new this;\n"
      "    return c;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C a = new;\n"
      "  C arr [2];\n"
      "  C e = new a;\n"
      "  initial begin\n"
      "    C b;\n"
      "    b = new a;\n"
      "    b = new arr[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
