#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "elaborator/rtlir.h"
#include "fixture_vpi_run.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// Detail 8: an omitted or null argument is written into an object, and with
// no object there is nothing to write.
TEST(TaskFuncCallModel, MarkingNoObjectAsAnArgumentDoesNothing) {
  VpiMakeEmptyArgument(nullptr);
  VpiMakeNullArgument(nullptr);
  VpiObject arg;
  VpiMakeNullArgument(&arg);
  EXPECT_EQ(arg.const_type, vpiNullConst);
}

// §37.42: a call's arguments are the ones it was written with; a missing one
// is no argument.
TEST(TaskFuncCallModel, AMissingArgumentIsNoneOfTheCalls) {
  VpiObject arg;
  arg.type = vpiConstant;
  VpiObject call;
  call.type = vpiFuncCall;
  call.arguments = {nullptr, &arg};
  VpiObject iter;
  VpiCollectTfCallArguments(&call, &iter);
  ASSERT_EQ(iter.children.size(), 1u);
  EXPECT_EQ(iter.children[0], &arg);
}

// §37.42 (figure): only a system task or function call reaches a user systf;
// any other object asked for one resolves nothing here.
TEST(TaskFuncCallModel, OnlyASystemCallReachesAUserSystf) {
  VpiObject module;
  module.type = vpiModule;
  VpiHandle out = nullptr;
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiUserSystf, &module, out));
  EXPECT_EQ(out, nullptr);
}

// A design whose top's one continuous assignment calls a function, run with a
// PLI application registered.
class CallsInAnAssignment : public VpiDesignRun {
 protected:
  // The function the call on the right of the assignment reaches.
  static vpiHandle CalledFunction() {
    vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiFunction, vpi_handle(vpiRhs, vpi_scan(it)));
  }
};

// §37.42 with §3.12.1: a call of a function the compilation unit declares
// reaches the unit's function, made where the unit holds no other data.
TEST_F(CallsInAnAssignment, ACallReachesTheCompilationUnitsFunction) {
  Run("function int f(); return 1; endfunction\n"
      "module top; wire [31:0] y; assign y = f(); endmodule\n");
  vpiHandle f = CalledFunction();
  ASSERT_NE(f, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "$unit::f");
}

// §27.4: a call in a generate block reaches the block's function of the name
// written, beside another the block declares...
TEST_F(CallsInAnAssignment, ACallReachesItsNameAmongTheBlocksFunctions) {
  Run("module top; if (1) begin : g\n"
      "  function int a(); return 1; endfunction\n"
      "  function int b(); return 2; endfunction\n"
      "  wire [31:0] w; assign w = b(); end endmodule\n");
  vpiHandle b = Named(vpiTaskFunc, By("top.g"), "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(b));
}

// ...and a call in a block nested in it reaches the function of the
// enclosing block where the nested one declares none.
TEST_F(CallsInAnAssignment, ACallReachesTheEnclosingBlocksFunction) {
  Run("module top; if (1) begin : g\n"
      "  function int f(); return 1; endfunction\n"
      "  if (1) begin : h wire [31:0] w; assign w = f(); end end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.g"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(f));
}

// §23.9: a call in the second of two sibling blocks that each declare a
// function of the name reaches its own block's, not the first block's.
TEST_F(CallsInAnAssignment, ACallReachesItsOwnBlocksFunctionOverASiblings) {
  Run("module top; if (1) begin : a\n"
      "  function int f(); return 1; endfunction int u; end\n"
      "  if (1) begin : b function int f(); return 2; endfunction\n"
      "  wire [31:0] w; assign w = f(); end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.b"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(f));
}

// §37.85 detail 2: a call in an unnamed block reaches the function of the
// block's implicit scope (#5737).
TEST_F(CallsInAnAssignment, ACallInAnUnnamedBlockReachesItsFunction) {
  Run("module top; if (1) begin\n"
      "  function int f(); return 1; endfunction\n"
      "  wire [31:0] w; assign w = f(); end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.genblk1"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(f));
}

// §23.9: a call the module writes outside every block reaches the module's
// function, not that of a block declared ahead of it.
TEST_F(CallsInAnAssignment, AModuleCallReachesTheModulesFunctionOverABlocks) {
  Run("module top;\n"
      "  if (1) begin : g function int f(); return 1; endfunction end\n"
      "  function int f(); return 2; endfunction\n"
      "  wire [31:0] y; assign y = f(); endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(f));
}

// §26.3: a call reaches the package function the module imports by its name,
// passing over an import of another of the package's items...
TEST_F(CallsInAnAssignment, ACallReachesAFunctionImportedByName) {
  Run("package p; int x; function int f(); return 1; endfunction\n"
      "  function int g(); return 2; endfunction endpackage\n"
      "module top; import p::x; import p::g;\n"
      "  wire [31:0] y; assign y = g(); endmodule\n");
  vpiHandle g = Named(vpiTaskFunc, By("p"), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(g));
}

// ...and the function of the one wildcard-imported package that declares it.
TEST_F(CallsInAnAssignment, ACallReachesTheWildcardImportDeclaringIt) {
  Run("package p; function int f(); return 1; endfunction endpackage\n"
      "package q; function int h(); return 3; endfunction endpackage\n"
      "module top; import p::*; import q::*;\n"
      "  wire [31:0] y; assign y = h(); endmodule\n");
  vpiHandle h = Named(vpiTaskFunc, By("q"), "h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(h));
}

// §37.42 with §26.3: a callee written `p::f` resolves to the function the
// package p declares, with no object where none was made for it; any other
// callee but a name resolves to none: an expression of another kind, a
// member access, and a scope resolution missing a side or joining anything
// but two names.
TEST(TaskFuncCallModel, OnlyAPackagesFunctionResolvesAScopedCallee) {
  ModuleItem function;
  function.kind = ModuleItemKind::kFunctionDecl;
  function.name = "f";
  PackageDecl package;
  package.name = "p";
  package.items = {&function};
  RtlirDesign design;
  design.packages = {&package};
  RtlirModule mod;
  const std::string kPrefix = "top";
  const VpiSubroutineObjects kMade;
  const VpiCallSite kSite{design, mod, kPrefix, nullptr, kMade};
  Expr p;
  p.kind = ExprKind::kIdentifier;
  p.text = "p";
  Expr f;
  f.kind = ExprKind::kIdentifier;
  f.text = "f";
  Expr other;
  other.kind = ExprKind::kIntegerLiteral;
  Expr scoped;
  scoped.kind = ExprKind::kMemberAccess;
  scoped.is_scope_resolution = true;
  scoped.lhs = &p;
  scoped.rhs = &f;
  const VpiCalledSubroutine kCalled = VpiCalleeSubroutine(kSite, scoped);
  EXPECT_EQ(kCalled.decl, &function);
  EXPECT_EQ(kCalled.object, nullptr);
  EXPECT_EQ(VpiCalleeSubroutine(kSite, other).decl, nullptr);
  Expr member = scoped;
  member.is_scope_resolution = false;
  EXPECT_EQ(VpiCalleeSubroutine(kSite, member).decl, nullptr);
  const std::pair<Expr*, Expr*> kSides[] = {
      {nullptr, &f}, {&p, nullptr}, {&other, &f}, {&p, &other}};
  for (const auto& [lhs, rhs] : kSides) {
    Expr partial = scoped;
    partial.lhs = lhs;
    partial.rhs = rhs;
    EXPECT_EQ(VpiCalleeSubroutine(kSite, partial).decl, nullptr);
  }
}

// §37.42: a name no generate block, module, compilation unit or imported
// package declares resolves to no task or function and no object.
TEST(TaskFuncCallModel, ANameNothingDeclaresResolvesToNone) {
  RtlirDesign design;
  RtlirModule mod;
  RtlirImport wildcard;
  wildcard.package_name = "p";
  wildcard.is_wildcard = true;
  mod.imports.push_back(wildcard);
  const std::string kPrefix = "top";
  const VpiSubroutineObjects kMade;
  const VpiCalledSubroutine kCalled =
      VpiNamedSubroutine({design, mod, kPrefix, nullptr, kMade}, "f");
  EXPECT_EQ(kCalled.decl, nullptr);
  EXPECT_EQ(kCalled.object, nullptr);
}

}  // namespace
}  // namespace delta
