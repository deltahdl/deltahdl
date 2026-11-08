#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
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

TEST(TaskFuncCallModel, MarkingNoObjectAsAnArgumentDoesNothing) {
  VpiMakeEmptyArgument(nullptr);
  VpiMakeNullArgument(nullptr);
  VpiObject arg;
  VpiMakeNullArgument(&arg);
  EXPECT_EQ(arg.const_type, vpiNullConst);
}

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

TEST(TaskFuncCallModel, OnlyASystemCallReachesAUserSystf) {
  VpiObject module;
  module.type = vpiModule;
  VpiHandle out = nullptr;
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiUserSystf, &module, out));
  EXPECT_EQ(out, nullptr);
}

class CallsInAnAssignment : public VpiDesignRun {
 protected:
  static vpiHandle CalledFunction(const char* scope = "top") {
    vpiHandle it = vpi_iterate(vpiContAssign, By(scope));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiFunction, vpi_handle(vpiRhs, vpi_scan(it)));
  }
};

TEST_F(CallsInAnAssignment, ACallReachesTheCompilationUnitsFunction) {
  Run("function int f(); return 1; endfunction\n"
      "module top; wire [31:0] y; assign y = f(); endmodule\n");
  vpiHandle f = CalledFunction();
  ASSERT_NE(f, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "$unit::f");
}

TEST_F(CallsInAnAssignment, ACallReachesItsNameAmongTheBlocksFunctions) {
  Run("module top; if (1) begin : g\n"
      "  function int a(); return 1; endfunction\n"
      "  function int b(); return 2; endfunction\n"
      "  wire [31:0] w; assign w = b(); end endmodule\n");
  vpiHandle b = Named(vpiTaskFunc, By("top.g"), "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction("top.g")), VpiObjectOf(b));
}

TEST_F(CallsInAnAssignment, ACallReachesTheEnclosingBlocksFunction) {
  Run("module top; if (1) begin : g\n"
      "  function int f(); return 1; endfunction\n"
      "  if (1) begin : h wire [31:0] w; assign w = f(); end end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.g"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction("top.g.h")), VpiObjectOf(f));
}

TEST_F(CallsInAnAssignment, ACallReachesItsOwnBlocksFunctionOverASiblings) {
  Run("module top; if (1) begin : a\n"
      "  function int f(); return 1; endfunction int u; end\n"
      "  if (1) begin : b function int f(); return 2; endfunction\n"
      "  wire [31:0] w; assign w = f(); end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.b"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction("top.b")), VpiObjectOf(f));
}

TEST_F(CallsInAnAssignment, ACallInAnUnnamedBlockReachesItsFunction) {
  Run("module top; if (1) begin\n"
      "  function int f(); return 1; endfunction\n"
      "  wire [31:0] w; assign w = f(); end endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.genblk1"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction("top.genblk1")), VpiObjectOf(f));
}

TEST_F(CallsInAnAssignment, AModuleCallReachesTheModulesFunctionOverABlocks) {
  Run("module top;\n"
      "  if (1) begin : g function int f(); return 1; endfunction end\n"
      "  function int f(); return 2; endfunction\n"
      "  wire [31:0] y; assign y = f(); endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(f));
}

TEST_F(CallsInAnAssignment, ACallReachesAFunctionImportedByName) {
  Run("package p; int x; function int f(); return 1; endfunction\n"
      "  function int g(); return 2; endfunction endpackage\n"
      "module top; import p::x; import p::g;\n"
      "  wire [31:0] y; assign y = g(); endmodule\n");
  vpiHandle g = Named(vpiTaskFunc, By("p"), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(g));
}

TEST_F(CallsInAnAssignment, ACallReachesTheWildcardImportDeclaringIt) {
  Run("package p; function int f(); return 1; endfunction endpackage\n"
      "package q; function int h(); return 3; endfunction endpackage\n"
      "module top; import p::*; import q::*;\n"
      "  wire [31:0] y; assign y = h(); endmodule\n");
  vpiHandle h = Named(vpiTaskFunc, By("q"), "h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(VpiObjectOf(CalledFunction()), VpiObjectOf(h));
}

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

TEST(TaskFuncCallModel, ABlocksFunctionCalledOutsideItsBlockHasNoObject) {
  ModuleItem function;
  function.kind = ModuleItemKind::kFunctionDecl;
  function.name = "f";
  RtlirDesign design;
  RtlirModule mod;
  mod.function_decls = {&function};
  RtlirGenBlockSubroutine sub;
  sub.decl = &function;
  mod.gen_block_subroutines.push_back(sub);
  const std::string kPrefix = "top";
  const VpiSubroutineObjects kMade;
  const VpiCalledSubroutine kCalled =
      VpiNamedSubroutine({design, mod, kPrefix, nullptr, kMade}, "f");
  EXPECT_EQ(kCalled.decl, &function);
  EXPECT_EQ(kCalled.object, nullptr);
}

class CallStatementsInAScope : public VpiDesignRun {
 protected:
  static std::vector<std::string> MethodCallsOf(vpiHandle scope) {
    std::vector<std::string> calls;
    vpiHandle it = vpi_iterate(vpiStmt, scope);
    if (it == nullptr) return calls;
    while (vpiHandle stmt = vpi_scan(it)) {
      if (vpi_get(vpiType, stmt) != vpiMethodFuncCall) continue;
      calls.emplace_back(vpi_get_str(vpiName, vpi_handle(vpiPrefix, stmt)));
    }
    return calls;
  }

  static void ExpectTaskCallReaches(const char* method, const char* scope,
                                    const char* cls) {
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), method);
    vpiHandle declared =
        Named(vpiMethods, Named(vpiClassDefn, By(scope), cls), method);
    ASSERT_NE(call, nullptr) << method;
    ASSERT_NE(declared, nullptr) << method;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(declared))
        << method;
  }
};

TEST_F(CallStatementsInAScope, ABlocksBuiltInValuesTakeTheirKindsMethods) {
  Run("module top; typedef enum {A, B} e_t; class C; endclass\n"
      "  localparam int N = 2;\n"
      "  initial begin : b\n"
      "    int q[$]; int s[string]; int t[e_t]; int c[C]; int p[N];\n"
      "    string str; e_t e;\n"
      "    q.push_back(1); s.delete(); t.delete(); c.delete(); p.sort();\n"
      "    str.putc(0, \"c\"); e.next();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(MethodCallsOf(By("top.b")),
            (std::vector<std::string>{"q", "s", "t", "c", "p", "str", "e"}));
}

TEST_F(CallStatementsInAScope, AModulesArraysAndAnonymousEnumTakeTheirMethods) {
  Run("module top; int d[]; int f[2]; enum {X, Y} e;\n"
      "  initial begin : b d.delete(); f.sort(); e.next(); end\n"
      "endmodule\n");
  EXPECT_EQ(MethodCallsOf(By("top.b")),
            (std::vector<std::string>{"d", "f", "e"}));
}

TEST_F(CallStatementsInAScope, AChainsMemberIsFoundPastTheMembersBeforeIt) {
  Run("module top;\n"
      "  class B; task run(); endtask endclass\n"
      "  class H; function void f(); endfunction int n; B b = new; endclass\n"
      "  H h = new;\n"
      "  initial h.b.run();\n"
      "endmodule\n");
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle call = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(
                Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run")));
}

TEST_F(CallStatementsInAScope, AVoidCastCallIsTheFuncCallItWraps) {
  Run("module top; function int f(int a); return a; endfunction\n"
      "  initial begin : b void'(f(3)); end\n"
      "endmodule\n");
  vpiHandle call = CallOf(vpiFuncCall, By("top.b"), "f");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, call)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "f")));
  EXPECT_EQ(KindsOf(vpiArgument, call), std::vector<int>{vpiConstant});
}

TEST_F(CallStatementsInAScope, AStaticMethodCalledThroughItsScopeIsACall) {
  Run("package q; endpackage\n"
      "package p; localparam int K = 1;\n"
      "  class D; static function void g(); endfunction endclass\n"
      "endpackage\n"
      "module top;\n"
      "  class C; static function void f(); endfunction endclass\n"
      "  initial begin : b C::f(); p::D::g(); end\n"
      "endmodule\n");
  vpiHandle f = CallOf(vpiMethodFuncCall, By("top.b"), "f");
  vpiHandle g = CallOf(vpiMethodFuncCall, By("top.b"), "g");
  vpiHandle c_f = Named(vpiMethods, Named(vpiClassDefn, By("top"), "C"), "f");
  vpiHandle d_g = Named(vpiMethods, Named(vpiClassDefn, By("p"), "D"), "g");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(c_f, nullptr);
  ASSERT_NE(d_g, nullptr);
  EXPECT_EQ(vpi_handle(vpiPrefix, f), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, f)), VpiObjectOf(c_f));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, g)), VpiObjectOf(d_g));
}

TEST_F(CallStatementsInAScope, AGenerateBlocksStaticMethodCalledIsACall) {
  Run("module top;\n"
      "  if (1) begin : g\n"
      "    class C; static function void f(); endfunction endclass\n"
      "    initial begin : b C::f(); end\n"
      "  end\n"
      "endmodule\n");
  vpiHandle f = CallOf(vpiMethodFuncCall, By("top.g.b"), "f");
  vpiHandle c_f = Named(vpiMethods, Named(vpiClassDefn, By("top.g"), "C"), "f");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(c_f, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, f)), VpiObjectOf(c_f));
}

TEST_F(CallStatementsInAScope, ALoopBlocksCallReachesItsOwnInstancesMethod) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    class C; static function void f(); endfunction endclass\n"
      "    if (1) begin : h\n"
      "      initial begin : b C::f(); end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  for (const std::string kIn : {"top.g[0]", "top.g[1]"}) {
    vpiHandle f = CallOf(vpiMethodFuncCall, By(kIn + ".h.b"), "f");
    vpiHandle c_f = Named(vpiMethods, Named(vpiClassDefn, By(kIn), "C"), "f");
    ASSERT_NE(f, nullptr);
    ASSERT_NE(c_f, nullptr);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, f)), VpiObjectOf(c_f));
  }
}

TEST_F(CallStatementsInAScope, AScopesSpecializationChoosesItsBase) {
  Run("module top;\n"
      "  class B; static function void run(); endfunction endclass\n"
      "  class B2; static task tick(); endtask endclass\n"
      "  class C #(type T = B) extends T; endclass\n"
      "  initial begin : b\n"
      "    C #(.T(B2))::tick(); C #(B2)::tick(); C #(.T())::run();\n"
      "  end\n"
      "endmodule\n");
  vpiHandle tick =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "B2"), "tick");
  vpiHandle run = Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run");
  ASSERT_NE(tick, nullptr);
  ASSERT_NE(run, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> calls;
  while (vpiHandle stmt = vpi_scan(it)) calls.push_back(stmt);
  ASSERT_EQ(calls.size(), 3u);
  for (std::size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(vpi_get(vpiType, calls[i]), vpiMethodTaskCall) << i;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, calls[i])), VpiObjectOf(tick))
        << i;
  }
  EXPECT_EQ(vpi_get(vpiType, calls[2]), vpiMethodFuncCall);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, calls[2])), VpiObjectOf(run));
}

TEST_F(CallStatementsInAScope, ACallOnATypedefsHandleReachesItsClassMethod) {
  Run("module top;\n"
      "  class C; task go(); endtask endclass\n"
      "  class B; task run(); endtask C c = new; endclass\n"
      "  typedef B B_t;\n"
      "  initial begin : b B_t x; x = new; x.run(); x.c.go(); end\n"
      "endmodule\n");
  ExpectTaskCallReaches("run", "top", "B");
  ExpectTaskCallReaches("go", "top", "C");
}

TEST_F(CallStatementsInAScope, ACallOnAnImportedClasssHandleReachesItsMethod) {
  Run("package q; endpackage\n"
      "package p; localparam int K = 1;\n"
      "  class D; task run(); endtask endclass\n"
      "  class E; task go(); endtask endclass\n"
      "endpackage\n"
      "module top; import q::*; import p::K; import p::D; import p::*;\n"
      "  D d = new; E e = new;\n"
      "  initial begin : b d.run(); e.go(); end\n"
      "endmodule\n");
  ExpectTaskCallReaches("run", "p", "D");
  ExpectTaskCallReaches("go", "p", "E");
}

TEST_F(CallStatementsInAScope, AChainThroughAnInstanceReachesItsVariable) {
  Run("module sub; class B; task run(); endtask endclass B h = new;\n"
      "endmodule\n"
      "module top; sub u (); initial begin : b u.h.run(); end endmodule\n");
  ExpectTaskCallReaches("run", "top.u", "B");
  vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(By("top.u.h"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, call)),
            VpiObjectOf(By("top.u.h")));
}

TEST_F(CallStatementsInAScope, ACallThroughAnExpressionReachesItsMethod) {
  Run("package q; endpackage\n"
      "package p; class D; task go(); endtask endclass\n"
      "  int n; D obj = new;\n"
      "endpackage\n"
      "module top;\n"
      "  class B; task run(); endtask B h; endclass\n"
      "  function automatic B make(); B b = new; return b; endfunction\n"
      "  B objs [2];\n"
      "  initial begin : b\n"
      "    objs[0] = new; objs[0].h = new;\n"
      "    objs[0].run(); objs[0].h.run(); make().run(); p::obj.go();\n"
      "  end\n"
      "endmodule\n");
  vpiHandle b_run =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run");
  vpiHandle d_go = Named(vpiMethods, Named(vpiClassDefn, By("p"), "D"), "go");
  ASSERT_NE(b_run, nullptr);
  ASSERT_NE(d_go, nullptr);
  std::vector<VpiObject*> reached;
  std::vector<bool> prefixed;
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle stmt = vpi_scan(it)) {
    if (vpi_get(vpiType, stmt) != vpiMethodTaskCall) continue;
    prefixed.push_back(vpi_handle(vpiPrefix, stmt) != nullptr);
    reached.push_back(VpiObjectOf(vpi_handle(vpiTask, stmt)));
  }
  EXPECT_EQ(prefixed, (std::vector<bool>{true, true, true, true}));
  EXPECT_EQ(reached,
            (std::vector<VpiObject*>{VpiObjectOf(b_run), VpiObjectOf(b_run),
                                     VpiObjectOf(b_run), VpiObjectOf(d_go)}));
}

TEST_F(CallStatementsInAScope, ACallThroughAVirtualInterfaceIsATaskCall) {
  Run("interface other; endinterface\n"
      "interface ifc; logic x; function void f(); endfunction\n"
      "  task t(); endtask\n"
      "endinterface\n"
      "interface lone; task t(); endtask endinterface\n"
      "module top; ifc i (); other o ();\n"
      "  class H; virtual ifc vif; endclass\n"
      "  virtual ifc v = i; virtual lone w; H h = new;\n"
      "  initial begin : b virtual ifc u; u = i; h.vif = i;\n"
      "    v.t(); h.vif.t(); u.t(); v.f();\n"
      "    if (0) begin : g w.t(); end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiTaskCall, By("top.b")).size(), 3U);
  EXPECT_EQ(ObjectsOf(vpiFuncCall, By("top.b")).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiTaskCall, By("top.b.g")).size(), 1U);
}

TEST_F(CallStatementsInAScope, ACallOfADpiImportIsACall) {
  Run("module top;\n"
      "  import \"DPI-C\" function int c_f(int a);\n"
      "  import \"DPI-C\" task c_t();\n"
      "  initial if (0) begin : b void'(c_f(1)); c_t(); end\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiFuncCall, By("top.b")).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiTaskCall, By("top.b")).size(), 1U);
}

TEST_F(CallStatementsInAScope, ACallOnAResultOrAConditionalReachesItsMethod) {
  Run("package p; class D; task go(); endtask endclass\n"
      "  function automatic D make_d(); D d = new; return d; endfunction\n"
      "endpackage\n"
      "module top;\n"
      "  class B; task run(); endtask\n"
      "    function B self(); return this; endfunction\n"
      "    static function B make(); B b = new; return b; endfunction\n"
      "  endclass\n"
      "  B a = new, c = new; bit s;\n"
      "  initial begin : b a.self().run(); (s ? a : c).run();\n"
      "    B::make().run(); p::make_d().go();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiMethodTaskCall, By("top.b")).size(), 4U);
  ExpectTaskCallReaches("run", "top", "B");
  ExpectTaskCallReaches("go", "p", "D");
}

TEST_F(CallStatementsInAScope, ACallThroughAStructMemberReachesItsMethod) {
  Run("module sub; endmodule\n"
      "module top; sub u ();\n"
      "  class B; task run(); endtask endclass\n"
      "  typedef int other_t;\n"
      "  typedef struct { int n; B h; } s_t;\n"
      "  s_t s; struct { B h; } t;\n"
      "  initial begin : b s_t r; s.h = new; t.h = new; r.h = new;\n"
      "    s.h.run(); t.h.run(); r.h.run();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiMethodTaskCall, By("top.b")).size(), 3U);
  ExpectTaskCallReaches("run", "top", "B");
}

TEST_F(CallStatementsInAScope, ACallOnProcessSelfIsAMethodFuncCall) {
  Run("module top; initial begin : b process::self().srandom(1); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls =
      ObjectsOf(vpiMethodFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 1U);
  vpiHandle call = kCalls.front();
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

TEST_F(CallStatementsInAScope, ACallResolvedUpwardReachesTheEnclosingTask) {
  Run("module deep; initial begin : b t(); end endmodule\n"
      "module leaf; deep k (); endmodule\n"
      "module mid; leaf l (); endmodule\n"
      "module other; endmodule\n"
      "module top; task t; endtask other s (); mid m (); endmodule\n");
  vpiHandle task = Named(vpiTaskFunc, By("top"), "t");
  ASSERT_NE(task, nullptr);
  vpiHandle call = CallOf(vpiTaskCall, By("top.m.l.k.b"), "t");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(task));
}

TEST_F(CallStatementsInAScope, ACallOnALetsHandleReachesItsMethod) {
  Run("module top;\n"
      "  class B; task run(); endtask endclass\n"
      "  B b = new;\n"
      "  let other() = 1;\n"
      "  let cur() = b;\n"
      "  initial begin : b0 cur().run(); end\n"
      "endmodule\n");
  vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b0"), "run");
  vpiHandle run = Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(run, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(run));
}

TEST_F(CallStatementsInAScope, AScopeRandomizeCallIsAFuncCall) {
  Run("module top; int a;\n"
      "  initial begin : b randomize(a); std::randomize(a); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls = ObjectsOf(vpiFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 2U);
  for (vpiHandle call : kCalls) {
    EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
    EXPECT_EQ(vpi_handle(vpiFunction, call), nullptr);
  }
}

TEST_F(CallStatementsInAScope, ALocatorCallReachesItsWithExpression) {
  Run("module top; int q[$] = '{1, 2}; int z;\n"
      "  initial begin : b\n"
      "    q.find with (item > 1); q.find_index with (item > 1);\n"
      "    q.find_first with (item > 1); q.find_first_index with (item > 1);\n"
      "    q.find_last with (item > 1); q.find_last_index with (item > 1);\n"
      "    q.min with (item + 1); q.max with (item + 1);\n"
      "    q.unique with (item + 1); q.unique_index with (item + 1);\n"
      "    q.unique(); q.sum with (item * 2);\n"
      "    void'(std::randomize(z) with { z > 0; });\n"
      "  end\n"
      "endmodule\n");
  std::vector<vpiHandle> calls;
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle stmt = vpi_scan(it)) calls.push_back(stmt);
  ASSERT_EQ(calls.size(), 13u);
  for (std::size_t i = 0; i < 10; ++i) {
    vpiHandle with = vpi_handle(vpiWith, calls[i]);
    ASSERT_NE(with, nullptr) << i;
    EXPECT_EQ(vpi_get(vpiType, with), vpiOperation) << i;
  }
  for (std::size_t i = 10; i < calls.size(); ++i) {
    EXPECT_EQ(vpi_handle(vpiWith, calls[i]), nullptr) << i;
  }
}

TEST_F(CallStatementsInAScope, ACallOfAClassBuiltInMethodIsAMethodFuncCall) {
  Run("module top;\n"
      "  class B; rand int x; endclass\n"
      "  class C extends B;\n"
      "    function void pre_randomize(); endfunction\n"
      "  endclass\n"
      "  B h = new; C k = new;\n"
      "  initial begin : b\n"
      "    void'(h.randomize()); h.pre_randomize(); h.post_randomize();\n"
      "    h.rand_mode(0); h.constraint_mode(0); h.srandom(1);\n"
      "    void'(h.get_randstate()); h.set_randstate(\"s\");\n"
      "    void'(k.randomize()); k.pre_randomize();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(MethodCallsOf(By("top.b")),
            (std::vector<std::string>{"h", "h", "h", "h", "h", "h", "h", "h",
                                      "k", "k"}));
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> calls;
  while (vpiHandle stmt = vpi_scan(it)) calls.push_back(stmt);
  ASSERT_EQ(calls.size(), 10u);
  for (std::size_t i = 0; i + 1 < calls.size(); ++i) {
    EXPECT_EQ(vpi_get(vpiUserDefn, calls[i]), 0) << i;
    EXPECT_EQ(vpi_handle(vpiFunction, calls[i]), nullptr) << i;
  }
  vpiHandle declared =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "C"), "pre_randomize");
  ASSERT_NE(declared, nullptr);
  EXPECT_EQ(vpi_get(vpiUserDefn, calls.back()), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, calls.back())),
            VpiObjectOf(declared));
}

TEST_F(CallStatementsInAScope, ACallReachesTheMethodATypeParameterBaseHas) {
  Run("module top;\n"
      "  class B; function void run(); endfunction endclass\n"
      "  class B2; task tick(); endtask endclass\n"
      "  class C #(int N = 1, type T = B) extends T; endclass\n"
      "  class H; C c = new; C #(.T(B2)) d = new; endclass\n"
      "  C c = new; C #(1, B2) e = new; H h = new;\n"
      "  initial begin : b c.run(); h.c.run(); e.tick(); h.d.tick(); end\n"
      "endmodule\n");
  vpiHandle run = Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run");
  vpiHandle tick =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "B2"), "tick");
  ASSERT_NE(run, nullptr);
  ASSERT_NE(tick, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> calls;
  while (vpiHandle stmt = vpi_scan(it)) calls.push_back(stmt);
  ASSERT_EQ(calls.size(), 4u);
  for (std::size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(vpi_get(vpiType, calls[i]), vpiMethodFuncCall) << i;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, calls[i])), VpiObjectOf(run))
        << i;
  }
  for (std::size_t i = 2; i < 4; ++i) {
    EXPECT_EQ(vpi_get(vpiType, calls[i]), vpiMethodTaskCall) << i;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, calls[i])), VpiObjectOf(tick))
        << i;
  }
}

TEST_F(CallStatementsInAScope, AnExpressionsSpecializationChoosesItsBase) {
  Run("module top;\n"
      "  class B; endclass\n"
      "  class B2; task tick(); endtask endclass\n"
      "  class C #(type T = B) extends T; endclass\n"
      "  class H; C #(.T(B2)) d = new;\n"
      "    function C #(.T(B2)) get(); return d; endfunction\n"
      "  endclass\n"
      "  C #(.T(B2)) objs [2]; H hs [2];\n"
      "  function C #(.T(B2)) make(); make = new; endfunction\n"
      "  initial begin : b objs[0] = new; hs[0] = new;\n"
      "    objs[0].tick(); make().tick(); hs[0].d.tick(); hs[0].get().tick();\n"
      "  end\n"
      "endmodule\n");
  vpiHandle tick =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "B2"), "tick");
  ASSERT_NE(tick, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> calls;
  while (vpiHandle stmt = vpi_scan(it)) {
    if (vpi_get(vpiType, stmt) != vpiAssignment) calls.push_back(stmt);
  }
  ASSERT_EQ(calls.size(), 4u);
  for (std::size_t i = 0; i < calls.size(); ++i) {
    EXPECT_EQ(vpi_get(vpiType, calls[i]), vpiMethodTaskCall) << i;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, calls[i])), VpiObjectOf(tick))
        << i;
  }
}

TEST_F(CallStatementsInAScope, AStructMembersSpecializationChoosesItsBase) {
  Run("module top;\n"
      "  class B; endclass\n"
      "  class B2; task tick(); endtask endclass\n"
      "  class C #(type T = B) extends T; endclass\n"
      "  typedef struct { C #(.T(B2)) c; } s_t;\n"
      "  s_t s;\n"
      "  initial begin : b s.c = new; s.c.tick(); end\n"
      "endmodule\n");
  vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "tick");
  vpiHandle tick =
      Named(vpiMethods, Named(vpiClassDefn, By("top"), "B2"), "tick");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(tick, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(tick));
}

TEST_F(CallStatementsInAScope, ACallOfRandomizeThroughABuiltInBaseIsACall) {
  Run("module top;\n"
      "  class M extends mailbox #(int); endclass\n"
      "  M m = new;\n"
      "  initial begin : b void'(m.randomize()); end\n"
      "endmodule\n");
  EXPECT_EQ(MethodCallsOf(By("top.b")), std::vector<std::string>{"m"});
}

TEST_F(CallStatementsInAScope, AModeCallOnAMemberIsAMethodFuncCall) {
  Run("module top;\n"
      "  class C; rand int x; constraint c { x > 0; } endclass\n"
      "  C h = new;\n"
      "  initial begin : b h.x.rand_mode(0); h.c.constraint_mode(0); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls =
      ObjectsOf(vpiMethodFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 2U);
  for (vpiHandle call : kCalls) {
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
    EXPECT_EQ(vpi_handle(vpiFunction, call), nullptr);
  }
  vpiHandle prefix = vpi_handle(vpiPrefix, kCalls.front());
  ASSERT_NE(prefix, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, prefix), "x");
}

TEST_F(CallStatementsInAScope, ARandomizeCallReachesItsInlineConstraint) {
  Run("module top;\n"
      "  class C; rand int x; endclass\n"
      "  C h = new;\n"
      "  initial begin : b\n"
      "    void'(h.randomize() with { x > 0; });\n"
      "    void'(h.randomize() with (x) { x < 9; });\n"
      "    void'(h.randomize());\n"
      "  end\n"
      "endmodule\n");
  std::vector<vpiHandle> calls;
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle stmt = vpi_scan(it)) calls.push_back(stmt);
  ASSERT_EQ(calls.size(), 3u);
  for (std::size_t i = 0; i < 2; ++i) {
    vpiHandle with = vpi_handle(vpiWith, calls[i]);
    ASSERT_NE(with, nullptr) << i;
    EXPECT_EQ(vpi_get(vpiType, with), vpiConstraint) << i;
  }
  EXPECT_EQ(vpi_handle(vpiWith, calls[2]), nullptr);
}

TEST_F(CallStatementsInAScope, AMethodCallInAnExpressionIsAMethodFuncCall) {
  Run("module top;\n"
      "  class C; function int get(); return 7; endfunction endclass\n"
      "  C h = new; int r; int q[$] = '{1, 2};\n"
      "  initial begin : b r = h.get(); r = q.size(); end\n"
      "endmodule\n");
  std::vector<vpiHandle> calls;
  vpiHandle it = vpi_iterate(vpiStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle stmt = vpi_scan(it)) {
    calls.push_back(vpi_handle(vpiRhs, stmt));
  }
  ASSERT_EQ(calls.size(), 2u);
  const char* const kNames[] = {"get", "size"};
  const char* const kPrefixes[] = {"h", "q"};
  for (std::size_t i = 0; i < calls.size(); ++i) {
    ASSERT_NE(calls[i], nullptr) << i;
    EXPECT_EQ(vpi_get(vpiType, calls[i]), vpiMethodFuncCall) << i;
    EXPECT_STREQ(vpi_get_str(vpiName, calls[i]), kNames[i]) << i;
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, calls[i])),
                 kPrefixes[i])
        << i;
  }
  vpiHandle get = Named(vpiMethods, Named(vpiClassDefn, By("top"), "C"), "get");
  ASSERT_NE(get, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, calls[0])), VpiObjectOf(get));
  EXPECT_EQ(vpi_handle(vpiFunction, calls[1]), nullptr);
  s_vpi_value value{};
  value.format = vpiIntVal;
  vpi_get_value(calls[0], &value);
  EXPECT_EQ(value.value.integer, 7);
}

}  // namespace
}  // namespace delta
