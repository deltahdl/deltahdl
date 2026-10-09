#include <gtest/gtest.h>

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

// §23.9 with §37.42: the module's own lookup passes over a function only a
// generate block declares. A call no block encloses still resolves to that
// declaration, which names the kind of call, but reaches no object.
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

// The method func calls a scope's statements make, each as its method's name
// and the name of the variable it is applied to, in the order written.
class CallStatementsInAScope : public VpiDesignRun {
 protected:
  static std::vector<std::pair<std::string, std::string>> MethodCallsOf(
      vpiHandle scope) {
    std::vector<std::pair<std::string, std::string>> calls;
    vpiHandle it = vpi_iterate(vpiStmt, scope);
    if (it == nullptr) return calls;
    while (vpiHandle stmt = vpi_scan(it)) {
      if (vpi_get(vpiType, stmt) != vpiMethodFuncCall) continue;
      // vpi_get_str answers in one buffer the next call overwrites, so the
      // method's name is copied before the prefix's is read.
      std::string method = vpi_get_str(vpiName, stmt);
      calls.emplace_back(method,
                         vpi_get_str(vpiName, vpi_handle(vpiPrefix, stmt)));
    }
    return calls;
  }

  // That the method task call `method` the block top.b holds reaches the
  // method of that name of the class defn `cls` that `scope` holds.
  static void ExpectTaskCallReaches(const char* method, const char* scope,
                                    const char* cls) {
    vpiHandle call = Named(vpiMethodTaskCall, By("top.b"), method);
    vpiHandle declared =
        Named(vpiMethods, Named(vpiClassDefn, By(scope), cls), method);
    ASSERT_NE(call, nullptr) << method;
    ASSERT_NE(declared, nullptr) << method;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(declared))
        << method;
  }
};

// A block's queue (§7.10.2), its associative arrays indexed by a keyword, a
// typedef name and a class (§7.8), its fixed-size array sized by a parameter
// (§7.12.2), its string (§6.16) and its enum (§6.19.5) each take the built-in
// methods of their kind, so a call of one as a statement is a method func call
// applied to the block's variable. The kind each variable is read as decides
// whether the method is one of its own: an associative array has no sort and a
// fixed-size array no delete.
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
  EXPECT_EQ(
      MethodCallsOf(By("top.b")),
      (std::vector<std::pair<std::string, std::string>>{{"push_back", "q"},
                                                        {"delete", "s"},
                                                        {"delete", "t"},
                                                        {"delete", "c"},
                                                        {"sort", "p"},
                                                        {"putc", "str"},
                                                        {"next", "e"}}));
}

// A module's dynamic array (§7.5), its fixed-size array (§7.12.2) and its enum
// declared without a typedef (§6.19) take the built-in methods of their kind
// as a block's do.
TEST_F(CallStatementsInAScope, AModulesArraysAndAnonymousEnumTakeTheirMethods) {
  Run("module top; int d[]; int f[2]; enum {X, Y} e;\n"
      "  initial begin : b d.delete(); f.sort(); e.next(); end\n"
      "endmodule\n");
  EXPECT_EQ(MethodCallsOf(By("top.b")),
            (std::vector<std::pair<std::string, std::string>>{
                {"delete", "d"}, {"sort", "f"}, {"next", "e"}}));
}

// §8.4 with §37.42 detail 2: a call through a member chain, h.b.run(), finds
// the chain's member among the class's members wherever the class declares
// it, past a method and another property declared ahead of it, and is a
// method task call of the class the member holds a handle of.
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

// §13.4.1 with §37.42: a function call written in a void cast is a func call
// statement reaching the function it calls, with the arguments it was written
// with, the cast discarding the value and adding nothing to the model (#5782).
TEST_F(CallStatementsInAScope, AVoidCastCallIsTheFuncCallItWraps) {
  Run("module top; function int f(int a); return a; endfunction\n"
      "  initial begin : b void'(f(3)); end\n"
      "endmodule\n");
  vpiHandle call = Named(vpiFuncCall, By("top.b"), "f");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, call)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "f")));
  EXPECT_EQ(KindsOf(vpiArgument, call), std::vector<int>{vpiConstant});
}

// §8.10 with §8.23 and §37.42: a static method called through its class's
// scope, C::f(), or through a package's class, p::D::g(), is a method func
// call applied to no object, reaching the method of the class defn made where
// the class is declared (#5775).
TEST_F(CallStatementsInAScope, AStaticMethodCalledThroughItsScopeIsACall) {
  Run("package q; endpackage\n"
      "package p; localparam int K = 1;\n"
      "  class D; static function void g(); endfunction endclass\n"
      "endpackage\n"
      "module top;\n"
      "  class C; static function void f(); endfunction endclass\n"
      "  initial begin : b C::f(); p::D::g(); end\n"
      "endmodule\n");
  vpiHandle f = Named(vpiMethodFuncCall, By("top.b"), "f");
  vpiHandle g = Named(vpiMethodFuncCall, By("top.b"), "g");
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

// §6.18 with §37.42: a handle whose class a typedef names is a handle of that
// class, so a call applied to it, or through a property of its class, is a
// method task call reaching the class's method (#5778).
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

// §26.3 with §37.42: a handle of a class a package declares, imported by name
// or with a wildcard, is a handle of that class, so a call applied to it is a
// method task call reaching the method of the package's class defn (#5786).
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

// §23.6 with §37.42 detail 2: a method called through a class var of an
// instance below, u.h.run(), is a method task call applied to that instance's
// variable, reaching the method of the class defn the instance holds (#5776).
TEST_F(CallStatementsInAScope, AChainThroughAnInstanceReachesItsVariable) {
  Run("module sub; class B; task run(); endtask endclass B h = new;\n"
      "endmodule\n"
      "module top; sub u (); initial begin : b u.h.run(); end endmodule\n");
  ExpectTaskCallReaches("run", "top.u", "B");
  vpiHandle call = Named(vpiMethodTaskCall, By("top.b"), "run");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(By("top.u.h"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, call)),
            VpiObjectOf(By("top.u.h")));
}

// §37.42 detail 2: a method called through an expression's value, an
// element of an array of handles, a property of an element, a function's
// result or a package's variable, is a method task call reaching its class's
// method (#5777), applied to an object it reaches through vpiPrefix (#5792).
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
  // Whether each call, in the order written, reaches a prefix.
  EXPECT_EQ(prefixed, (std::vector<bool>{true, true, true, true}));
  EXPECT_EQ(reached,
            (std::vector<VpiObject*>{VpiObjectOf(b_run), VpiObjectOf(b_run),
                                     VpiObjectOf(b_run), VpiObjectOf(d_go)}));
}

// §25.9 with §37.42: a call of an interface's task through a virtual
// interface, a module's, a block's or a class property's, is a task call named
// after the task (#5784), and one of its function a func call. The
// interface's declaration says which, so a call through a virtual interface
// of an interface nothing instantiates is a task call too (#5791).
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
  EXPECT_EQ(NamesOf(vpiTaskCall, By("top.b")),
            (std::vector<std::string>{"t", "t", "t"}));
  EXPECT_EQ(NamesOf(vpiFuncCall, By("top.b")), std::vector<std::string>{"f"});
  EXPECT_EQ(NamesOf(vpiTaskCall, By("top.b.g")), std::vector<std::string>{"t"});
}

// §35.5 with §37.42: a call of a function imported through DPI is a func call
// named after it, and a call of an imported task a task call, though no task
// or function object stands for either (#5785). The calls never run, so the
// run calls no foreign code.
TEST_F(CallStatementsInAScope, ACallOfADpiImportIsACall) {
  Run("module top;\n"
      "  import \"DPI-C\" function int c_f(int a);\n"
      "  import \"DPI-C\" task c_t();\n"
      "  initial if (0) begin : b void'(c_f(1)); c_t(); end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiFuncCall, By("top.b")), std::vector<std::string>{"c_f"});
  EXPECT_EQ(NamesOf(vpiTaskCall, By("top.b")), std::vector<std::string>{"c_t"});
}

// §8.6, §8.10 and §11.4.11 with §37.42: a method called on the handle a
// method call returns, a.self().run(), a static method's, B::make().run(), a
// package's function's, p::make_d().go(), or the one a conditional yields,
// (s ? a : c).run(), is a method task call of the class that handle's type
// names (#5789).
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
  EXPECT_EQ(NamesOf(vpiMethodTaskCall, By("top.b")),
            (std::vector<std::string>{"go", "run", "run", "run"}));
  ExpectTaskCallReaches("run", "top", "B");
  ExpectTaskCallReaches("go", "p", "D");
}

// §7.2 with §37.42 detail 2: a method called through a structure's member
// that holds a class handle, the structure declared through a typedef or
// written out, of the module or of a block, is a method task call of the
// member's class (#5788).
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
  EXPECT_EQ(NamesOf(vpiMethodTaskCall, By("top.b")),
            (std::vector<std::string>{"run", "run", "run"}));
  ExpectTaskCallReaches("run", "top", "B");
}

// §9.7 with §37.42: a method of process called on the handle process::self()
// returns is a method func call of the built-in class, not user-defined
// (#5797).
TEST_F(CallStatementsInAScope, ACallOnProcessSelfIsAMethodFuncCall) {
  Run("module top; initial begin : b process::self().srandom(1); end\n"
      "endmodule\n");
  vpiHandle call = Named(vpiMethodFuncCall, By("top.b"), "srandom");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

}  // namespace
}  // namespace delta
