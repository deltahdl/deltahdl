#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ScopeItemsOfARun : public VpiDesignRun {
 protected:
  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && VpiObjectOf(a) == VpiObjectOf(b);
  }

  static bool ScopeIs(vpiHandle obj, vpiHandle scope) {
    return Same(vpi_handle(vpiScope, obj), scope);
  }

  static vpiHandle Proc(vpiHandle scope, std::size_t index) {
    std::vector<vpiHandle> procs = ObjectsOf(vpiProcess, scope);
    return index < procs.size() ? procs[index] : nullptr;
  }

  static vpiHandle BodyOf(vpiHandle obj) { return vpi_handle(vpiStmt, obj); }

  static vpiHandle FirstStmt(vpiHandle block) {
    std::vector<vpiHandle> stmts = ObjectsOf(vpiStmt, block);
    return stmts.empty() ? nullptr : stmts.front();
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static std::vector<int> SortedKindsOf(int type, vpiHandle ref) {
    std::vector<int> kinds = KindsOf(type, ref);
    std::sort(kinds.begin(), kinds.end());
    return kinds;
  }

  static vpiHandle InnerOfKind(vpiHandle scope, int kind) {
    for (vpiHandle inner : ObjectsOf(vpiInternalScope, scope)) {
      if (vpi_get(vpiType, inner) == kind) return inner;
    }
    return nullptr;
  }

  static std::string Str(int property, vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return text == nullptr ? "" : text;
  }

  static std::vector<vpiHandle> LoopVarsOf(vpiHandle for_stmt) {
    std::vector<vpiHandle> vars;
    for (vpiHandle init : ObjectsOf(vpiForInitStmt, for_stmt)) {
      vars.push_back(vpi_handle(vpiLhs, init));
    }
    return vars;
  }

  static vpiHandle Unit() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }

  static vpiHandle Tf(vpiHandle scope, const char* name) {
    return Named(vpiTaskFunc, scope, name);
  }
};

using Names = std::vector<std::string>;

TEST_F(ScopeItemsOfARun, EveryScopeKindIteratesTheEventsItDeclares) {
  Run("interface ifc; event ie; event ia[2]; endinterface\n"
      "program prg; event pe; event pa[2]; endprogram\n"
      "module sub; event se; endmodule\n"
      "module top; event me; event ma[2]; sub u(); ifc i0(); prg p0();\n"
      "  task t; event te; endtask\n"
      "  function void f; event fe; endfunction\n"
      "  if (1) begin : g event ge; end\n"
      "  initial begin : nb event be; end\n"
      "  initial fork : nf event ke; join\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiNamedEvent, top), Names{"me"});
  EXPECT_EQ(NamesOf(vpiNamedEventArray, top), Names{"ma"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.i0")), Names{"ie"});
  EXPECT_EQ(NamesOf(vpiNamedEventArray, By("top.i0")), Names{"ia"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.p0")), Names{"pe"});
  EXPECT_EQ(NamesOf(vpiNamedEventArray, By("top.p0")), Names{"pa"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, Tf(top, "t")), Names{"te"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, Tf(top, "f")), Names{"fe"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.g")), Names{"ge"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.nb")), Names{"be"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.nf")), Names{"ke"});
}

TEST_F(ScopeItemsOfARun, DISABLED_AModuleIteratesItsConcurrentAssertionsOnly) {
  Run("module top; logic clk, a;\n"
      "  ap: assert property (@(posedge clk) a);\n"
      "  mp: assume property (@(posedge clk) a);\n"
      "  cp: cover property (@(posedge clk) a);\n"
      "  rp: restrict property (@(posedge clk) a);\n"
      "  initial begin ia: assert (1); im: assume (1); ic: cover (1); end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiConcurrentAssertions, By("top")),
            (Names{"ap", "cp", "mp", "rp"}));
}

TEST_F(ScopeItemsOfARun,
       DISABLED_EveryScopeKindIteratesItsConcurrentAssertions) {
  Run("interface ifc(input logic clk); logic a;\n"
      "  ia: assert property (@(posedge clk) a);\n"
      "endinterface\n"
      "program prg(input logic clk); logic a;\n"
      "  pa: assert property (@(posedge clk) a);\n"
      "endprogram\n"
      "module top; logic clk, a; ifc i0(clk); prg p0(clk);\n"
      "  if (1) begin : g ga: assert property (@(posedge clk) a); end\n"
      "  always @(posedge clk) begin : blk ba: assert property (a); end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiConcurrentAssertions, By("top.g")), Names{"ga"});
  EXPECT_EQ(NamesOf(vpiConcurrentAssertions, By("top.i0")), Names{"ia"});
  EXPECT_EQ(NamesOf(vpiConcurrentAssertions, By("top.p0")), Names{"pa"});
  EXPECT_EQ(NamesOf(vpiConcurrentAssertions, By("top.blk")), Names{"ba"});
}

TEST_F(ScopeItemsOfARun, AForeachIsTheScopeOfItsLoopVariables) {
  Run("module top; int a[2]; int m[2][3][4];\n"
      "  initial foreach (a[i]) a[i] = i;\n"
      "  initial foreach (m[x, , z]) m[x][0][z] = 0;\n"
      "  task t; foreach (a[k]) a[k] = 0; endtask\n"
      "  class C; int q[3];\n"
      "    function void f; foreach (q[j]) q[j] = 0; endfunction\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle c = Named(vpiClassDefn, top, "C");
  ASSERT_NE(c, nullptr);
  struct Case {
    vpiHandle foreach_stmt;
    Names vars;
  };
  for (const Case& each :
       {Case{BodyOf(Proc(top, 0)), {"i"}},
        Case{BodyOf(Proc(top, 1)), {"x", "z"}},
        Case{BodyOf(Tf(top, "t")), {"k"}}, Case{BodyOf(Tf(c, "f")), {"j"}}}) {
    ASSERT_EQ(KindOf(each.foreach_stmt), vpiForeachStmt);
    EXPECT_EQ(NamesOf(vpiLoopVars, each.foreach_stmt), each.vars);
    for (vpiHandle var : ObjectsOf(vpiLoopVars, each.foreach_stmt)) {
      if (KindOf(var) == vpiOperation) continue;
      EXPECT_TRUE(ScopeIs(var, each.foreach_stmt)) << Str(vpiName, var);
    }
  }
  std::vector<vpiHandle> skipping =
      ObjectsOf(vpiLoopVars, BodyOf(Proc(top, 1)));
  ASSERT_EQ(skipping.size(), 3U);
  EXPECT_EQ(Str(vpiName, skipping[0]), "x");
  EXPECT_EQ(KindOf(skipping[1]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipping[1]), vpiNullOp);
  EXPECT_EQ(Str(vpiName, skipping[2]), "z");
}

TEST_F(ScopeItemsOfARun, AForOverAModuleVariableIsNoScope) {
  Run("module top; int i; initial for (i = 0; i < 2; i++); endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(KindOf(BodyOf(Proc(top, 0))), vpiFor);
  EXPECT_TRUE(ObjectsOf(vpiInternalScope, top).empty());
}

TEST_F(ScopeItemsOfARun, DISABLED_ADeclaringForIsTheScopeOfEachLoopVariable) {
  Run("module top; int y;\n"
      "  initial for (int a = 0, b = 0; a < 2; a++) y = b;\n"
      "endmodule\n");
  vpiHandle for_stmt = BodyOf(Proc(By("top"), 0));
  ASSERT_EQ(KindOf(for_stmt), vpiFor);
  std::vector<vpiHandle> vars = LoopVarsOf(for_stmt);
  ASSERT_EQ(vars.size(), 2U);
  EXPECT_EQ(Str(vpiName, vars[0]), "a");
  EXPECT_EQ(Str(vpiName, vars[1]), "b");
  for (vpiHandle var : vars) {
    EXPECT_TRUE(ScopeIs(var, for_stmt)) << Str(vpiName, var);
  }
}

TEST_F(ScopeItemsOfARun, DISABLED_ADeclaringForIteratesItsLoopVariables) {
  Run("module top; int y;\n"
      "  initial for (int a = 0, b = 0; a < 2; a++) y = b;\n"
      "endmodule\n");
  vpiHandle for_stmt = BodyOf(Proc(By("top"), 0));
  ASSERT_EQ(KindOf(for_stmt), vpiFor);
  EXPECT_EQ(NamesOf(vpiVariables, for_stmt), (Names{"a", "b"}));
}

TEST_F(ScopeItemsOfARun, ADeclaringForIsAScopeOfTheScopeAroundIt) {
  Run("module top; int y;\n"
      "  task t; for (int i = 0; i < 2; i++) y = i; endtask\n"
      "  function void f; for (int i = 0; i < 2; i++) y = i; endfunction\n"
      "  initial begin : nb for (int i = 0; i < 2; i++) y = i; end\n"
      "  class C; int n;\n"
      "    function void m; for (int i = 0; i < 2; i++) n = i; endfunction\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle c = Named(vpiClassDefn, top, "C");
  ASSERT_NE(c, nullptr);
  for (vpiHandle holder :
       {Tf(top, "t"), Tf(top, "f"), By("top.nb"), Tf(c, "m")}) {
    ASSERT_NE(holder, nullptr);
    EXPECT_EQ(SortedKindsOf(vpiInternalScope, holder),
              std::vector<int>{vpiFor});
    vpiHandle for_stmt = InnerOfKind(holder, vpiFor);
    ASSERT_NE(for_stmt, nullptr) << Str(vpiName, holder);
    EXPECT_TRUE(ScopeIs(for_stmt, holder)) << Str(vpiName, holder);
  }
}

TEST_F(ScopeItemsOfARun, AModuleIteratesAVirtualInterfaceArrayOnce) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i0(); virtual ifc v; virtual ifc va[1:2];\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, top), (Names{"v", "va"}));
  EXPECT_EQ(KindOf(Named(vpiVariables, top, "va")), vpiArrayVar);
}

TEST_F(ScopeItemsOfARun, DISABLED_EveryScopeKindIteratesEachVirtualInterface) {
  Run("interface ifc; endinterface\n"
      "program prg; virtual ifc s; virtual ifc a[2]; endprogram\n"
      "module top; ifc i0(); prg p0();\n"
      "  task t; virtual ifc s; virtual ifc a[2]; endtask\n"
      "  function void f; virtual ifc s; virtual ifc a[2]; endfunction\n"
      "  if (1) begin : g virtual ifc s; virtual ifc a[2]; end\n"
      "  initial begin : nb virtual ifc s; virtual ifc a[2]; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  for (vpiHandle scope :
       {By("top.p0"), Tf(top, "t"), Tf(top, "f"), By("top.g"), By("top.nb")}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiVirtualInterfaceVar, scope),
              (Names{"a[0]", "a[1]", "s"}))
        << Str(vpiFullName, scope);
  }
}

TEST_F(ScopeItemsOfARun, ALexicalScopeIteratesNoVirtualInterface) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i0();\n"
      "  class D; virtual ifc v; endclass\n"
      "  class C; virtual ifc v; virtual ifc vs[2]; D d; endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_iterate(vpiVirtualInterfaceVar, c), nullptr);
  vpiHandle lexical = vpi_handle(vpiTypespec, Named(vpiVariables, c, "d"));
  ASSERT_EQ(KindOf(lexical), vpiClassTypespec);
  EXPECT_EQ(vpi_iterate(vpiVirtualInterfaceVar, lexical), nullptr);
}

constexpr const char* kClassWithInterfaces =
    "interface ifc; endinterface\n"
    "module top; ifc i0();\n"
    "  class C; virtual ifc v; virtual ifc vs[2]; endclass\n"
    "  C c = new;\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, DISABLED_ASpecializationIteratesEachVirtualInterface) {
  Run(kClassWithInterfaces);
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  vpiHandle spec = vpi_handle(vpiClassTypespec, obj);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(NamesOf(vpiVirtualInterfaceVar, spec),
            (Names{"v", "vs[0]", "vs[1]"}));
}

TEST_F(ScopeItemsOfARun, AClassIteratesAVirtualInterfaceArrayOnce) {
  Run(kClassWithInterfaces);
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  for (vpiHandle scope : {vpi_handle(vpiClassTypespec, obj), obj}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiVariables, scope), (Names{"v", "vs"}));
    EXPECT_EQ(KindOf(Named(vpiVariables, scope, "vs")), vpiArrayVar);
  }
}

constexpr const char* kParametersOfEveryScope =
    "interface ifc #(parameter int P = 1, parameter type T = int);\n"
    "  localparam int L = 2;\n"
    "endinterface\n"
    "program prg #(parameter int P = 1, parameter type T = int);\n"
    "  localparam int L = 2;\n"
    "endprogram\n"
    "module top; int y; ifc i0(); prg p0();\n"
    "  initial begin : nb localparam int BL = 3; y = BL; end\n"
    "  initial fork : nf localparam int FL = 4; y = FL; join\n"
    "  task t; localparam int TL = 5; y = TL; endtask\n"
    "  function int f; localparam int FN = 6; return FN; endfunction\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, InterfacesAndProgramsIterateEveryParameterKind) {
  Run(kParametersOfEveryScope);
  EXPECT_EQ(NamesOf(vpiParameter, By("top.i0")), (Names{"L", "P", "T"}));
  EXPECT_EQ(NamesOf(vpiParameter, By("top.p0")), (Names{"L", "P", "T"}));
}

TEST_F(ScopeItemsOfARun, DISABLED_BlocksAndSubroutinesIterateTheirParameters) {
  Run(kParametersOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiParameter, By("top.nb")), Names{"BL"});
  EXPECT_EQ(NamesOf(vpiParameter, By("top.nf")), Names{"FL"});
  EXPECT_EQ(NamesOf(vpiParameter, Tf(top, "t")), Names{"TL"});
  EXPECT_EQ(NamesOf(vpiParameter, Tf(top, "f")), Names{"FN"});
}

constexpr const char* kBodies =
    "  int y;\n"
    "  task t0; endtask\n"
    "  task t1; y = 1; endtask\n"
    "  task t2; y = 1; y = 2; endtask\n"
    "  function void f0; endfunction\n"
    "  function void f1; y = 1; endfunction\n"
    "  function void f2; y = 1; y = 2; endfunction\n";

TEST_F(ScopeItemsOfARun, EveryTaskAndFunctionReachesItsBody) {
  Run(std::string("interface ifc;\n") + kBodies + "endinterface\n" +
      "program prg;\n" + kBodies + "endprogram\n" + "module top;\n" + kBodies +
      "  ifc i0(); prg p0();\nendmodule\n");
  for (vpiHandle scope : {By("top"), By("top.i0"), By("top.p0")}) {
    ASSERT_NE(scope, nullptr);
    std::string at = Str(vpiFullName, scope);
    EXPECT_EQ(BodyOf(Tf(scope, "t0")), nullptr) << at;
    EXPECT_EQ(BodyOf(Tf(scope, "f0")), nullptr) << at;
    EXPECT_EQ(KindOf(BodyOf(Tf(scope, "t1"))), vpiAssignment) << at;
    EXPECT_EQ(KindOf(BodyOf(Tf(scope, "f1"))), vpiAssignment) << at;
    for (const char* name : {"t2", "f2"}) {
      vpiHandle body = BodyOf(Tf(scope, name));
      EXPECT_EQ(KindOf(body), vpiBegin) << at << name;
      EXPECT_EQ(Str(vpiName, body), "") << at << name;
      EXPECT_EQ(KindsOf(vpiStmt, body),
                (std::vector<int>{vpiAssignment, vpiAssignment}))
          << at << name;
    }
  }
}

TEST_F(ScopeItemsOfARun, InterfacesAndProgramsIterateTheirAssertionDecls) {
  Run("interface ifc(input logic clk); logic a;\n"
      "  sequence is1; a; endsequence\n"
      "endinterface\n"
      "program prg(input logic clk); logic a;\n"
      "  property pp; @(posedge clk) a; endproperty\n"
      "  sequence ps; a; endsequence\n"
      "endprogram\n"
      "module top; logic clk; ifc i0(clk); prg p0(clk); endmodule\n");
  EXPECT_EQ(NamesOf(vpiSequenceDecl, By("top.i0")), Names{"is1"});
  EXPECT_EQ(NamesOf(vpiPropertyDecl, By("top.p0")), Names{"pp"});
  EXPECT_EQ(NamesOf(vpiSequenceDecl, By("top.p0")), Names{"ps"});
}

constexpr const char* kLetsOfEveryScope =
    "interface ifc; let il(x) = x; endinterface\n"
    "program prg; let pl(x) = x; endprogram\n"
    "module top; logic clk; int y; ifc i0(); prg p0();\n"
    "  let ml(x) = x;\n"
    "  initial begin : nb let bl(x) = x; y = bl(1); end\n"
    "  initial begin let ul(x) = x; y = ul(1); end\n"
    "  task t; let tl(x) = x; y = tl(1); endtask\n"
    "  function void f; let fl(x) = x; y = fl(1); endfunction\n"
    "  clocking cb @(posedge clk); let cl(x) = x; endclocking\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, InstancesIterateOnlyTheirOwnLetDecls) {
  Run(kLetsOfEveryScope);
  EXPECT_EQ(NamesOf(vpiLetDecl, By("top")), Names{"ml"});
  EXPECT_EQ(NamesOf(vpiLetDecl, By("top.i0")), Names{"il"});
  EXPECT_EQ(NamesOf(vpiLetDecl, By("top.p0")), Names{"pl"});
}

TEST_F(ScopeItemsOfARun, DISABLED_InnerScopesIterateTheirLetDecls) {
  Run(kLetsOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiLetDecl, By("top.nb")), Names{"bl"});
  EXPECT_EQ(NamesOf(vpiLetDecl, InnerOfKind(top, vpiBegin)), Names{"ul"});
  EXPECT_EQ(NamesOf(vpiLetDecl, Tf(top, "t")), Names{"tl"});
  EXPECT_EQ(NamesOf(vpiLetDecl, Tf(top, "f")), Names{"fl"});
  EXPECT_EQ(NamesOf(vpiLetDecl, Named(vpiClockingBlock, top, "cb")),
            Names{"cl"});
}

constexpr const char* kSourcePackage =
    "package src; int v; logic clk;\n"
    "  function int fn(); return 1; endfunction\n"
    "  task tk; endtask\n"
    "  parameter int P = 3;\n"
    "  typedef int t_t;\n"
    "  property sp; @(posedge clk) v == v; endproperty\n"
    "endpackage\n";

constexpr const char* kImportsOfEveryScope =
    "import src::*; int uv = v;\n"
    "package user; import src::*; int u = v; endpackage\n"
    "interface ifc; import src::*; int w = v; endinterface\n"
    "program prg; import src::*; int w = v; endprogram\n"
    "module top; int y; ifc i0(); prg p0();\n"
    "  function int f; import src::*; return v; endfunction\n"
    "  task t; import src::*; y = v; endtask\n"
    "  initial begin : nb import src::*; y = v; end\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, InterfacesAndProgramsIterateWhatTheyImport) {
  Run(std::string(kSourcePackage) + kImportsOfEveryScope);
  EXPECT_EQ(NamesOf(vpiImport, By("top.i0")), Names{"v"});
  EXPECT_EQ(NamesOf(vpiImport, By("top.p0")), Names{"v"});
}

TEST_F(ScopeItemsOfARun, DISABLED_PackagesAndTheUnitIterateWhatTheyImport) {
  Run(std::string(kSourcePackage) + kImportsOfEveryScope);
  for (vpiHandle scope : {Unit(), By("user")}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiImport, scope), Names{"v"}) << Str(vpiName, scope);
  }
}

TEST_F(ScopeItemsOfARun, DISABLED_AnInnerScopeIteratesWhatItImports) {
  Run(std::string(kSourcePackage) + kImportsOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  for (vpiHandle scope : {Tf(top, "f"), Tf(top, "t"), By("top.nb")}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiImport, scope), Names{"v"}) << Str(vpiName, scope);
  }
  EXPECT_EQ(vpi_iterate(vpiImport, top), nullptr);
}

TEST_F(ScopeItemsOfARun, DISABLED_EveryKindOfImportedObjectIsIterated) {
  Run(std::string(kSourcePackage) +
      "module top; import src::*; t_t x = P;\n"
      "  initial begin tk; x = fn(); end\n"
      "  a1: assert property (sp);\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiImport, By("top")),
            (Names{"P", "fn", "sp", "t_t", "tk"}));
}

TEST_F(ScopeItemsOfARun, AScopeReferencingNothingImportedIteratesNoImport) {
  Run(std::string(kSourcePackage) +
      "module bare; int z; endmodule\n"
      "module top; import src::*; int z; bare b(); endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiImport, By("top")), nullptr);
  EXPECT_EQ(vpi_iterate(vpiImport, By("top.b")), nullptr);
}

TEST_F(ScopeItemsOfARun, ABlockIteratesItsStatementsInOrderOnly) {
  Run("module top; event e;\n"
      "  initial begin : nb int v; v = 1; #1; @e; end\n"
      "  initial fork : nf int v; v = 1; #1; @e; join\n"
      "  initial begin int v; v = 1; #1; @e; end\n"
      "endmodule\n");
  std::vector<int> order{vpiAssignment, vpiDelayControl, vpiEventControl};
  EXPECT_EQ(KindsOf(vpiStmt, By("top.nb")), order);
  EXPECT_EQ(KindsOf(vpiStmt, By("top.nf")), order);
  vpiHandle unnamed = BodyOf(Proc(By("top"), 2));
  ASSERT_EQ(KindOf(unnamed), vpiBegin);
  EXPECT_EQ(KindsOf(vpiStmt, unnamed), order);
}

TEST_F(ScopeItemsOfARun, AStatementReachesTheNearestScopeAroundIt) {
  Run("interface ifc; int y; initial y = 1; endinterface\n"
      "program prg; int y; initial y = 1; endprogram\n"
      "module top; int y; int a[2]; ifc i0(); prg p0();\n"
      "  initial begin int v; v = 1; end\n"
      "  initial fork : nf y = 1; join\n"
      "  task t; y = 1; endtask\n"
      "  function void f; y = 1; endfunction\n"
      "  initial for (int i = 0; i < 2; i++) y = i;\n"
      "  initial foreach (a[i]) y = i;\n"
      "  if (1) begin : g initial y = 1; end\n"
      "  class C; int n; function void m; n = 1; endfunction endclass\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle unnamed = BodyOf(Proc(top, 0));
  EXPECT_TRUE(ScopeIs(FirstStmt(unnamed), unnamed));
  EXPECT_TRUE(ScopeIs(FirstStmt(By("top.nf")), By("top.nf")));
  EXPECT_TRUE(ScopeIs(BodyOf(Tf(top, "t")), Tf(top, "t")));
  EXPECT_TRUE(ScopeIs(BodyOf(Tf(top, "f")), Tf(top, "f")));
  vpiHandle for_stmt = BodyOf(Proc(top, 2));
  EXPECT_TRUE(ScopeIs(BodyOf(for_stmt), for_stmt));
  vpiHandle foreach_stmt = BodyOf(Proc(top, 3));
  EXPECT_TRUE(ScopeIs(BodyOf(foreach_stmt), foreach_stmt));
  EXPECT_TRUE(ScopeIs(BodyOf(Proc(By("top.g"), 0)), By("top.g")));
  vpiHandle m = Tf(Named(vpiClassDefn, top, "C"), "m");
  EXPECT_TRUE(ScopeIs(BodyOf(m), m));
  EXPECT_TRUE(ScopeIs(BodyOf(Proc(By("top.i0"), 0)), By("top.i0")));
  EXPECT_TRUE(ScopeIs(BodyOf(Proc(By("top.p0"), 0)), By("top.p0")));
}

TEST_F(ScopeItemsOfARun, AnUnnamedForkThatDeclaresNothingIsNoScope) {
  Run("module top; int y; initial fork y = 1; join endmodule\n");
  EXPECT_TRUE(ObjectsOf(vpiInternalScope, By("top")).empty());
}

TEST_F(ScopeItemsOfARun, DISABLED_AnUnnamedBlockDeclaringAnyItemIsAScope) {
  Run("module m0; int y; initial begin typedef int t_t; y = 1; end endmodule\n"
      "module m1; int y; initial begin localparam int L = 1; y = L; end\n"
      "endmodule\n"
      "module m2; int y; initial begin parameter int P = 1; y = P; end\n"
      "endmodule\n"
      "module m3; int y; initial begin let l(x) = x; y = l(1); end\n"
      "endmodule\n"
      "module m4; int y; initial begin event e; y = 1; end endmodule\n"
      "module top; m0 u0(); m1 u1(); m2 u2(); m3 u3(); m4 u4(); endmodule\n");
  for (const char* inst : {"top.u0", "top.u1", "top.u2", "top.u3", "top.u4"}) {
    vpiHandle scope = By(inst);
    ASSERT_NE(scope, nullptr) << inst;
    EXPECT_EQ(SortedKindsOf(vpiInternalScope, scope),
              std::vector<int>{vpiBegin})
        << inst;
  }
}

TEST_F(ScopeItemsOfARun, AnUnnamedDeclaringBlockIsAScopeWhereverItStands) {
  Run("interface ifc; int y; initial begin int v; y = v; end endinterface\n"
      "program prg; int y; initial begin int v; y = v; end endprogram\n"
      "module top; int y; ifc i0(); prg p0();\n"
      "  task t; begin int v; y = v; end endtask\n"
      "  function void f; begin int v; y = v; end endfunction\n"
      "  initial begin : nb begin int v; y = v; end end\n"
      "  class C; int n; function void m; begin int v; n = v; end\n"
      "  endfunction endclass\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  for (vpiHandle holder :
       {Tf(top, "t"), Tf(top, "f"), By("top.nb"),
        Tf(Named(vpiClassDefn, top, "C"), "m"), By("top.i0"), By("top.p0")}) {
    ASSERT_NE(holder, nullptr);
    EXPECT_EQ(SortedKindsOf(vpiInternalScope, holder),
              std::vector<int>{vpiBegin})
        << Str(vpiFullName, holder);
  }
}

constexpr const char* kVarsOfEveryScope =
    "package pk; logic l; logic arr[2]; int i; endpackage\n"
    "module top; logic [3:0] lv; int i; real r; string s; logic m [2];\n"
    "  task t; logic l; logic arr[2]; int i; endtask\n"
    "  function void f; logic l; logic arr[2]; int i; endfunction\n"
    "  if (1) begin : g logic l; logic arr[2]; int i; end\n"
    "  initial begin : nb logic l; logic arr[2]; int i; end\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, EveryScopeKindIteratesItsArrayVars) {
  Run(kVarsOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiMemory, top), Names{"m"});
  for (vpiHandle scope :
       {Tf(top, "t"), Tf(top, "f"), By("top.g"), By("top.nb"), By("pk")}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiRegArray, scope), Names{"arr"}) << Str(vpiName, scope);
    EXPECT_EQ(NamesOf(vpiMemory, scope), Names{"arr"}) << Str(vpiName, scope);
  }
}

TEST_F(ScopeItemsOfARun, SubroutinesAndBlocksIterateOnlyTheirLogicVars) {
  Run(kVarsOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  for (vpiHandle scope : {Tf(top, "t"), Tf(top, "f"), By("top.nb")}) {
    ASSERT_NE(scope, nullptr);
    EXPECT_EQ(NamesOf(vpiReg, scope), Names{"l"}) << Str(vpiName, scope);
  }
}

TEST_F(ScopeItemsOfARun, DISABLED_EveryScopeKindIteratesOnlyItsLogicVars) {
  Run(kVarsOfEveryScope);
  EXPECT_EQ(NamesOf(vpiReg, By("top")), Names{"lv"});
  for (const char* name : {"top.g", "pk"}) {
    EXPECT_EQ(NamesOf(vpiReg, By(name)), Names{"l"}) << name;
  }
}

TEST_F(ScopeItemsOfARun, EveryForkReportsTheKeywordClosingIt) {
  Run("module top; int y;\n"
      "  initial begin fork y = 1; join fork y = 2; join_none end\n"
      "  task t; fork : nf y = 1; join_any fork y = 2; join endtask\n"
      "  function void f; fork y = 3; join_none fork : ff y = 4; join_none\n"
      "  endfunction\n"
      "  class C; int n; task m; fork : cf n = 1; join_none fork n = 2; join\n"
      "  endtask endclass\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  std::vector<vpiHandle> in_initial = ObjectsOf(vpiStmt, BodyOf(Proc(top, 0)));
  ASSERT_EQ(in_initial.size(), 2U);
  EXPECT_EQ(vpi_get(vpiJoinType, in_initial[0]), vpiJoin);
  EXPECT_EQ(vpi_get(vpiJoinType, in_initial[1]), vpiJoinNone);
  std::vector<vpiHandle> in_task = ObjectsOf(vpiStmt, BodyOf(Tf(top, "t")));
  ASSERT_EQ(in_task.size(), 2U);
  EXPECT_EQ(vpi_get(vpiJoinType, in_task[0]), vpiJoinAny);
  EXPECT_EQ(vpi_get(vpiJoinType, in_task[1]), vpiJoin);
  for (vpiHandle fork : ObjectsOf(vpiStmt, BodyOf(Tf(top, "f")))) {
    EXPECT_EQ(vpi_get(vpiJoinType, fork), vpiJoinNone);
  }
  EXPECT_EQ(ObjectsOf(vpiStmt, BodyOf(Tf(top, "f"))).size(), 2U);
  vpiHandle m = Tf(Named(vpiClassDefn, top, "C"), "m");
  std::vector<vpiHandle> in_method = ObjectsOf(vpiStmt, BodyOf(m));
  ASSERT_EQ(in_method.size(), 2U);
  EXPECT_EQ(vpi_get(vpiJoinType, in_method[0]), vpiJoinNone);
  EXPECT_EQ(vpi_get(vpiJoinType, in_method[1]), vpiJoin);
}

TEST_F(ScopeItemsOfARun, ModuleScopesHaveTheirNamesAndFullNames) {
  Run("module top; logic clk;\n"
      "  task t; endtask\n"
      "  function void f; endfunction\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  for (genvar k = 0; k < 2; k++) begin : g end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(Str(vpiName, Tf(top, "t")), "t");
  EXPECT_EQ(Str(vpiFullName, Tf(top, "t")), "top.t");
  EXPECT_EQ(Str(vpiName, Tf(top, "f")), "f");
  EXPECT_EQ(Str(vpiFullName, Tf(top, "f")), "top.f");
  vpiHandle cb = Named(vpiClockingBlock, top, "cb");
  EXPECT_EQ(Str(vpiName, cb), "cb");
  EXPECT_EQ(Str(vpiFullName, cb), "top.cb");
  EXPECT_EQ(Str(vpiName, By("top.g[1]")), "g[1]");
  EXPECT_EQ(Str(vpiFullName, By("top.g[1]")), "top.g[1]");
}

TEST_F(ScopeItemsOfARun, InterfaceAndProgramClockingBlocksHaveTheirNames) {
  Run("interface bus(input logic clk); clocking cb @(posedge clk);\n"
      "  endclocking endinterface\n"
      "program prg(input logic clk); clocking cb @(posedge clk);\n"
      "  endclocking endprogram\n"
      "module top; logic clk; bus b(clk); prg p(clk); endmodule\n");
  vpiHandle in_bus = Named(vpiClockingBlock, By("top.b"), "cb");
  EXPECT_EQ(Str(vpiName, in_bus), "cb");
  EXPECT_EQ(Str(vpiFullName, in_bus), "top.b.cb");
  vpiHandle in_prg = Named(vpiClockingBlock, By("top.p"), "cb");
  EXPECT_EQ(Str(vpiName, in_prg), "cb");
  EXPECT_EQ(Str(vpiFullName, in_prg), "top.p.cb");
}

TEST_F(ScopeItemsOfARun, AModuleReachesEveryKindOfScopeItHolds) {
  Run("module top; logic clk; int a[2]; int v;\n"
      "  task t; endtask\n"
      "  function void f; endfunction\n"
      "  if (1) begin : g end\n"
      "  class C; endclass\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  initial fork : nf join\n"
      "  initial foreach (a[i]) a[i] = 0;\n"
      "endmodule\n");
  std::vector<int> expected{vpiTask,         vpiFunction,  vpiGenScope,
                            vpiClassDefn,    vpiNamedFork, vpiForeachStmt,
                            vpiClockingBlock};
  std::sort(expected.begin(), expected.end());
  EXPECT_EQ(SortedKindsOf(vpiInternalScope, By("top")), expected);
}

constexpr const char* kHeldScopes =
    "package pk; task pt; endtask endpackage\n"
    "interface ifc; task it; endtask endinterface\n"
    "program prg; task qt; endtask endprogram\n"
    "module top; ifc i0(); prg p0();\n"
    "  task t; begin : tb end endtask\n"
    "  function void f; begin : fb end endfunction\n"
    "  class C; task m; endtask endclass\n"
    "  C c = new;\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, EveryScopeKindReachesTheScopesItHolds) {
  Run(kHeldScopes);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiInternalScope, By("pk")), Names{"pt"});
  EXPECT_EQ(NamesOf(vpiInternalScope, By("top.i0")), Names{"it"});
  EXPECT_EQ(NamesOf(vpiInternalScope, By("top.p0")), Names{"qt"});
  EXPECT_EQ(NamesOf(vpiInternalScope, Tf(top, "t")), Names{"tb"});
  EXPECT_EQ(NamesOf(vpiInternalScope, Tf(top, "f")), Names{"fb"});
}

TEST_F(ScopeItemsOfARun, DISABLED_AClassObjReachesOnlyTheScopesItHolds) {
  Run(kHeldScopes);
  EXPECT_EQ(NamesOf(vpiInternalScope, vpi_handle(vpiClassObj, By("top.c"))),
            Names{"m"});
}

constexpr const char* kTypedefsOfEveryScope =
    "interface ifc; typedef int it_t; endinterface\n"
    "program prg; typedef int pt_t; endprogram\n"
    "module top; int y; ifc i0(); prg p0();\n"
    "  initial begin : nb typedef int b_t; b_t x; y = x; end\n"
    "  initial begin typedef int u_t; u_t x; y = x; end\n"
    "  task t; typedef int t_t; t_t x; y = x; endtask\n"
    "  function void f; typedef int f_t; f_t x; y = x; endfunction\n"
    "endmodule\n";

TEST_F(ScopeItemsOfARun, InterfacesAndProgramsIterateTheirTypedefs) {
  Run(kTypedefsOfEveryScope);
  EXPECT_TRUE(NamesOf(vpiTypedef, By("top")).empty());
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.i0")), Names{"it_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.p0")), Names{"pt_t"});
}

TEST_F(ScopeItemsOfARun, DISABLED_BlocksAndSubroutinesIterateTheirTypedefs) {
  Run(kTypedefsOfEveryScope);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.nb")), Names{"b_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, InnerOfKind(top, vpiBegin)), Names{"u_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, Tf(top, "t")), Names{"t_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, Tf(top, "f")), Names{"f_t"});
}

TEST_F(ScopeItemsOfARun, DISABLED_APropertyDeclReachesTheScopeDeclaringIt) {
  Run("package pk; property kp; 1; endproperty endpackage\n"
      "interface ifc; property ip; 1; endproperty endinterface\n"
      "module top; logic clk; ifc i0();\n"
      "  property mp; 1; endproperty\n"
      "  if (1) begin : g property gp; 1; endproperty end\n"
      "  clocking cb @(posedge clk); property cp; 1; endproperty endclocking\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle cb = Named(vpiClockingBlock, top, "cb");
  struct Case {
    vpiHandle scope;
    const char* name;
  };
  for (const Case& each :
       {Case{top, "mp"}, Case{By("top.g"), "gp"}, Case{cb, "cp"},
        Case{By("top.i0"), "ip"}, Case{By("pk"), "kp"}}) {
    vpiHandle decl = Named(vpiPropertyDecl, each.scope, each.name);
    ASSERT_NE(decl, nullptr) << each.name;
    EXPECT_TRUE(ScopeIs(decl, each.scope)) << each.name;
  }
}

}  // namespace
}  // namespace delta
